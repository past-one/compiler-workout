(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t with show

    let to_int = function
    | Int n -> n
    | _ -> failwith "int value expected"

    let to_string = function
    | String s -> s
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x =
      let rec update_array' = function
      | hd::tl, 0 -> x :: tl
      | hd::tl, n -> hd :: update_array' (tl, n - 1)
      | [], _     -> failwith "Invalid array to update"
      in
      update_array' (a, i)

  end

let get = function
| Some v -> v
| None   -> failwith "Trying to get None value"

let value (_, _, _, r) = get r

let int_value conf = Value.to_int @@ value conf

(* States *)
module State =
  struct
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope
         then L (scope, bind x v s, enclosing)
         else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st   -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e

  end

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args =
      let result v = (st, i, o, Some v) in
      function
      | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
      | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
      | ".elem"    -> let b, j = match args with [b; j] -> b, j | _ -> failwith "Unreachable" in
                      let i = Value.to_int j in
                      result (match b with
                              | Value.String s -> Value.of_int @@ Char.code s.[i]
                              | Value.Array  a -> List.nth a i
                              | _              -> failwith "Invalid value parameter for elem"
                              )
      | ".length"  ->
        result @@ Value.of_int (match List.hd args with
                                | Value.Array a -> List.length a
                                | Value.String s -> String.length s
                                | _ -> failwith "Invalid parameter for length"
      )
      | ".array"   -> result @@ Value.of_array args
      | "isArray"  -> result @@ Value.of_int (match List.hd args with Value.Array  _ -> 1 | _ -> 0)
      | "isString" -> result @@ Value.of_int (match List.hd args with Value.String _ -> 1 | _ -> 0)
      | _          -> failwith "Unknown builtin"

  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t
    (* function call      *) | Call   of string * t list
                                with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
    let binop =
      let toInt f x y = if f x y then 1 else 0 in
      function
      | "+"  -> ( + )
      | "-"  -> ( - )
      | "*"  -> ( * )
      | "/"  -> ( / )
      | "%"  -> ( mod )
      | "<"  -> toInt ( <  )
      | "<=" -> toInt ( <= )
      | ">"  -> toInt ( >  )
      | ">=" -> toInt ( >= )
      | "==" -> toInt ( =  )
      | "!=" -> toInt ( <> )
      | "&&" -> toInt (fun x y -> (x <> 0) && (y <> 0))
      | "!!" -> toInt (fun x y -> (x <> 0) || (y <> 0))
      | op   -> failwith (Printf.sprintf "Undefined binop %s" op)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option

    (* Expression evaluator

          val eval : env -> config -> t -> config

       Takes an environment, a configuration and an expresion, and returns another configuration. The
       environment supplies the following method

           method call : string -> int list -> config -> config

       which takes a name of the function, a list of actual parameters and a configuration,
       an returns the resulting configuration

    *)
    let rec eval env ((s, _, _, _) as conf) =
      let (>>>) c e = eval env c e in
      let result (s, i, o, _) r = (s, i, o, Some r) in
      function
      | Const z          -> result conf @@ Value.of_int z
      | Array exprs      ->
        let args, conf' = eval_list env exprs conf in
        env#call ".array" args conf'
      | String s         -> result conf @@ Value.of_string s
      | Var name         -> result conf @@ State.eval s name
      | Binop (op, x, y) ->
        let c  = conf >>> x in
        let c' = c    >>> y in
        let first  = int_value c  in
        let second = int_value c' in
        result c' @@ Value.of_int @@ binop op first second
      | Elem (v, k)      ->
        let args, conf' = eval_list env [v; k] conf in
        env#call ".elem" args conf'
      | Length a         ->
        let conf' = conf >>> a in
        env#call ".length" [value conf'] conf
      | Call (f, exprs)  ->
        let args, conf' = eval_list env exprs conf in
        env#call f args conf'
    and eval_list env exprs conf =
      let folding (tl, c) e = let c' = eval env c e in (value c' :: tl), c' in
      let rev_args, conf' = List.fold_left folding ([], conf) exprs in
      List.rev rev_args, conf'

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as an int

    *)

    let ostapBinops ops =
      let ostapBinop op = (ostap ($(op)), fun x y -> Binop (op, x, y)) in
      List.map ostapBinop ops

    ostap (
      parse:
        !(Ostap.Util.expr
         (fun x -> x)
         [|
           `Lefta, ostapBinops ["!!"];
           `Lefta, ostapBinops ["&&"];
           `Nona,  ostapBinops ["<="; ">="; "<"; ">"; "=="; "!="];
           `Lefta, ostapBinops ["+"; "-"];
           `Lefta, ostapBinops ["*"; "/"; "%"]
         |]
         all
        );

      call: f:IDENT "(" args:!(Util.list0 parse) ")" { Call (f, args) } ;

      all:
          v:almost "." %"length" { Length v }
        | almost ;

      almost:
          value:primary keys:(-"[" parse -"]")*
          { List.fold_left (fun v k -> Elem (v, k)) value keys }
        | primary ;

      primary:
          call
        | x:IDENT   { Var x }
        | d:DECIMAL { Const d }
        | c:CHAR    { Const (Char.code c) }
        | s:STRING  { String (String.sub s 1 @@ String.length s - 2) }
        | "[" a:!(Util.list parse) "]" { Array a }
        | -"(" parse -")"
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)
        ostap (
          parse: empty {failwith "Not implemented"}
        )

        let vars p =
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p

      end

    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list
    (* leave a scope                    *) | Leave
                                              with show

    (* Statement evaluator

         val eval : env -> config -> t -> t -> config

       Takes an environment, a configuration, a continuation and a statement, and returns another configuration. The
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
           | _                           -> failwith "Invalid parameter for update"
          )
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st
      (* State.update x (update (State.eval st x) v is) st *)

    let rec eval env conf k =
      let (<.>) a b = match a, b with
      | s, Skip -> s
      | s1, s2  -> Seq (s1, s2)
      in
      let (>>) c = function Skip -> c | stmt -> eval env c Skip stmt in
      let (>>>) c e = Expr.eval env conf e in
      function
      | Skip                  -> conf >> k
      | Assign (var, keys, e) ->
        let args, c = Expr.eval_list env keys conf in
        let (s', i', o', _) as c' = c >>> e in
        (update s' var (value c') args, i', o', None) >> k
      | Seq (a, b)            -> eval env conf (b <.> k) a
      | If (e, a, b)          ->
        let c' = conf >>> e in
        eval env c' k (if int_value c' <> 0 then a else b)
      | While (e, body)       ->
        let c' = conf >>> e in
        c' >> (if int_value c' <> 0 then Seq (body, While (e, body)) <.> k else k)
      | Repeat (body, e)      ->
        conf >> body >> (If (e, Skip, Repeat (body, e)) <.> k)
      | Return None           -> conf
      | Return Some e         -> conf >>> e
      | Call (f, exprs)       -> conf >>> Expr.Call (f, exprs) >> k

    (* Statement parser *)

    ostap (
      parse:
          a:stmt ";" b:parse { Seq (a, b) }
        | stmt;

      expr: !(Expr.parse) ;

      else_stmt:
          %"elif" e:expr %"then" s1:parse s2:else_stmt { If (e, s1, s2) }
        | %"else" s:parse { s }
        | empty { Skip } ;

      stmt:
          x:IDENT
          keys:(-"[" expr -"]")*
          ":=" e:expr                         { Assign (x, keys, e) }
        | %"skip"                             { Skip }
        | %"return" e_opt:expr?               { Return e_opt }
        | %"while" e:expr %"do" s:parse %"od" { While (e, s) }
        | %"repeat" s:parse %"until" e:expr   { Repeat (s, e) }
        | %"if" e:expr %"then"
          s1:parse s2:else_stmt %"fi"         { If (e, s1, s2) }
        | %"for" start:parse ","
          e:expr "," loop:parse
          %"do" body:parse %"od"              { Seq (start, While(e, Seq (body, loop))) }
        | call:!(Expr.call)                   {
          match call with
          | Expr.Call (f, args) -> Call (f, args)
          | _ -> failwith "Unreachable"
        }
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      id: IDENT ;

      parse: %"fun" name:id "(" args:!(Util.list0 id) ")"
        vars:(%"local" !(Util.list id))?
        "{" body:!(Stmt.parse) "}"
        { name, (args, (match vars with None -> [] | Some v -> v), body) }
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M   = Map.Make (String) in
  let m          = List.fold_left (fun m (name, def) -> M.add name def m) M.empty defs in
  let _, _, o, _ =
    Stmt.eval
      (object (self)
         method call f args ((st, i, o, r) as conf) =
          try
            let xs, locs, body   = M.find f m in
            let st'              = List.fold_left2 (fun st x a -> State.update x a st) (State.enter st (xs @ locs)) xs args in
            let st'', i', o', r' = Stmt.eval self (st', i, o, r) Stmt.Skip body in
            (State.leave st'' st, i', o', r')
          with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
