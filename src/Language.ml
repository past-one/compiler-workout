(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let value (_, _, _, r) = match r with
| Some v -> v
| None   -> failwith "Trying to get None value"

(* States *)
module State =
  struct
    (* State: global state, local state, scope variables *)
    type t = { g: string -> int; l: string -> int; scope: string list }

    let emptyFun x = failwith (Printf.sprintf "Undefined variable %s" x)

    (* Empty state *)
    let empty = { g = emptyFun; l = emptyFun; scope = [] }

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let upd f y = if x = y then v else f y in
      if List.mem x s.scope
      then { s with l = upd s.l }
      else { s with g = upd s.g }

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st scope = { g = st.g; l = emptyFun; scope = scope }

    (* Drops a scope *)
    let leave fromSt toSt = { toSt with g = fromSt.g }

  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

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
    type config = State.t * int list * int list * int option

    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method call : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)
    let rec eval env ((s, _, _, _) as conf) =
      let (>>>) c e = eval env c e in
      let result (s, i, o, _) r = (s, i, o, Some r) in
      function
      | Const z          -> result conf z
      | Var name         -> result conf @@ State.eval s name
      | Binop (op, x, y) ->
        let c  = conf >>> x in
        let c' = c    >>> y in
        result c' @@ binop op (value c) @@ value c'
      | Call (f, exprs)  ->
        let folding (tl, c) e = let c' = c >>> e in (value c' :: tl), c' in
        let rev_args, conf' = List.fold_left folding ([], conf) exprs in
        env#call f (List.rev rev_args) conf'

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
         primary
        );

      call: f:IDENT "(" args:!(Util.list0 parse) ")" { Call (f, args) } ;

      primary:
          call
        | x:IDENT   { Var x }
        | d:DECIMAL { Const d }
        | -"(" parse -")"
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* Statement evaluator

         val eval : env -> config -> t -> t -> config

       Takes an environment, a configuration, a continuation and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env conf k =
      let (<.>) a b = match a, b with
      | s, Skip -> s
      | s1, s2  -> Seq (s1, s2)
      in
      let (>>) c = function Skip -> c | stmt -> eval env c Skip stmt in
      let (>>>) c e = Expr.eval env conf e in
      function
      | Skip             -> conf >> k
      | Read var         -> (
        match conf with
        | s, z::tl, o, _ -> (State.update var z s, tl, o, None) >> k
        | _ -> failwith "Unexpected end of input"
      )
      | Assign (var, e)  ->
        let (s', i', o', r) as conf' = conf >>> e in
        (State.update var (value conf') s', i', o', None) >> k
      | Write e          ->
        let (s', i', o', r) as conf' = conf >>> e in
        (s', i', o' @ [value conf'], None) >> k
      | Seq (a, b)       -> eval env conf (b <.> k) a
      | If (e, a, b)     ->
        let c' = conf >>> e in
        eval env c' k (if value c' <> 0 then a else b)
      | While (e, body)  ->
        let c' = conf >>> e in
        c' >> (if value c' <> 0 then Seq (body, While (e, body)) <.> k else k)
      | Repeat (body, e) -> 
        conf >> body >> (If (e, Skip, Repeat (body, e)) <.> k)
      | Return None      -> conf
      | Return Some e    -> conf >>> e
      | Call (f, exprs)  -> conf >>> Expr.Call (f, exprs) >> k

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
          %"read" "(" x:IDENT ")"             { Read x }
        | %"write" "(" e:expr ")"             { Write e }
        | x:IDENT ":=" e:expr                 { Assign (x, e) }
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
         method call f args (st, i, o, r) =
           let xs, locs, body   = M.find f m in
           let st'              = List.fold_left2 (fun st x a -> State.update x a st) (State.enter st (xs @ locs)) xs args in
           let st'', i', o', r' = Stmt.eval self (st', i, o, r) Stmt.Skip body in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
