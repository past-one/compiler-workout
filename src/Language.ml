(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* State: a partial map from variables to integer values. *)
    type state = string -> int

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    let binop = 
      let toInt f x y = if f x y then 1 else 0 
      in function
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

    (* Expression evaluator

          val eval : state -> t -> int

       Takes a state and an expression, and returns the value of the expression in
       the given state.
    *)
    let rec eval state = function
      | Const i          -> i
      | Var   name       -> state name
      | Binop (op, x, y) -> binop op (eval state x) (eval state y)

    let ostapBinops ops = let ostapBinop op = (ostap ($(op)), fun x y -> Binop (op, x, y))
      in List.map ostapBinop ops;;

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as an int

    *)
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

      primary:
          x:IDENT {Var x}
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
    (* loop with a post-condition       *) | Until  of Expr.t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval ((s, i, o) as conf) = function
      | Read   var       -> (
        match i with
        | z::tl -> Expr.update var z s, tl, o
        | _     -> failwith "Unexpected end of input"
        )
      | Write  e         -> s, i, o @ [Expr.eval s e]
      | Assign (var, e)  -> Expr.update var (Expr.eval s e) s, i, o
      | Seq    (a, b)    -> eval (eval conf a) b
      | Skip             -> conf
      | If     (e, a, b) -> eval conf (if Expr.eval s e <> 0 then a else b)
      | While  (e, stmt) -> (
        if Expr.eval s e <> 0
        then eval conf @@ Seq (stmt, While (e, stmt))
        else conf
        )
      | Until  (e, stmt) -> let (s, _, _) as conf = eval conf stmt in (
        if Expr.eval s e = 0
        then eval conf @@ Until (e, stmt)
        else conf
        )

    (* Statement parser *)

    ostap (
      parse:
          a:stmt ";" b:parse { Seq (a, b) }
        | stmt;

      expr: !(Expr.parse) ;

      else_stmt:
          %"elif" e:expr %"then" s1:parse s2:else_stmt { If (e, s1, s2) }
        | %"else" s:parse { s }
        | "" { Skip } ;

      stmt:
          %"read" "(" x:IDENT ")"                      { Read x }
        | %"write" "(" e:expr ")"                      { Write e }
        | x:IDENT ":=" e:expr                          { Assign (x, e) }
        | %"skip"                                      { Skip }
        | %"while" e:expr %"do" s:parse %"od"          { While (e, s) }
        | %"repeat" s:parse %"until" e:expr            { Until (e, s) }
        | %"if" e:expr %"then"
          s1:parse s2:else_stmt %"fi"                  { If (e, s1, s2) }
        | %"for" start:parse "," e:expr "," loop:parse
          %"do" body:parse %"od"                       { Seq (start, While(e, Seq (body, loop))) }
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse
