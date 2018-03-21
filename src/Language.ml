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

    let toInt f x y = if f x y then 1 else 0

    let binop = function
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
      | Binop (op, x, y) -> (binop op) (eval state x) (eval state y)

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
    (* loop with a post-condition       *) (* add yourself *)  with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval config stmt = match config, stmt with
      | (s, z::i, o), Read   var      -> (Expr.update var z s, i, o)
      | (s, i, o),    Write  e        -> (s, i, o @ [Expr.eval s e])
      | (s, i, o),    Assign (var, e) -> (Expr.update var (Expr.eval s e) s, i, o)
      | conf,         Seq    (a, b)   -> eval (eval conf a) b
      | _,            Read   _        -> failwith "Unexpected end of input"

    (* Statement parser *)

    ostap (
      parse:
          a:stmt -";" b:parse { Seq (a, b) }
        | stmt;

      stmt:
          "read" -"(" x:IDENT -")"          { Read x }
        | "write" -"(" e:!(Expr.parse) -")" { Write e }
        | x:IDENT -":=" e:!(Expr.parse)     { Assign (x, e) }
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
