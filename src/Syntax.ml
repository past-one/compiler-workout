(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 

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

    let boolToInt v = match v with
      | true  -> 1
      | false -> 0

    let intToBool v = match v with
      | 0 -> false
      | _ -> true

    let evalBinop op a b = match op with
      | "+"  -> a + b
      | "-"  -> a - b
      | "*"  -> a * b
      | "/"  -> a / b
      | "%"  -> a mod b
      | "<"  -> boolToInt (a <  b)
      | "<=" -> boolToInt (a <= b)
      | ">"  -> boolToInt (a >  b)
      | ">=" -> boolToInt (a >= b)
      | "==" -> boolToInt (a =  b)
      | "!=" -> boolToInt (a <> b)
      | "&&" -> boolToInt (intToBool a && intToBool b)
      | "!!" -> boolToInt (intToBool a || intToBool b)
      | unknown -> failwith (Printf.sprintf "Undefined binop %s" unknown)

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec eval s e = match e with
      | Const i -> i
      | Var   name -> s name
      | Binop (op, e1, e2) -> evalBinop op (eval s e1) (eval s e2)

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let eval _ = failwith "Not implemented yet"
                                                         
  end
