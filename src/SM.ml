open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

let evalInsn config insn = match config, insn with
  | (y::x::stack, conf),   BINOP op -> ((Expr.binop op x y)::stack, conf)
  | (stack, conf),         CONST z  -> (z::stack, conf)
  | (stack, (s, z::i, o)), READ     -> (z::stack, (s, i, o))
  | (z::stack, (s, i, o)), WRITE    -> (stack, (s, i, o @ [z]))
  | (stack, (s, i, o)),    LD var   -> ((s var)::stack, (s, i, o))
  | (z::stack, (s, i, o)), ST var   -> (stack, (Expr.update var z s, i, o))
  | _,                     _        -> failwith "Invalid instruction"

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)
let rec eval = List.fold_left evalInsn

let rec compileExpr = function
  | Expr.Const z          -> [CONST z]
  | Expr.Var   var        -> [LD var]
  | Expr.Binop (op, x, y) -> compileExpr x @ compileExpr y @ [BINOP op]

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile (stmt: Stmt.t) : prg = match stmt with
  | Stmt.Read   var         -> [READ ; ST var]
  | Stmt.Write  expr        -> compileExpr expr @ [WRITE]
  | Stmt.Assign (var, expr) -> compileExpr expr @ [ST var]
  | Stmt.Seq    (a, b)      -> compile a @ compile b
