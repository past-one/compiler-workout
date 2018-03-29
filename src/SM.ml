open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string
(* conditional jump                *) | CJMP  of string * string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
 *)
let rec eval env (config: config) : prg -> config =
  let fail (i: insn) = failwith @@ "Invalid instruction " ^ (GT.transform(insn) (new @insn[show]) () i)
  in let evalInsn ((stack, ((s, i, o) as conf)): config) (insn : insn) : config = match insn with
  | BINOP op -> (match stack with y::x::tl -> (Expr.binop op x y) :: tl, conf    | _ -> fail insn)
  | READ     -> (match i     with z::tl    -> (z::stack, (s, tl, o))             | _ -> fail insn)
  | WRITE    -> (match stack with z::tl    -> stack, (s, i, o @ [z])             | _ -> fail insn)
  | ST var   -> (match stack with z::tl    -> stack, (Expr.update var z s, i, o) | _ -> fail insn)
  | LD var   -> (s var)::stack, conf
  | CONST z  -> z::stack, conf
  | _        -> fail insn
  in function
  | LABEL _       :: tl -> eval env config tl
  | JMP l         :: _  -> eval env config @@ env#labeled l
  | CJMP (suf, l) :: tl -> (
    let condition z = match suf with
    | "z"   -> z =  0
    | "nz"  -> z <> 0
    | other -> failwith @@ "Unknown condition " ^ other
    in match config with
    | z :: stack, conf -> if condition z then (eval env config @@ env#labeled l) else eval env config tl
    | _                -> fail @@ CJMP (suf, l)
    )
  | insn          :: tl -> eval env (evalInsn config insn) tl
  | []                  -> config

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String)
  in let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let compile stmt =
  let rec compileExpr = function
  | Expr.Const  z          -> [CONST z]
  | Expr.Var    x          -> [LD x]
  | Expr.Binop  (op, a, b) -> compileExpr a @ compileExpr b @ [BINOP op]
  in let label, labeling = (
    object 
    val counter = 0 
    method gen = "L" ^ string_of_int counter, {< counter = counter + 1 >} 
    end
    )#gen
  in let labelIf need l = if need then [LABEL l] else []
  in let rec compile' labeling lEnd = function
  | Stmt.Read   x          -> [READ; ST x], false, labeling
  | Stmt.Write  e          -> compileExpr e @ [WRITE], false, labeling
  | Stmt.Assign (x, e)     -> compileExpr e @ [ST x], false, labeling
  | Stmt.Skip              -> [], false, labeling
  | Stmt.Seq    (a, b)     ->
    let lMid, labeling = labeling#gen
    in let first, needLMid, labeling = compile' labeling lMid a 
    in let second, needL, labeling = compile' labeling lEnd b 
    in first @ labelIf needLMid lMid @ second, needL, labeling
  | Stmt.If     (e, a, b)  ->
    let lElse, labeling = labeling#gen
    in let first,  _, labeling = compile' labeling lEnd a
    in let second, _, labeling = compile' labeling lEnd b
    in compileExpr e @ [CJMP ("z", lElse)] @ first @ [JMP lEnd; LABEL lElse] @ second, true, labeling
  | Stmt.While  (e, s)     ->
    let lCheck,     labeling = labeling#gen
    in let lStart,  labeling = labeling#gen
    in let body, _, labeling = compile' labeling lCheck s
    in [JMP lCheck; LABEL lStart] @ body @ [LABEL lCheck]
      @ compileExpr e @ [CJMP ("nz", lStart)], false, labeling
  | Stmt.Until  (e, s)     -> 
    let lMid, labeling = labeling#gen
    in let lStart, labeling = labeling#gen
    in let body, needLMid, labeling = compile' labeling lMid s
    in [LABEL lStart] @ body @ labelIf needLMid lMid @ compileExpr e @ [CJMP ("z", lStart)], false, labeling
  in let p, needL, _ = compile' labeling label stmt 
  in p @ labelIf needL label
