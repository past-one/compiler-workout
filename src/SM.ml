open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP  of string
(* put a constant on the stack     *) | CONST  of int
(* put a string on the stack       *) | STRING of string
(* load a variable to the stack    *) | LD     of string
(* store a variable from the stack *) | ST     of string
(* store in an array               *) | STA    of string * int
(* a label                         *) | LABEL  of string
(* unconditional jump              *) | JMP    of string
(* conditional jump                *) | CJMP   of string * string
(* begins procedure definition     *) | BEGIN  of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL   of string * int * bool
(* returns from a function         *) | RET    of bool with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

let fail (i: insn) = failwith @@ "Invalid instruction " ^ (GT.transform(insn) (new @insn[show]) () i)

let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)

 *)
let rec eval env config =
  let evalInsn (cstack, stack, ((s, i, o, r) as c)) insn = match insn with
  | BINOP op            ->
    (match stack with
    | y::x::tl -> cstack, (Expr.binop op x y) :: tl, c
    | _ -> fail insn
    )
  | ST var              ->
    (match stack with
    | z::tl    -> cstack, stack, (State.update var (Value.of_int z) s, i, o, r)
    | _ -> fail insn
    )
  | LD var              -> cstack, (Value.to_int @@ State.eval s var)::stack, c
  | CONST z             -> cstack, z::stack, c
  | BEGIN (_, args, xs) ->
    let folding (state, stack) arg = match stack with
    | z :: tl -> State.update arg (Value.of_int z) state, tl
    | []      -> failwith "Not enough args on stack"
    in
    let s', stack' = List.fold_left folding (State.enter s @@ args @ xs, stack) args in
    cstack, stack', (s', i, o, r)
  | _                   -> fail insn
  in

  function
  | LABEL _ :: tl -> eval env config tl
  | JMP l   :: _  -> eval env config @@ env#labeled l
  | RET _   :: _
  | END     :: _  -> (
    match config with
    | (prog, s)::cstack', stack, (s', i, o, r) ->
      eval env (cstack', stack, (State.leave s' s, i, o, r)) prog
    | _ -> config
    )
  | CALL (f, _, _) :: tl ->
    let cstack, stack, ((s, _, _, _) as conf) = config in
    eval env ((tl, s)::cstack, stack, conf) @@ env#labeled f
  | CJMP (suf, l) :: tl ->
    let cond z = match suf with
    | "z"   -> z =  0
    | "nz"  -> z <> 0
    | other -> failwith @@ "Unknown CJMP condition " ^ other
    in (
      match config with
      | cst, z :: stack, conf -> eval env (cst, stack, conf) (if cond z then env#labeled l else tl)
      | _ -> fail @@ CJMP (suf, l)
    )
  | insn :: tl -> eval env (evalInsn config insn) tl
  | []                  -> config

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o, _)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o, _)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, [], None))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let compile (defs, stmt) =
  let rec compileExpr = function
  | Expr.Const z          -> [CONST z]
  | Expr.Var x            -> [LD x]
  | Expr.Binop (op, a, b) -> compileExpr a @ compileExpr b @ [BINOP op]
  | Expr.Call (f, exprs)  -> call f exprs true
  and call f exprs isFunc =
    List.fold_left (fun ac e -> compileExpr e @ ac) [] exprs @ [CALL (f, List.length exprs, isFunc)]
  in

  let label, gen = (
    object (self)
    val counter = 0
    method get  = "L" ^ string_of_int counter, {< counter = counter + 1 >}
    method get2 =
      let l1, self1 = self#get in
      let l2, self2 = self1#get in
      l1, l2, self2
    end
    )#get
  in
  let labelIf need l = if need then [LABEL l] else [] in

  let rec compile' gen lEnd =
    let start g insns = insns, false, g in
    let just = start gen in
    function
    | Stmt.Assign (x, keys, e) -> just @@ compileExpr e @ [ST x]
    | Stmt.Skip                -> just []
    | Stmt.Return None         -> just [RET false]
    | Stmt.Return (Some e)     -> just @@ compileExpr e @ [RET true]
    | Stmt.Call (f, exprs)     -> just @@ call f exprs false
    | Stmt.Seq (a, b)          ->
      let lMid, gen' = gen#get in
      compile' gen' lMid a >? lMid >> (b, lEnd)
    | Stmt.If (e, a, b)        ->
      let lElse, gen' = gen#get in
      start gen' (compileExpr e) >@
      [CJMP ("z", lElse)] >>
      (a, lEnd) >@
      [JMP lEnd; LABEL lElse] >>
      (b, lEnd) >! true
    | Stmt.While  (e, s)       ->
      let lCheck, lStart, gen' = gen#get2 in
      start gen' [JMP lCheck; LABEL lStart] >>
      (s, lCheck) >@
      ([LABEL lCheck] @ compileExpr e) >@
      [CJMP ("nz", lStart)] >! false
    | Stmt.Repeat (s, e)       ->
      let lMid, lStart, gen' = gen#get2 in
      start gen' [LABEL lStart] >>
      (s, lMid) >? lMid >@
      (compileExpr e @ [CJMP ("z", lStart)]) >! false
  and (>?) (insns, need, g) l = insns @ labelIf need l, need, g
  and (>@) (insns, need, g) o = insns @ o, need, g
  and (>!) (insns, _, g) need = insns, need, g
  and (>>) (insns, _, g) (stmt, l) =
    let body, need, g' = compile' g l stmt in
    insns @ body, need, g'
  in

  let rec compileDefs gen defs =
    let folding (insns, g) (f, (args, vars, body)) =
      let l, g' = g#get in
      let result, _, g'' = compile' g' l body >? l in
      insns @ [LABEL f; BEGIN (f, args, vars)] @ result @ [END], g''
    in
    fst @@ List.fold_left folding ([], gen) defs
  in

  let main, _, gen' = compile' gen label stmt >? label in
  main @ [END] @ compileDefs gen' defs
