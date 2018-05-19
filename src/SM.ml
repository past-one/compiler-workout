open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

let showInsn i = GT.transform(insn) (new @insn[show]) () i

let showAll is = String.concat "\n" @@ List.map showInsn is

let fail i = failwith @@ "Invalid instruction " ^ showInsn i

let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (taken, rest)
  | n -> (match rest with h::tl -> unzip (h::taken, tl) (n-1) | _ -> failwith "Unexpected end of splitten list")
  in
  unzip ([], l) n

let init f n =
  let rec inner tail = function
  | 0            -> (f 0) :: tail
  | i when i > 0 -> inner ((f i) :: tail) @@ i - 1
  | i            -> failwith @@ "Invalid init argument " ^ string_of_int i
  in
  List.rev @@ inner [] n

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)

 *)
let rec eval env ((_, stack, _) as config) allInsns =
  let evalInsn (cstack, stack, ((s, i, o, r) as c)) insn = match insn with
  | BINOP op            ->
    (match stack with
    | y::x::tl -> cstack, Value.of_int (Expr.binop op (Value.to_int x) @@ Value.to_int y) :: tl, c
    | _ -> fail insn
    )
  | ST var              ->
    (match stack with
    | hd::tl   -> cstack, tl, (State.update var hd s, i, o, r)
    | _ -> fail insn
    )
  | STA (var, n)        ->
    (match stack with
    | hd::stack' ->
      let (splitted, stack'') = split n stack' in
      cstack, stack', (Stmt.update s var hd splitted, i, o, r)
    | _ -> fail insn
    )
  | ENTER vars          ->
    let (splitted, stack') = split (List.length vars) stack in
    let state = List.fold_left2 (fun s x v -> State.bind x v s) State.undefined vars splitted in
    cstack, stack', (State.push s state vars, i, o, r)
  | SEXP (s, n)         ->
    let (splitted, stack') = split n stack in
    cstack, (Value.sexp s splitted)::stack', c
  | DROP                ->
    (match stack with
    | _::tl    -> cstack, tl, c
    | _ -> fail insn
    )
  | DUP                 ->
    (match stack with
    | hd::tl   -> cstack, hd::hd::tl, c
    | _ -> fail insn
    )
  | SWAP                ->
    (match stack with
    | y::x::tl -> cstack, x::y::tl, c
    | _ -> fail insn
    )
  | TAG s               ->
    (match stack with
    | Value.Sexp (s', _) ::tl when s = s' -> cstack, (Value.of_int 1)::tl, c
    | _::tl                               -> cstack, (Value.of_int 0)::tl, c
    | _ -> fail insn
    )
  | LEAVE               -> cstack, stack, (State.pop s, i, o, r)
  | LD var              -> cstack, State.eval s var::stack, c
  | STRING s            -> cstack, Value.of_string s::stack, c
  | CONST z             -> cstack, Value.of_int z::stack, c
  | BEGIN (_, args, xs) ->
    let splitted, stack' = split (List.length args) stack in
    let s' = List.fold_left2 (fun s x v -> State.update x v s) (State.enter s @@ args @ xs) args splitted in
    cstack, stack', (s', i, o, r)
  | _                   -> fail insn
  in

  match allInsns with
  | LABEL _ :: tl -> eval env config tl
  | JMP l   :: _  -> eval env config @@ env#labeled l
  | RET _   :: _
  | END     :: _  -> (
    match config with
    | (prog, s)::cstack', stack, (s', i, o, r) ->
      eval env (cstack', stack, (State.leave s' s, i, o, r)) prog
    | _ -> config
    )
  | CALL (f, nArgs, isFunc) :: tl ->
    let cstack, stack, ((s, _, _, _) as conf) = config in
    if env#is_label f
    then eval env ((tl, s)::cstack, stack, conf) @@ env#labeled f
    else eval env (env#builtin config f nArgs isFunc) tl
  | CJMP (suf, l) :: tl ->
    let cond z = match suf with
    | "z"   -> Value.to_int z =  0
    | "nz"  -> Value.to_int z <> 0
    | other -> failwith @@ "Unknown CJMP condition " ^ other
    in (
      match config with
      | cst, hd :: stack, conf -> eval env (cst, stack, conf) (if cond hd then env#labeled l else tl)
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
         method builtin (cstack, stack, (st, i, o, _)) f nArgs isFunc =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split nArgs stack in
           let (st, i, o, r) = Builtin.eval (st, i, o, None) args f in
           let stack'' = if isFunc then get r::stack' else stack' in
           (cstack, stack'', (st, i, o, None))
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
  | Expr.Array exprs      -> call ".array" exprs true
  | Expr.Sexp (s, exprs)  -> compileExprList exprs @ [SEXP (s, List.length exprs)]
  | Expr.String s         -> [STRING s]
  | Expr.Var x            -> [LD x]
  | Expr.Binop (op, a, b) -> compileExpr a @ compileExpr b @ [BINOP op]
  | Expr.Elem (v, k)      -> call ".elem" [v; k] true
  | Expr.Length v         -> call ".length" [v] true
  | Expr.Call (f, exprs)  -> call f exprs true
  and compileExprList exprs = List.fold_left (fun ac e -> compileExpr e @ ac) [] @@ List.rev exprs
  and call f exprs isFunc = compileExprList exprs @ [CALL (f, List.length exprs, isFunc)]
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

  let rec compileStmt gen lEnd =
    let start g insns = insns, false, g in
    let just = start gen in
    function
    | Stmt.Assign (x, [], e)   -> just @@ compileExpr e @ [ST x]
    | Stmt.Assign (x, keys, e) -> just @@ compileExprList keys @
      compileExpr e @ [STA (x, List.length keys)]

    | Stmt.Skip                -> just []
    | Stmt.Leave               -> just [LEAVE]
    | Stmt.Return None         -> just [RET false]
    | Stmt.Return (Some e)     -> just @@ compileExpr e @ [RET true]
    | Stmt.Call (f, exprs)     -> just @@ call f exprs false
    | Stmt.Seq (a, b)          ->
      let lMid, gen' = gen#get in
      compileStmt gen' lMid a >? lMid >> (b, lEnd)

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

    | Stmt.Case (e, branches)  ->
      let revPathElem revPath =
        DUP :: (List.concat @@
        List.rev_map (fun i -> [CONST i; CALL (".elem", 2, true)]) revPath
        )
      in
      let rec compileCheck revPath lNext = function
      | Stmt.Pattern.Wildcard     -> []
      | Stmt.Pattern.Ident _      -> []
      | Stmt.Pattern.Sexp (s, ps) ->
        revPathElem revPath @ [TAG s; CJMP ("z", lNext)] @
        revPathElem revPath @ [
          CALL (".length", 1, true);
          CONST (List.length ps);
          BINOP "==";
          CJMP ("z", lNext)
        ] @ List.concat @@ List.mapi (fun i pat -> compileCheck (i::revPath) lNext pat) ps
      in
      let rec bind revPath = function
      | Stmt.Pattern.Wildcard     -> []
      | Stmt.Pattern.Ident x      -> revPathElem revPath @ [SWAP]
      | Stmt.Pattern.Sexp (_, ps) ->
        List.concat @@ List.mapi (fun i pat -> bind (i::revPath) pat) ps
      in
      let rec compileBranches (prev, _, g) = function
      | [] -> (prev @ [DROP], true, g)
      | (pat, stmt) :: otherBranches ->
        let lNext, g' = g#get in
        let body, _, g'' =
          start g' (bind [] pat @ [DROP; ENTER (Stmt.Pattern.vars pat)]) >> (stmt, lEnd)
        in
        (match (compileCheck [] lNext pat) with
        | []    -> start g'' @@ prev @ body
        | check ->
          let current = start g'' @@ prev @ check @ body @ [JMP lEnd; LABEL lNext] in
          compileBranches current otherBranches
        )
      in
      compileBranches (just @@ compileExpr e) branches >! true

  and (>?) (insns, need, g) l = insns @ labelIf need l, need, g
  and (>@) (insns, need, g) o = insns @ o, need, g
  and (>!) (insns, _, g) need = insns, need, g
  and (>>) (insns, _, g) (stmt, l) =
    let body, need, g' = compileStmt g l stmt in
    insns @ body, need, g'
  in

  let rec compileDefs gen defs =
    let folding (insns, g) (f, (args, vars, body)) =
      let l, g' = g#get in
      let result, _, g'' = compileStmt g' l body >? l in
      insns @ [LABEL f; BEGIN (f, args, vars)] @ result @ [END], g''
    in
    fst @@ List.fold_left folding ([], gen) defs
  in

  let main, _, gen' = compileStmt gen label stmt >? label in
  main @ [END] @ compileDefs gen' defs
