(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 4 (0..3) by now *)
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4

(* We need to distinguish the following operand types: *)
type opnd =
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)

(* For convenience we define the following synonyms for the registers: *)
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string

(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl"
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s

(* Opening stack machine to use instructions without fully qualified names *)
open SM

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)
let compile environment code =
  let move a b = match a, b with (* we can't move data directly from stack to memory or vice versa *)
  | R _, _ -> [Mov (a, b)]
  | _, R _ -> [Mov (a, b)]
  | _      -> [Mov (a, eax); Mov (eax, b)]
  in
  let binop op = function
  | a, R z -> [Binop (op, a, R z)]
  | a, b   -> [
    Mov (b, edx);
    Binop (op, a, edx);
    Mov (edx, b)
    ]
  in
  let apply (a, b) f = b, f a in
  let hash s =
    let charCode = function
    | '_'            -> 53
    | c when c > 'Z' -> Char.code c - 70
    | c              -> Char.code c - 64
    in
    let len = min 5 @@ String.length s in
    let rec hash' acc = function
    | k when k >= len -> acc
    | k               -> hash' ((acc lsl 6) lor (charCode s.[k])) @@ k + 1
    in
    hash' 0 0
  in

  let call env f args isFunc =
    let argsNum = List.length args in
    let argPushes = List.map (fun arg -> Push arg) args in
    let argPushes =
      if f = "Barray"
      then argPushes @ [Push (L argsNum)]
      else argPushes
    in
    let argPop = match argsNum with
    | 0 -> []
    | _ -> [Binop ("+", L (argsNum * word_size), esp)]
    in

    let regs = env#live_registers in
    let regPushes = List.map (fun r -> Push r) regs in
    let regPops = List.rev_map (fun r -> Pop r) regs in
    let env', resultPop =
      if isFunc
      then apply env#allocate @@ fun x -> [Mov (eax, x)]
      else env, []
    in
    env', regPushes @ argPushes @ [Call f] @ argPop @ regPops @ resultPop
  in

  let compileInsn env i = match i with
  | JMP l       -> env, [Jmp l]
  | LABEL l     -> env, [Label l]
  | RET false   -> env, [Jmp env#epilogue]
  | END         -> env, [
    Label env#epilogue; Mov (ebp, esp); Pop ebp; Ret;
    Meta (Printf.sprintf "\t.set %s, %d" env#lsize (env#allocated * word_size))
  ] (* epilog *)

  | RET true    -> apply env#pop                   @@ fun x -> [Mov (x, eax); Jmp env#epilogue]
  | CONST z     -> apply env#allocate              @@ fun x -> [Mov (L z, x)]
  | ST var      -> apply (env#global var)#pop      @@ fun x -> move x @@ env#loc var
  | LD var      -> apply (env#global var)#allocate @@ fun x -> move (env#loc var) x

  | CJMP (k, l) -> apply env#pop (function
    | (R _) as x ->                        [Binop ("cmp", L 0, x); CJmp (k, l)]
    | x          -> [Binop ("^", eax, eax); Binop ("cmp", eax, x); CJmp (k, l)]
  )

  | DROP  -> snd @@ env#pop, []
  | DUP   ->
    let xFrom = env#look in
    let xTo, env' = env#allocate in
    env', move xFrom xTo
  | SWAP  -> env#swap, []
  | STRING s ->
    let str, env' = env#string s in
    call env' "Bstring" [M ("$" ^ str)] true
  | SEXP (s, length) ->
    let t = hash s in
    let args, env' = env#popN length in
    call env' "Bsexp" (L t :: (args @ [L length])) true
  | STA (var, n) ->
    let value, env' = (env#global var)#pop in
    let args, env'' = env'#popN n in
    call env'' "Bsta" (args @ [env''#loc var; value; L n]) true
  | TAG s ->
    let t = hash s in
    let arg, env' = env#pop in
    call env' "Btag" [L t; arg] true
  | ENTER vars -> failwith "Not implemented"
  | LEAVE -> failwith "Not implemented"

  | BEGIN (f, args, vars) ->
    let env' = env#enter f args vars in
    env', [Push ebp; Mov (esp, ebp); Binop ("-", M ("$" ^ env'#lsize), esp)] (* prolog *)
  | CALL (f, argsNum, isFunc) ->
    let f' =
      if f.[0] = '.'
      then "B" ^ String.sub f 1 (String.length f - 1)
      else f
    in
    let args, env' = env#popN argsNum in
    call env' f' args isFunc

  | BINOP op -> let x, env' = env#pop in let y = env'#look in env', (
    let cmpF a b suf = [
      Mov (a, edx);
      Binop ("^", eax, eax); (* set eax to zero first *)
      Binop ("cmp", edx, b);
      Set (suf, "%al");
      Mov (eax, b)
    ]
    in
    let cmp = cmpF x y in
    let div reg = [
      Mov (y, eax);
      Cltd; (* prepare eax *)
      IDiv x;
      Mov (reg, y)
    ]
    in
    match op with
    | "==" -> cmp "e"
    | "!=" -> cmp "ne"
    | ">"  -> cmp "g"
    | ">=" -> cmp "ge"
    | "<"  -> cmp "l"
    | "<=" -> cmp "le"
    | "/"  -> div eax
    | "%"  -> div edx
    | "!!" -> binop "!!" (x, y) @ cmpF (L 0) y "ne"
    | "&&" -> cmpF (L 0) x "ne" @ cmpF (L 0) y "ne" @ binop "&&" (x, y)
    | op   -> binop op (x, y)
  )
  in
  let folding (e, oldInstr) i = let e, newInstr = compileInsn e i in (e, oldInstr @ newInstr) in
  List.fold_left folding (environment, []) code

(* A set of strings *)
module S = Set.Make (String)

(* A map indexed by strings *)
module M = Map.Make (String)

(* Environment implementation *)
let make_assoc =
  let rec make_assoc' n = function
  | []       -> []
  | hd :: tl -> (hd, n) :: make_assoc' (n + 1) tl
  in
  make_assoc' 0

class env =
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stringm     = M.empty (* a string map                      *)
    val scount      = 0       (* string count                      *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)

    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->
        try S (List.assoc x locals) with Not_found -> M ("global_" ^ x)

    (* allocates a fresh position on a symbolic stack *)
    method allocate =
      let x, n =
        let rec allocate' = function
        | []                            -> ebx       , 0
        | S n :: S m :: _               ->
          let next = (max n m) + 1 in      S next    , next + 1
        | R _ :: S n :: _
        | S n :: _                      -> S (n + 1) , n + 2
        | R n :: R m :: _               ->
          let next = (max n m) + 1 in
          if next <= num_of_regs
          then                             R next    , 0
          else                             S 0       , 1
        | R n :: _ when n < num_of_regs -> R (n + 1) , 0
        | _                             -> S 0       , 1
        in
        allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = (
      match stack with
      | x::stack' -> x, {< stack = stack' >}
      | _         -> failwith "pop with empty symbolic stack"
      )

    (* pops n operands from the symbolic stack *)
    method popN n =
      let rec popN' env args = function
      | 0 -> List.rev args, env
      | n -> let x, env' = env#pop in popN' env' (x :: args) @@ n - 1
      in
      popN' self [] n

    (* returns current stack head *)
    method look = (
      match stack with
      | x::_ -> x
      | _    -> failwith "look with empty symbolic stack"
      )

    method swap = (
      match stack with
      | x::y::tl -> {< stack = y::x::tl >}
      | _       -> failwith "swap with empty symbolic stack"
      )

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* registers a string constant *)
    method string x =
      try M.find x stringm, self
      with Not_found ->
        let y = Printf.sprintf "string_%d" scount in
        let m = M.add x y stringm in
        y, {< scount = scount + 1; stringm = m>}

    (* gets all global variables *)
    method globals = S.elements globals

    (* gets all string definitions *)
    method strings = M.bindings stringm

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots + List.length locals

    (* enters a function *)
    method enter f a l = {<
      stack_slots = 0;
      stack = [];
      locals = make_assoc l;
      args = make_assoc a;
      fname = f
      >}

    (* returns a label for the epilogue *)
    method epilogue = fname ^ "_epilogue"

    (* returns a name for local size meta-symbol *)
    method lsize = fname ^ "_SIZE" 

    (* returns a list of live registers *)
    method live_registers = List.filter (function R _ -> true | _ -> false) stack

  end

(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Const 0))) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (List.map (fun s      -> Meta (Printf.sprintf "%s:\t.int\t0"         s  )) env#globals) @
                               (List.map (fun (s, v) -> Meta (Printf.sprintf "%s:\t.string\t\"%s\"" v s)) env#strings) in
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (show i ^ "\n"))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (name ^ ".s") in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)
