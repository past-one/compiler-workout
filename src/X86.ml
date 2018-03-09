(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 0-3 by now *)
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
  | op    -> failwith (Printf.sprintf "unknown binary operator %s" op)
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
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

(* Opening stack machine to use instructions without fully qualified names *)
open SM

(* A set of strings *)
module S = Set.Make (String)

(* Environment implementation *)
class env =
  object (self)
    val stack_slots = 0        (* maximal number of stack positions *)
    val globals     = S.empty  (* a set of global variables         *)
    val stack       = []       (* symbolic stack                    *)

    (* gets a name for a global variable *)
    method loc x = "global_" ^ x

    (* allocates a fresh position on a symbolic stack *)
    method allocate =
      let x, n =
  let rec allocate' = function
  | []                            -> ebx     , 0
  | (S n)::_                      -> S (n+1) , n+1
  | (R n)::_ when n < num_of_regs -> R (n+1) , stack_slots
  | _                             -> S 0     , 1
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

    (* pops one operand from the symbolic stack and also returns current stack head *)
    method popAndLook = (
      match stack with
        | x::y::stack' -> x, y, {< stack = y::stack' >}
        | _            -> failwith "popAndLook with empty symbolic stack"
    )

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* gets the number of allocated stack slots *)
    method allocated = stack_slots

    (* gets all global variables *)
    method globals = S.elements globals
  end

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
   *)
let compile (environment: env) (code: prg) : env * instr list =
  let swap a b = match a, b with (* we can't move data directly from stack to memory or vice versa *)
  | R _, _ -> [Mov (a, b)]
  | _, R _ -> [Mov (a, b)]
  | _      -> [Mov (a, eax); Mov (eax, b)]
  in let compileInsn env i = match i with
  | WRITE    -> let x, env = env#pop                   in env, [Push x; Call "_Lwrite"]
  | CONST z  -> let x, env = env#allocate              in env, [Mov (L z, x)]
  | ST var   -> let x, env = (env#global var)#pop      in env, swap x @@ M (env#loc var)
  | LD var   -> let x, env = (env#global var)#allocate in env, swap (M (env#loc var)) x
  | READ     -> let x, env = env#allocate              in env, [Call "_Lread"; Mov (eax, x)]
  | BINOP op -> let x, y, env = env#popAndLook         in env, (
    let cmpF a b suf = [
      Mov (a, edx);
      Binop ("^", eax, eax); (* set eax to zero first *)
      Binop ("cmp", edx, b);
      Set (suf, "%al");
      Mov (eax, b)
    ]
    in let cmp = cmpF x y
    in let div reg = [
      Mov (y, eax);
      Cltd; (* prepare eax *)
      IDiv x;
      Mov (reg, y)
      ]
    in let binop op = function
      | a, R z -> [Binop (op, a, R z)]
      | a, b   -> [
        Mov (b, edx);
        Binop (op, a, edx);
        Mov (edx, b)
        ] (* we can't move data directly from stack to memory or vice versa *)
    in match op with
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
  in let compile' (e, oldInstr) i = let e, newInstr = compileInsn e i in (e, oldInstr @ newInstr)
  in List.fold_left compile' (environment, []) code

(* compiles a unit: generates x86 machine code for the stack program and surrounds it
   with function prologue/epilogue
*)
let compile_unit env scode =
  let env, code = compile env scode in
  env,
  ([Push ebp; Mov (esp, ebp); Binop ("-", L (word_size*env#allocated), esp)] @
   code @
   [Mov (ebp, esp); Pop ebp; Binop ("^", eax, eax); Ret]
  )

(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm prog =
  let env, code = compile_unit (new env) (SM.compile prog) in
  let asm = Buffer.create 1024 in
  Buffer.add_string asm "\t.data\n";
  List.iter
    (fun s ->
       Buffer.add_string asm (Printf.sprintf "%s:\t.int\t0\n" s)
    )
    env#globals;
  Buffer.add_string asm "\t.text\n";
  Buffer.add_string asm "\t.globl\t_main\n";
  Buffer.add_string asm "_main:\n";
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    code;
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build stmt name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm stmt);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)

