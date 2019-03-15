#use "code-gen.ml";;

let handle_get_const_address const consts_table =
  let value = List.assoc const consts_table in
  match value with
  | (i,s) -> Printf.sprintf "const_tbl+%d" i;;

let handle_get_freeVar_address const tbl = 
  let index = List.assoc const tbl in
  Printf.sprintf "fvar_tbl+%d * WORD_SIZE" index


let makeMyPrims = 
"cons:
  push rbp
  mov rbp, rsp
  
  push r8
  push r9
  mov r8, PVAR(0)
  mov r9, PVAR(1)
  MAKE_PAIR(rax, r8, r9)

  pop r9
  pop r8
  leave
  ret
  
car:
  push rbp
  mov rbp, rsp

  mov rax, PVAR(0) ; rax = Pair(a,b)
  cmp byte [rax], T_PAIR
  jne .fail
  CAR rax, rax ; rax = a
  
  leave
  ret
  
  .fail:
  call write_fail_to_pair
  call exit

cdr:
  push rbp
  mov rbp, rsp
  
  mov rax, PVAR(0) ; rax = Pair(a,b)
  cmp byte [rax], T_PAIR
  jne .fail
  CDR rax, rax ; rax = b
  
  leave
  ret

   .fail:
  call write_fail_to_pair
  call exit

setCar:
  push rbp
  mov rbp, rsp
  
  push r8
  mov rax, PVAR(0) ; rax = Pair(a,b)
  cmp byte [rax], T_PAIR
  jne .fail
  mov r8, PVAR(1) ; r8 = new car
  mov [rax+1] , r8 ; rax+1 is car
  mov rax, SOB_VOID_ADDRESS ; set-car! prints nothing
  pop r8

  leave
  ret
  
   .fail:
  call write_fail_to_pair
  call exit

  setCdr:
  push rbp
  mov rbp, rsp
  
  push r8
  mov rax, PVAR(0) ; rax = Pair(a,b)
  cmp byte [rax], T_PAIR
  jne .fail
  mov r8, PVAR(1) ; r8 = new cdr
  mov [rax+9] , r8 ; rax+9 is cdr
  mov rax, SOB_VOID_ADDRESS ; set-cdr! prints nothing
  pop r8

  leave
  ret

 .fail:
  call write_fail_to_pair
  call exit
  
  
apply:
;r8 = will be used as param_count and counter for copying rest_args
;r9 = at extract_list address of the list that will be split and pushed, at fix_stack will be the increasing counter
;r10 = at extract_list will only hold the car, at fix_stack will be used to swap
;r11 = at fix_stack will be used to swap
;r12 = will be the new amount of args that will be pushed (increasing with every push of arg)
;at overriding the stack, it is the same as ApplicTP
  push rbp
  mov rbp,rsp

  push SOB_NIL_ADDRESS ; pushing magic
  xor rcx, rcx
  xor r12, r12
  mov r8, PARAM_COUNT
  dec r8
  mov r9, [rbp + 8 * (4 + r8)] ; r9 holds the pair

.extract_list:
  cmp byte [r9], T_PAIR
  je .push_car
  cmp r9, SOB_NIL_ADDRESS
  je .set_to_fix_stack
  jmp .fail

.push_car:
  CAR r10, r9
  push r10
  CDR r9, r9
  inc rcx
  inc r12
  jmp .extract_list

.set_to_fix_stack:
  dec rcx
  xor r9, r9

.fix_stack:
  cmp rcx, r9
  jle .set_push_rest_args
  mov r10, [rsp + 8 * r9]
  mov r11, [rsp + 8 * rcx]
  mov [rsp + 8 * r9] , r11
  mov [rsp + 8 * rcx] , r10
  dec rcx
  inc r9
  jmp .fix_stack

.set_push_rest_args:
  dec r8

.push_rest_args:
  cmp r8, 0
  je .finish_setup
  push qword [rbp + 8 * (4 + r8)]
  inc r12
  dec r8
  jmp .push_rest_args

.finish_setup:
  push r12
  mov rax, [rbp + 8 * 4] ; arg0 is the closure we are going to activate
  cmp byte [rax], T_CLOSURE
  jne .fail
  CLOSURE_ENV r8, rax
  push r8
  push qword [rbp + 8 * 1]

.override_stack:
  ;overriding the stack
  mov r15, [rbp]
  mov r9, qword [rbp + 8 * 3] ; r9 = number of args in overridden frame
  add r9, 4 ; r9 = entire size of overridden frame
  mov r10, [rsp + 8 * 2] ; r10 = number of args in overiding frame
  add r10, 3 ; r10 = entire size of overriding frame (no rbp in stack, so size is one less then r9

.copy_frame:
  cmp r10, 0
  jl .fix_rsp_rbp
  mov r11, [rsp + 8 * r10] ; copy from new frame
  mov [rbp + 8 * r9] , r11 ; copy to old frame
  dec r10
  dec r9
  jmp .copy_frame

.fix_rsp_rbp:
  inc r9 ; need to restore rsp
  shl r9, 3 ; mul by 8
  add r9, rbp
  mov rsp, r9 ;fixing rsp
  mov rbp, r15
  ;end of overiding the stack

.jmp_to_fuction:
  CLOSURE_CODE rax, rax ; rax = the closure's code address
  jmp rax ; jmping (not calling) to the code

.fail:
  call write_fail_to_apply_prim
  call exit\n"



  


let file_to_string f =
  let ic = open_in f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s;;

let string_to_asts s = List.map Semantics.run_semantics
                         (Tag_Parser.tag_parse_expressions
                            (Reader.read_sexprs s));;

let primitive_names_to_labels = 
   ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
   "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
   "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
   "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
   "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
   "make-vector", "make_vector"; "symbol->string", "symbol_to_string"; 
   "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
   "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ"; "cons", "cons";
   "car" , "car" ; "cdr", "cdr" ; "set-car!" , "setCar" ; "set-cdr!" , "setCdr";
   "apply", "apply"];;

let make_prologue consts_tbl fvars_tbl =
  let get_const_address const = handle_get_const_address const consts_tbl in 
  let get_fvar_address const = handle_get_freeVar_address const fvars_tbl in
  let make_primitive_closure (prim, label) =
"    MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, " ^ label  ^ ")
    mov [" ^ (get_fvar_address prim)  ^ "], rax" in
  let make_constant (c, (a, s)) = s in

"
;;; All the macros and the scheme-object printing procedure
;;; are defined in compiler.s
%include \"compiler.s\"

section .bss
malloc_pointer:
    resq 1

section .data
const_tbl:
" ^ (String.concat "\n" (List.map make_constant consts_tbl)) ^ "

;;; These macro definitions are required for the primitive
;;; definitions in the epilogue to work properly
%define SOB_VOID_ADDRESS " ^ get_const_address Void ^ "
%define SOB_NIL_ADDRESS " ^ get_const_address (Sexpr Nil) ^ "
%define SOB_FALSE_ADDRESS " ^ get_const_address (Sexpr (Bool false)) ^ "
%define SOB_TRUE_ADDRESS " ^ get_const_address (Sexpr (Bool true)) ^ "

fvar_tbl:
" ^ (String.concat "\n" (List.map (fun (x,i) -> (Printf.sprintf "dq T_UNDEFINED ; freeVar %s with offset %d * WORD_SIZE" x (i))) fvars_tbl)) ^ "
global main
section .text
main:
    ;; set up the heap
    mov rdi, GB(4)
    call malloc
    mov [malloc_pointer], rax

    ;; Set up the dummy activation frame
    ;; The dummy return address is T_UNDEFINED
    ;; (which a is a macro for 0) so that returning
    ;; from the top level (which SHOULD NOT HAPPEN
    ;; AND IS A BUG) will cause a segfault.
    push rbp
    push qword SOB_NIL_ADDRESS ; magic
    push 0
    push qword SOB_NIL_ADDRESS 
    push qword T_UNDEFINED
    push rsp
    mov rbp, rsp ;maybe will need to remove, this is my own addition
    call code_fragment
    add rsp, 4*8
    pop rbp
    ret
code_fragment:
    ;; Set up the primitive stdlib fvars:
    ;; Since the primtive procedures are defined in assembly,
    ;; they are not generated by scheme (define ...) expressions.
    ;; This is where we emulate the missing (define ...) expressions
    ;; for all the primitive procedures.
    
" ^  (String.concat "\n" (List.map make_primitive_closure primitive_names_to_labels)) ^ 
"
stdlib:\n";;

let epilogue =  makeMyPrims;;

exception X_missing_input_file;;

let constTest = 
  let asts = string_to_asts "(apply (lambda (x) x) '(3))" in
  let consts_tbl = Code_Gen.make_consts_tbl asts in
  asts;;



try
  let infile = Sys.argv.(1) in
  let code = (file_to_string "stdlib.scm") ^(file_to_string infile) in
  let asts = string_to_asts code in
  let consts_tbl = Code_Gen.make_consts_tbl asts in
  let fvars_tbl = Code_Gen.make_fvars_tbl asts in
  let generate = Code_Gen.generate consts_tbl fvars_tbl 0 in
  let code_fragment = String.concat "\n\n"
                        (List.map
                           (fun ast -> (generate ast) ^ "\n    call write_sob_if_not_void")
                           asts) in
  let provided_primitives = file_to_string "prims.s" in
                   
  print_string ((make_prologue consts_tbl fvars_tbl)  ^
                  code_fragment ^ "\n ret\n\n;primitive functions:\n" ^
                    provided_primitives ^ "\n" ^ epilogue)

with Invalid_argument(x) -> raise X_missing_input_file;;

