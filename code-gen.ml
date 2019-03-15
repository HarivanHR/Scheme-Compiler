#use "semantic-analyser.ml";;

exception X_not_suppose_to_happen;;
exception X_failed_to_find_Var;;

let rec make_set lst = match lst with
| [] -> []
| h::t -> h::(make_set(List.filter (fun (x) -> x<>h) t));;  

let lengthCalc const = match const with
| Void -> 1
| Sexpr(Nil) -> 1
| Sexpr(Bool(x)) -> 2
| Sexpr(Char(x)) -> 2
| Sexpr(Number(_)) -> 9
| Sexpr(String(x)) -> 9 + (String.length x)
| Sexpr(Symbol(x)) -> 9
| Sexpr(Pair (x,y)) -> 17
| Sexpr(Vector(lst)) -> 9 + (8 * (List.length lst))

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) ((string_of_int (Char.code s.[i])) :: l) in
  exp (String.length s - 1) []

let stringMaker const tbl i= match const with  
| Void -> "MAKE_VOID ;offset 0"
| Sexpr(Nil) -> "MAKE_NIL ;offset 1"
| Sexpr(Bool(false)) -> "MAKE_BOOL(0) ;offset 2"
| Sexpr(Bool(true)) -> "MAKE_BOOL(1) ;offset 4"
| Sexpr(Char(x)) -> Printf.sprintf "MAKE_LITERAL_CHAR(%d) ;offset %d"  (Char.code x) i
| Sexpr(Number(Int(x))) -> Printf.sprintf "MAKE_LITERAL_INT(%d)   ;offset %d"  x i
| Sexpr(Number(Float(x))) -> Printf.sprintf "MAKE_LITERAL_FLOAT(%f)  ;offset %d"  x i
| Sexpr(String(x)) -> Printf.sprintf "MAKE_LITERAL_STRING %s ;offset %d" (String.concat " , " (explode x)) i
| Sexpr(Symbol(x)) -> 
    let xAssoc = List.assoc (Sexpr(String(x))) tbl in 
    let xOffset = (match xAssoc with
      |(i, s) -> i) in
      Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl+%d) ;offset %d" xOffset i
| Sexpr(Pair (car,cdr)) -> 
    let carAssoc = List.assoc (Sexpr(car)) tbl in 
    let carOffset = (match carAssoc with
      |(i, s) -> i) in
    let cdrAssoc = List.assoc (Sexpr(cdr)) tbl in
    let cdrOffset = (match cdrAssoc with
      |(i, s) -> i) in
    Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl+%d, const_tbl+%d) ;offset %d"  carOffset cdrOffset i 
| Sexpr(Vector(lst)) -> let str = "MAKE_LITERAL_VECTOR " ^ (String.concat "" (List.map (fun (x) ->
                                                                        let (i,_) = List.assoc (Sexpr(x)) tbl in
                                                                        Printf.sprintf "const_tbl+%d ," i) lst)) in
                        (String.sub str 0 ((String.length str)-1)) ^ "\n";; 


let rec update_index_for_const tbl acc originalTbl= (*TODO: try to change to make it use fold left and do this and next function together*)
    match tbl with
    | [] -> []
    | hd::tl -> (match hd with
                  | (e, (i,s)) -> (e,(acc,s)) :: update_index_for_const (List.tl tbl) (acc + (lengthCalc e)) originalTbl);;

let rec update_strings_for_const tbl originalTbl = 
match tbl with
    | [] -> []
    | hd::tl -> (match hd with
                  | (e, (i,s)) -> (e,(i,stringMaker e originalTbl i)) :: update_strings_for_const (List.tl tbl) originalTbl);;


let rec getShallowConstTbl e tbl = match e with

| Const'(se) -> tbl @ [(se,(0,""))]
| BoxSet'(_, x) -> getShallowConstTbl x tbl
| If'(t, th, el) ->
    let t_tbl = getShallowConstTbl t tbl in
      let th_tbl = getShallowConstTbl th t_tbl in
        getShallowConstTbl el th_tbl
| Seq'(eList) ->  
  let newList = List.fold_right getShallowConstTbl eList [] in
  tbl @ (List.rev newList)
| Set'(x, y) ->
    let xTbl = getShallowConstTbl x tbl in
      getShallowConstTbl y xTbl
| Def' (x, y) ->
    let xTbl = getShallowConstTbl x tbl in
      getShallowConstTbl y xTbl
| Or'(eList) ->  
  let newList = List.fold_right getShallowConstTbl eList [] in
  tbl @ (List.rev newList)
| LambdaSimple'(_, body) -> getShallowConstTbl body tbl
| LambdaOpt'(_,_, body) -> getShallowConstTbl body tbl
| Applic'(x,eList) ->
    let x_tbl = getShallowConstTbl x tbl in
    let newList = List.fold_right getShallowConstTbl eList [] in
    x_tbl @ (List.rev newList)
| ApplicTP'(x,eList) ->
    let x_tbl = getShallowConstTbl x tbl in
    let newList = List.fold_right getShallowConstTbl eList [] in
    x_tbl @ (List.rev newList)
| _ -> tbl;;

let rec extendConst const = match const with
|(Sexpr(Symbol x), (_,_)) -> [(Sexpr(String x),(0,"")); const]
|(Sexpr(Pair (car ,cdr)),(0,"")) -> (extendConst (Sexpr(car),(0,"")) @ extendConst (Sexpr(cdr),(0,""))) @ [const] 
|(Sexpr(Vector lst),(0,"")) -> 
  let tupleSubList = List.map (fun e -> (Sexpr(e),(0,""))) lst in
  let subList = List.map extendConst tupleSubList in
  let flattenList = List.flatten subList in
  flattenList @ [const]
| _-> [const];;


let rec getDeepConstTbl lst = match lst with
| [] -> []
| _ -> List.flatten (List.map extendConst lst);;


let rec isFreeVarExist v tbl = 
  if ((List.mem v tbl) = false) then (tbl @ [v]) else tbl;;

let rec getFreeVars e tbl= match e with  
| Const'(v) -> tbl
| Var'(v) -> (match v with
              |VarFree(x) -> isFreeVarExist x tbl
              | _ -> tbl)
| Box'(v) -> (match v with
              |VarFree(x) -> isFreeVarExist x tbl
              | _ -> tbl)
| BoxGet'(v) -> (match v with
              |VarFree(x) -> isFreeVarExist x tbl
              | _ -> tbl)
| BoxSet'(v,ex) ->
                let v_tbl =  (match v with
                          |VarFree(x) -> isFreeVarExist x tbl
                          | _ -> tbl) in
                getFreeVars ex v_tbl
| If'(t,th,el) -> 
                let t_tbl = getFreeVars t tbl in
                let th_tbl = getFreeVars th t_tbl in
                getFreeVars el th_tbl
| Seq'(eList) -> 
                let newList = List.fold_right getFreeVars eList [] in
                tbl @ (List.rev newList)
| Set'(x,y) -> 
                let x_tbl = getFreeVars x tbl in
                getFreeVars y x_tbl
| Def'(x,y) -> 
                let x_tbl = getFreeVars x tbl in
                getFreeVars y x_tbl
| Or'(eList) -> 
                let newList = List.fold_right getFreeVars eList [] in
                tbl @ (List.rev newList)
| LambdaSimple'(_, body) -> getFreeVars body tbl
| LambdaOpt'(_,_, body) -> getFreeVars body tbl
| Applic'(x,eList) ->
                let x_tbl = getFreeVars x tbl in
                let newList = List.fold_right getFreeVars eList [] in
                x_tbl @(List.rev newList)
| ApplicTP'(x,eList) ->
                let x_tbl = getFreeVars x tbl in
                let newList = List.fold_right getFreeVars eList [] in
                x_tbl @(List.rev newList);;

let rec update_index_for_freeVar tbl acc = match tbl with
| [] -> []
| hd::tl -> (hd,acc) :: update_index_for_freeVar (List.tl tbl) (acc+1);;


let rec getConstAddress const const_tbl = 
let (i,s) = List.assoc const const_tbl in
i;;

let rec getFvarAddress fvarString fvar_tbl =
List.assoc fvarString fvar_tbl;;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * (int * string)) list 
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * (int * string)) list -> (string * int) list -> int -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

let make_big_const_table ast = 
let shallow_tbl = getShallowConstTbl ast [(Void,(0,"")) ; (Sexpr(Nil),(0,"")) ; (Sexpr(Bool false),(0,"")); (Sexpr(Bool true),(0,""))] in 
getDeepConstTbl shallow_tbl;;



let make_consts_tbl asts =
let deep_tbl = List.flatten (List.map make_big_const_table asts) in
let deep_set = make_set deep_tbl in
let updated_tbl_with_index = update_index_for_const deep_set 0 deep_set in
update_strings_for_const updated_tbl_with_index updated_tbl_with_index;;

let make_big_fvar_table ast = 
getFreeVars ast ["boolean?"; "float?"; "integer?"; "pair?";
                          "null?"; "char?"; "vector?"; "string?";
                          "procedure?"; "symbol?"; "string-length";
                          "string-ref"; "string-set!"; "make-string";
                          "vector-length"; "vector-ref"; "vector-set!";
                          "make-vector"; "symbol->string"; 
                          "char->integer"; "integer->char"; "eq?";
                          "+"; "*"; "-"; "/"; "<"; "=";"cons"; "car" ; "cdr" ; "set-car!" ;
                          "set-cdr!"; "apply"];;


  let make_fvars_tbl asts =
   let freeVarList = List.flatten (List.map make_big_fvar_table asts)  in
   let freeVarSet = make_set freeVarList in
    update_index_for_freeVar freeVarSet 0;;

  let labelCount = ref (-1);;
  let labelMaker s toIncrease =  (*we will want to increase only in the first time of using a label per sexpr*)
    if (toIncrease = true)
    then (labelCount:= !labelCount + 1;
                 Printf.sprintf "L_%s%d" s (!labelCount))
    else (Printf.sprintf "L_%s%d" s !labelCount);;

  

  let rec generate consts fvars envSize e  = match e with
  | Const'(v) -> Printf.sprintf "mov rax, const_tbl+%d ;getting a constant\n" (getConstAddress v consts)
  | Var'(v) -> (match v with
                | VarFree(x) -> Printf.sprintf "mov rax, qword [fvar_tbl+%d * WORD_SIZE] ;getting free var %s\n" (getFvarAddress x fvars) x
                | VarParam(x,i) -> Printf.sprintf "mov rax, qword [rbp + 8 * (4+%d)] ;getting param %s \n" i x
                | VarBound(x,major,minor) -> "mov rax, qword [rbp + 8 * 2]   ;getting lexical env\n"
                                             ^ (Printf.sprintf "mov rax, qword [rax + 8 * %d]  ;getting major index for var: %s\n" major x)
                                             ^ (Printf.sprintf "mov rax, qword [rax + 8 * %d]  ;getting minor index for var: %s\n" minor x)) 
  | Box'(v) ->
  (generate consts fvars envSize (Var'(v))) ^ 
  "push rax ; box' only shows after (set! x (box x)) so rax holds pointed to x. we push to hold the address
  MALLOC rax, 8
  pop qword [rax] ; we will put the address of x into the address of the box\n"
  | BoxGet'(v) -> (generate consts fvars envSize (Var'(v)) ) ^ (Printf.sprintf "mov rax, qword [rax] ;make [var] be var\n")
  | BoxSet'(v,ex) -> (generate consts fvars envSize ex) ^ (Printf.sprintf "push rax\n") ^ 
                      (generate consts fvars envSize (Var'(v))) ^ (Printf.sprintf "pop qword [rax]\n") ^
                      ("mov rax, SOB_VOID_ADDRESS\n")
  | If'(t,th,el) -> 
      let elseLabel = labelMaker "else" true in
      let exitLabel = labelMaker "exit" false in
      (generate consts fvars envSize t) ^ "cmp rax, SOB_FALSE_ADDRESS ;comparing rax to false\n" ^   (*the const_tbl+2 is diffrent from the lecture*)
      (Printf.sprintf "je %s\n" elseLabel) ^ (generate consts fvars envSize th) ^ 
      (Printf.sprintf "jmp %s\n" exitLabel) ^ (Printf.sprintf "%s:" elseLabel) ^ "\n" ^
      (generate consts fvars envSize el)  ^ (Printf.sprintf "%s:" exitLabel) ^ "\n"
  | Seq'(eList) -> (String.concat "\n" (List.map (fun (e) -> generate consts fvars envSize e) eList))
  | Set'(x,y) ->(match x with
                | Var'(VarFree(x)) -> (generate consts fvars envSize y) ^ 
                                      (Printf.sprintf "mov qword [fvar_tbl+%d * WORD_SIZE], rax ;putting new value to var %s\n" (getFvarAddress x fvars) x) ^
                                      "mov rax, SOB_VOID_ADDRESS ;Value of \"set!\" is void and we dont print\n"

                | Var'(VarParam(x,i)) -> (generate consts fvars envSize y) ^
                                   (Printf.sprintf "mov qword [rbp + 8 * (4+%d)], rax ;getting param\n" i) ^
                                   (Printf.sprintf "mov rax, SOB_VOID_ADDRESS ;putting void in rax\n")
                | Var'(VarBound(x,major,minor)) -> (generate consts fvars envSize y) ^ "mov rbx, qword [rbp + 8 * 2] ;getting lexical env\n"
                                                    ^ (Printf.sprintf "mov rbx, qword [rbx + 8 * %d]  ;getting major index for var: %s\n" major x)
                                                    ^ (Printf.sprintf "mov qword [rbx + 8 * %d], rax  ;setting the var %s to the new value\n" minor x)
                                                    ^ "mov rax, SOB_VOID_ADDRESS ;Value of \"set!\" is void and we dont print\n"
                | _ -> raise X_not_suppose_to_happen)
  | Def'(x,y) -> (match x with
                | Var'(VarFree(x)) -> (generate consts fvars envSize y) ^ 
                                      (Printf.sprintf "mov qword [fvar_tbl+%d * WORD_SIZE], rax ;putting new value to var %s\n" (getFvarAddress x fvars) x) ^
                                      "mov rax, SOB_VOID_ADDRESS ;Value of \"set!\" is void and we dont print\n"
                | _ -> raise X_not_suppose_to_happen)
  | Or'(eList) -> 
      let exitLabel = labelMaker "exit" true in
      (String.concat "" (List.map (fun (e) -> (Printf.sprintf "%s" (generate consts fvars envSize e))
      ^ "cmp rax, SOB_FALSE_ADDRESS ; comparing rax to false\n"
      ^ (Printf.sprintf "jne %s\n"  (exitLabel))) eList)) ^ (Printf.sprintf "%s:\n" exitLabel)
                                                            
  | LambdaSimple'(_, body) -> generate_lambda_simple consts fvars envSize body;
  | LambdaOpt'(paramList,_, body) -> generate_lambda_opt consts fvars envSize paramList body;
  | Applic'(x,eList) -> generate_applic consts fvars envSize x (List.rev eList)
  | ApplicTP'(x,eList) -> generate_applicTP consts fvars envSize x (List.rev eList)
  

  and generate_lambda_simple consts fvars envSize body  = 
    let copyRibsLabel = labelMaker "copyRibs" true in
    let copyArgsLabel = labelMaker "copyArgs" false in
    let closureLabel = labelMaker "makeClosure" false in
    let codeLabel = labelMaker "code" false in
    let contLabel = labelMaker "cont" false in
  "push rcx
  push r8
  push r9
  push r10
  push r11
  push r12
  push r13
  mov r8, [rbp + 8*3] ; r8 = Number of arguments that will be copied
  inc r8
  mov r9, [rbp + 8*2] ; r9 = address of old envioronment\n" ^
  (Printf.sprintf "mov rcx, (%d-1) ;rcx = oldEnvSize-1\n" envSize) ^
  (Printf.sprintf "MALLOC r10, (8+%d*8) ; r10 = address of extended enviornment\n" envSize) ^
  "shl r8, 3 ; mul by 8 for malloc
  MALLOC r11, r8 ; r11 = address of NewEnv[0]\n" ^
  "shr r8, 3 ; return to original size
  dec r8 ; starting from n-1 instead of n\n" ^
  (Printf.sprintf "%s:\n" copyRibsLabel) ^
  "cmp rcx, 0 ; checks whether we finished copying ribs\n" ^
  (Printf.sprintf "jl %s ; go to copyArgs if done copying ribs\n" copyArgsLabel) ^
  "; next 4 lines copy the rib pointer from oldEnv[rcx] to newEnv[rcx+1]
  mov r12, [r9 + 8 * rcx] ; r12 = oldEnv[rcx]
  inc rcx
  mov [r10 + 8 * rcx], r12 ; newEnv[rcx] = r12
  sub rcx, 2\n" ^
  (Printf.sprintf "jmp %s ; doing ribs loop again\n" copyRibsLabel) ^
  (Printf.sprintf "%s:\n" copyArgsLabel) ^
  "cmp r8, 0 ; checks whether we finished copying args from stack to newEnv[0]\n" ^
  (Printf.sprintf "jl %s ; if done, go create closure\n" closureLabel) ^
  "mov r13, [rbp + 8 * (4 + r8)] ; r13 = Arg_n-1
  mov [r11 + 8 * r8], r13 ; newEnv[0][n] = r13 = Arg_n
  dec r8\n" ^
  (Printf.sprintf "jmp %s ; doing args loop again\n" copyArgsLabel) ^
  (Printf.sprintf "%s:\n" closureLabel) ^
  "mov [r10], r11 ; connect the env[0] to env\n" ^
  (Printf.sprintf "MAKE_CLOSURE(rax, r10, %s) ; making the closure. r10 hold newEnv and putting label\n" codeLabel) ^
  (Printf.sprintf "jmp %s\n" contLabel) ^
  (Printf.sprintf "%s:\n" codeLabel) ^
  "push rbp
  mov rbp, rsp\n" ^
  (generate consts fvars (envSize+1) body) ^
  "leave
  ret\n" ^
  (Printf.sprintf "%s:\n" contLabel) ^ 
  "
  pop r13
  pop r12
  pop r11
  pop r10
  pop r9
  pop r8
  pop rcx\n\n\n"


  and generate_applic consts fvars envSize fName revArgs =
  let postFailLabel = labelMaker "postFail" true in
  let failLabel = labelMaker "failed" false in
  "push r8\n" ^
  "push qword SOB_NIL_ADDRESS\n" ^
  (String.concat "" (List.map (fun (arg) -> (generate consts fvars envSize arg) ^
                                           "push rax\n") revArgs)) ^
  (Printf.sprintf "push %d\n" (List.length revArgs)) ^
   (generate consts fvars envSize fName) ^
   "cmp byte [rax], T_CLOSURE ; checks whether fName is a closure\n" ^
   (Printf.sprintf "jne %s\n" failLabel) ^
   "CLOSURE_ENV r8, rax ; r8 = The env of the closure\n" ^
   "push r8\n" ^
   "CLOSURE_CODE rax, rax ; rax = the closure's code address\n" ^
   "call rax ; calling for applic\n" ^
   "add rsp, 8*1 ; skipping over env
   pop rbx ; pop arg count
   shl rbx, 3 ; making rbx to be WORD_SIZE*(arg count)
   add rsp, rbx
   add rsp, 8 ; going above the magic parameter
   pop r8\n" ^
   (Printf.sprintf "jmp %s\n" postFailLabel) ^
   (Printf.sprintf "%s:\n" failLabel) ^
  "call write_fail_to_apply
  call exit\n"^
   (Printf.sprintf "%s:\n\n" postFailLabel)


   and generate_applicTP consts fvars envSize fName revArgs = 
  let failLabel = labelMaker "failed" true in
  let copyFrameLabel = labelMaker "copy_frame" false in
  let restoreRspRbp = labelMaker "restore_rsp" false in
  "push qword SOB_NIL_ADDRESS\n" ^
  (String.concat "" (List.map (fun (arg) -> (generate consts fvars envSize arg) ^
                                           "push rax\n") revArgs)) ^
  (Printf.sprintf "push %d\n" (List.length revArgs)) ^
   (generate consts fvars envSize fName) ^
   "cmp byte [rax], T_CLOSURE ; checks whether fName is a closure\n" ^
   (Printf.sprintf "jne %s\n" failLabel) ^
   "CLOSURE_ENV r8, rax ; r8 = The env of the closure\n" ^
   "push r8\n" ^
   "push qword [rbp + 8 * 1] ; pushing old ret address\n" ^
   ";fixing the stack\n" ^
   "mov r15, [rbp]
   mov r9, qword [rbp + 8 * 3] ; r9 = number of args in overridden frame
   add r9, 4 ; r9 = entire size of overridden frame\n" ^
   "mov r10, [rsp + 8 * 2] ; r10 = number of args in overiding frame
   add r10, 3 ; r10 = entire size of overriding frame (no rbp in stack, so size is one less then r9\n" ^
   (Printf.sprintf "%s:\n" copyFrameLabel) ^
   "cmp r10, 0\n" ^
   (Printf.sprintf "jl %s\n" restoreRspRbp) ^
   "mov r11, [rsp + 8 * r10] ; copy from new frame
   mov [rbp + 8 * r9] , r11 ; copy to old frame
   dec r10
   dec r9\n" ^
   (Printf.sprintf "jmp %s\n" copyFrameLabel) ^
   (Printf.sprintf "%s:\n" restoreRspRbp) ^
   "inc r9 ; need to restore rsp
   shl r9, 3 ; mul by 8
   add r9, rbp
   mov rsp, r9 ;fixing rsp
   mov rbp, r15\n" ^
   ";end of fixing the stack\n" ^
   "CLOSURE_CODE rax, rax ; rax = the closure's code address\n" ^
   "jmp rax ; jmping (not calling) to the code\n" ^
   (Printf.sprintf "%s:\n" failLabel) ^
  "call write_fail_to_apply
  call exit\n"


  and generate_lambda_opt consts fvars envSize paramList body = 
    let copyRibsLabel = labelMaker "copyRibs" true in
    let copyArgsLabel = labelMaker "copyArgs" false in
    let closureLabel = labelMaker "makeClosure" false in
    let codeLabel = labelMaker "code" false in
    let contLabel = labelMaker "cont" false in
    let makeListLabel = labelMaker "makeList" false in
    let endOfMakeListLabel = labelMaker "endOfMakeList" false in
    "push rcx
  push r8
  push r9
  push r10
  push r11
  push r12
  push r13
  mov r8, [rbp + 8*3] ; r8 = Number of arguments that will be copied
  inc r8
  mov r9, [rbp + 8*2] ; r9 = address of old envioronment\n" ^
  (Printf.sprintf "mov rcx, (%d-1) ;rcx = oldEnvSize\n" envSize) ^
  (Printf.sprintf "MALLOC r10, (8+%d*8) ; r10 = address of extended enviornment\n" envSize) ^
  "shl r8, 3 ; mul by 8 for malloc
  MALLOC r11, r8 ; r11 = address of NewEnv[0]\n" ^
  "shr r8, 3 ; return to original size
  dec r8 ; starting from n-1 instead of n\n" ^
  (Printf.sprintf "%s:\n" copyRibsLabel) ^
  "cmp rcx, 0 ; checks whether we finished copying ribs\n" ^
  (Printf.sprintf "jl %s ; go to copyArgs if done copying ribs\n" copyArgsLabel) ^
  "; next 4 lines copy the rib pointer from oldEnv[rcx] to newEnv[rcx+1]
  mov r12, [r9 + 8 * rcx] ; r12 = oldEnv[rcx]
  inc rcx
  mov [r10 + 8 * rcx], r12 ; newEnv[rcx] = r12
  sub rcx, 2\n" ^
  (Printf.sprintf "jmp %s ; doing ribs loop again\n" copyRibsLabel) ^
  (Printf.sprintf "%s:\n" copyArgsLabel) ^
  "cmp r8, 0 ; checks whether we finished copying args from stack to newEnv[0]\n" ^
  (Printf.sprintf "jl %s ; if done, go create closure\n" closureLabel) ^
  "mov r13, [rbp + 8 * (4 + r8)] ; r13 = Arg_n-1
  mov [r11 + 8 * r8], r13 ; newEnv[0][n] = r13 = Arg_n
  dec r8\n" ^
  (Printf.sprintf "jmp %s ; doing args loop again\n" copyArgsLabel) ^
  (Printf.sprintf "%s:\n" closureLabel) ^
  "mov [r10], r11 ; connect the env[0] to env\n" ^
  (Printf.sprintf "MAKE_CLOSURE(rax, r10, %s) ; making the closure. r10 hold newEnv and putting label\n" codeLabel) ^
  (Printf.sprintf "jmp %s\n" contLabel) ^
  (Printf.sprintf "%s:\n" codeLabel) ^
  "push rbp
  mov rbp, rsp\n" ^
  "push r9 ; backing up registers
  push r10
  push r11
  push r12
  push r13
  push r14
  mov r14, SOB_NIL_ADDRESS\n" ^
  (Printf.sprintf "mov r9, %d ;putting the length of original parameter list without vs\n" (List.length paramList)) ^
  "mov r10, PARAM_COUNT
  mov r11, r10\n" ^
  (Printf.sprintf "%s:\n" makeListLabel) ^
  "cmp r9, r11\n" ^
  (Printf.sprintf "je %s\n" endOfMakeListLabel) ^
  "mov r12, [rbp + 8 * (4 + r10)]
  dec r11
  mov r13, [rbp + 8 * (4 + r11)]
  MAKE_PAIR(r14, r13,r12)
  mov [rbp + 8 * (4 + r10)], r14\n" ^
  (Printf.sprintf "jmp %s\n" makeListLabel) ^
  (Printf.sprintf "%s:\n" endOfMakeListLabel) ^
  "mov [rbp + 8 * (4 + r9)], r14\n" ^
  (generate consts fvars (envSize+1) body) ^
  "pop r14
  pop r13
  pop r12
  pop r11
  pop r10
  pop r9\n" ^
  "leave
  ret\n" ^
  (Printf.sprintf "%s:\n" contLabel) ^ 
  "
  pop r13
  pop r12
  pop r11
  pop r10
  pop r9
  pop r8
  pop rcx\n\n\n"


   
end;;





