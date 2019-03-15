(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "tag-parser.ml";;

 type var = 
   | VarFree of string
   | VarParam of string * int
   | VarBound of string * int * int;;
 
 type expr' =
   | Const' of constant
   | Var' of var
   | Box' of var
   | BoxGet' of var
   | BoxSet' of var * expr'
   | If' of expr' * expr' * expr'
   | Seq' of expr' list
   | Set' of expr' * expr'
   | Def' of expr' * expr'
   | Or' of expr' list
   | LambdaSimple' of string list * expr'
   | LambdaOpt' of string list * string * expr'
   | Applic' of expr' * (expr' list)
   | ApplicTP' of expr' * (expr' list);;
 
 let rec expr'_eq e1 e2 =
   match e1, e2 with
   | Const' Void, Const' Void -> true
   | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
   | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
   | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
   | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
   | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                             (expr'_eq th1 th2) &&
                                               (expr'_eq el1 el2)
   | (Seq'(l1), Seq'(l2)
   | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
   | (Set'(var1, val1), Set'(var2, val2)
   | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                              (expr'_eq val1 val2)
   | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
      (List.for_all2 String.equal vars1 vars2) &&
        (expr'_eq body1 body2)
   | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
      (String.equal var1 var2) &&
        (List.for_all2 String.equal vars1 vars2) &&
          (expr'_eq body1 body2)
   | Applic'(e1, args1), Applic'(e2, args2)
   | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
    (expr'_eq e1 e2) &&
      (List.for_all2 expr'_eq args1 args2)
   | _ -> false;;
   
                        
 exception X_syntax_error;;
 
 module type SEMANTICS = sig
   val run_semantics : expr -> expr'
   val annotate_lexical_addresses : expr -> expr'
   val annotate_tail_calls : expr' -> expr'
   val box_set : expr' -> expr'
 end;;
 
 module Semantics : SEMANTICS = struct
 
 
   let rec get_index name row =
      if (List.hd row = name) then 0
      else 1 + (get_index name (List.tl row));;

 let rec var_decider name depth table = 
  if (List.length table = 0) then VarFree(name)
  else
  let row = List.hd table in
  if (List.mem name row) then
   (let index = get_index name row  in
      if(depth = -1) then VarParam(name, index)
      else VarBound(name, depth, index))
  else (var_decider name (depth+1) (List.tl table));;
 
 
 
 
 let rec tagging e lexicalTable =
     match e with
       | Const(x) -> Const'(x)
       | Var(x) -> Var'( (var_decider x (-1) lexicalTable) )
       | If(test, th , el) -> If' ( (tagging test lexicalTable), (tagging th lexicalTable), (tagging el lexicalTable))
       | Seq(exprList) -> Seq'(List.map (fun (element) -> (tagging element lexicalTable)) exprList)
       | Set(x, y) -> Set'((tagging x lexicalTable), (tagging y lexicalTable))
       | Def(x,y) -> Def'((tagging x lexicalTable),(tagging y lexicalTable)) 
       | Or(exprList) -> Or'(List.map (fun (element) -> (tagging element lexicalTable)) exprList)
       | LambdaSimple(stringList, body) -> LambdaSimple'(stringList, (tagging body (stringList :: lexicalTable)))
       | LambdaOpt(stringList, extra, body) -> 
           let combined = List.append stringList [extra] in
           LambdaOpt'(stringList, extra, (tagging body (combined :: lexicalTable)))
       | Applic(name, params) -> Applic' ((tagging name lexicalTable), List.map (fun (element) -> (tagging element lexicalTable)) params );;
 
 
       
 
 let annotate_lexical_addresses e = 
        tagging e [];;
 
 let rec isLast e myList =
     let lastElement = List.nth myList ((List.length myList) -1)  in
     if (e = lastElement) then true else false;;
 
 let rec tailing e isTP = match e with
       | Const'(x) -> Const'(x)
       | Var'(x) -> Var'(x)
       | If'(test, th , el) -> If' ( (tailing test false), (tailing th isTP), (tailing el isTP))
       | Seq'(exprList) -> Seq'(List.map (fun (element) -> if (isLast element exprList)
                                                          then (tailing element isTP) else (tailing element false)) exprList) 
       | Set'(x, y) -> Set'((tailing x false), (tailing y false))
       | Def'(x,y) -> Def'((tailing x false),(tailing y false)) 
       | Or'(exprList) -> Or'(List.map (fun (element) -> if (isLast element exprList)
                                                          then (tailing element isTP) else (tailing element false)) exprList)
       | LambdaSimple'(stringList, body) -> LambdaSimple'(stringList, (tailing body true))
       | LambdaOpt'(stringList, extra, body) -> LambdaOpt'(stringList, extra, (tailing body true))
       | Applic'(name, params) -> if (isTP) then ApplicTP' ((tailing name false), List.map (fun (element) -> (tailing element false)) params)
                                          else Applic' ((tailing name false), List.map (fun (element) -> (tailing element false)) params)
       | _ -> raise X_syntax_error;;
 
 
 
 let annotate_tail_calls e = 
    tailing e false;;
 
 (** Start Box **)
 
 let varStringExtractor = function
 | VarFree(x) -> x
 | VarParam(x, _) -> x
 | VarBound (x,_,_) -> x;;
 
 (* Search for read and write, the return a list of: [0 = no operation, read = 1 , write = -1] *)
 let rec searchRW param e isSet isOutter = 
 match e with
   | Var'(x) -> 
                 let varString = (varStringExtractor x) in
                 if( varString = param ) then
                     ( if(isSet = 0) then [1] else [-1] )
                 else [0];
                 
   | Set'(x, y) -> let list_of_x = (searchRW param x 1 isOutter) in
                   let list_of_y =  (searchRW param y 0 isOutter) in
                   (List.append list_of_x list_of_y)
 
   | BoxSet'(_, setTo) -> (searchRW param setTo 0 isOutter)
 
   | If'(_test_, _then_, _else_) -> let list_of_test = (searchRW param _test_ 0 isOutter) in 
                                    let list_of_then = (searchRW param _then_ 0 isOutter) in 
                                    let list_of_else = (searchRW param _else_ 0 isOutter) in
                                    let appended = List.append  list_of_test list_of_then  in
                                    (List.append appended list_of_else)
 
   | Seq' (exprList) -> let list_of_exprList = List.map (fun expr' -> (searchRW param expr' 0 isOutter)) exprList in
                         (List.concat list_of_exprList)
 
   | Or' (exprList) -> let list_of_exprList = List.map (fun expr' -> (searchRW param expr' 0 isOutter)) exprList in
                         (List.concat list_of_exprList)
 
   | LambdaSimple' (stringList, body) -> if( isOutter = 1 || (List.mem param stringList)) then [] else (searchRW param body 0 isOutter)
 
   | LambdaOpt' (stringList,var,body) -> if( isOutter = 1 || (List.mem param stringList) ||  param = var) then [] else (searchRW param body 0 isOutter)
 
   | Applic' (var, exprList) -> let list_of_var = (searchRW param var 0 isOutter) in
                                let list_of_exprList = List.map (fun expr' -> (searchRW param expr' 0 isOutter)) exprList in
                                let combined_list = list_of_var :: list_of_exprList in
                                (List.concat combined_list)
 
   | ApplicTP' (var, exprList) -> let list_of_var = (searchRW param var 0 isOutter) in
                                  let list_of_exprList = List.map (fun expr' -> (searchRW param expr' 0 isOutter)) exprList in
                                  let combined_list = list_of_var :: list_of_exprList in
                                  (List.concat combined_list)
 
   | Def'(x,y)  -> let list_of_x = (searchRW param x 1 isOutter) in
                   let list_of_y = (searchRW param y 0 isOutter) in
                   (List.append list_of_x list_of_y)
 
   | _ -> [];;
 
 (* Search for lambdas, return : [[0 = no operation, read = 1 , write = -1]] *)
 let rec searchLambda param e lambdaTable=
 match e with
 | Set'(x, y) -> let list_of_x = (searchLambda param x lambdaTable) in
                 let list_of_y = (searchLambda param y lambdaTable) in
                 (List.append list_of_x list_of_y)
                 
 | BoxSet'(_, setTo) -> (searchLambda param setTo lambdaTable)
 
 | If'(_test_, _then_, _else_) -> let list_of_test = (searchLambda param _test_ lambdaTable) in 
                                  let list_of_then = (searchLambda param _then_ lambdaTable) in 
                                  let list_of_else = (searchLambda param _else_ lambdaTable) in
                                  let appended = List.append  list_of_test list_of_then  in
                                  (List.append appended list_of_else)
 
 | Seq' (exprList) -> let list_of_exprList = List.map (fun expr' -> (searchLambda param expr' lambdaTable)) exprList in
                     (List.concat list_of_exprList)
 
 | Or' (exprList) -> let list_of_exprList = List.map (fun expr' -> (searchLambda param expr' lambdaTable)) exprList in
                     (List.concat list_of_exprList)
 
 | Applic' (var, exprList) -> let list_of_var = (searchLambda param var lambdaTable) in
                              let list_of_exprList = List.map (fun expr' -> (searchLambda param expr' lambdaTable)) exprList in
                              let combined_list = list_of_var :: list_of_exprList in
                              (List.concat combined_list)
 
 | ApplicTP' (var, exprList) -> let list_of_var = (searchLambda param var lambdaTable) in
                                let list_of_exprList = List.map (fun expr' -> (searchLambda param expr' lambdaTable)) exprList in
                                let combined_list = list_of_var :: list_of_exprList in
                                (List.concat combined_list)
                     
 | Def'(x,y)  -> let list_of_x = (searchLambda param x lambdaTable) in
                 let list_of_y = (searchLambda param y lambdaTable) in
                 (List.append list_of_x list_of_y)
 
 | LambdaSimple' (stringList , body) -> if (List.mem param stringList) then lambdaTable else ( (searchRW param body 0 0) :: lambdaTable )
 
 | LambdaOpt' (_ , _ , body) -> ( (searchRW param body 0 0) :: lambdaTable )
 
 | _ -> [];;
 
 
 let rec handle_seq param body index_of_param ls =
  let head = List.hd ls in
  let to_set = Set'( Var'( (VarParam(param, index_of_param)) ), Box'( (VarParam(param, index_of_param))) ) in
  match head with
  | Set'(v , b) ->  
                  (match b with
                  | Box'(_) ->  to_set :: ls
                  | e -> to_set :: [Seq'(ls)] )
  | e ->  to_set :: [Seq'(ls)]

 let rec box_tagging_stage_1 param body index_of_param = 
   match body with
     | Seq'(exprList) -> Seq'((handle_seq param body index_of_param exprList))
     | e -> Seq'( (Set'( Var'( (VarParam(param, index_of_param)) ), Box'( (VarParam(param, index_of_param))) ))  :: [e]  );;
 
 let rec box_tagging_getNSet param e =
   match e with
   | Var'(x) -> let varString = (varStringExtractor x) in
                if( varString = param ) then  BoxGet' (x)
                else Var'(x)
   | Set'(x, y) -> ( match x with 
                     | Var'(s) -> ( let varString = (varStringExtractor s) in
                                   if( varString = param ) then BoxSet' ( s , (box_tagging_getNSet param y))
                                   else Set'( (box_tagging_getNSet param x), (box_tagging_getNSet param y )))
                     | _ -> Set'( (box_tagging_getNSet param x), (box_tagging_getNSet param y ))  )
   | BoxSet'(var, setTo) -> BoxSet'(var, (box_tagging_getNSet param setTo ))
   | If'(_test_, _then_, _else_) -> If'( (box_tagging_getNSet param _test_  ), (box_tagging_getNSet param _then_  ), (box_tagging_getNSet param _else_ ))
   | Seq' (exprList) -> Seq' (List.map (fun expr' -> (box_tagging_getNSet param expr')) exprList)
   | Or' (exprList) -> Or' (List.map (fun expr' -> (box_tagging_getNSet param expr' )) exprList)
   | LambdaSimple' (stringList, body) -> if(List.mem param stringList) 
                                        then LambdaSimple' (stringList, body) 
                                        else LambdaSimple' (stringList, (box_tagging_getNSet param body))
   | LambdaOpt' (vars,var,body) -> if(List.mem param vars || param = var) 
                                   then LambdaOpt' (vars, var, body )
                                   else LambdaOpt' (vars, var, (box_tagging_getNSet param body )) 
   | Applic' (var, exprList) -> Applic' ((box_tagging_getNSet param var ), (List.map (fun expr' -> (box_tagging_getNSet param expr' )) exprList))
   | ApplicTP' (var, exprList) -> ApplicTP' ((box_tagging_getNSet param var ), (List.map (fun expr' -> (box_tagging_getNSet param expr' )) exprList))
   | Def'(x,y)  -> Def'((box_tagging_getNSet param x ) ,(box_tagging_getNSet param y))
   | _ -> e;;
 
 let rec index_of_param x lst =
   match lst with
   | [] -> (-1)
   | h :: t -> if (x = h) then 0 else (1 + (index_of_param x t));;
 
 let rec box_tagging param body params = 
               let index_of_param = index_of_param param params in
               let body = box_tagging_getNSet param body in 
               let body = (box_tagging_stage_1 param body index_of_param) in
               body;;
 
 let rec findCross list_of_rw_2d = 
     let isRead = (List.mem [1,0] list_of_rw_2d) in
     let isWrite = (List.mem [0,1] list_of_rw_2d) in
     let isWriteAndWrite = (List.mem [1,1] list_of_rw_2d) in
     let isWriteAndWrite2 = (List.length (List.filter (fun a-> a = [1,1]) list_of_rw_2d) >= 2) in
     ( (isRead && isWrite) ||
       (isRead && isWriteAndWrite) ||
       (isWrite && isWriteAndWrite)  ||
       isWriteAndWrite2  );;
 
 let rec rw_2d ls = 
         match ( (List.mem 1 ls) ,  (List.mem (-1) ls) ) with
         | (true , true) -> [1,1]
         | (true , false) -> [1,0]
         | (false , true) -> [0,1]
         | (false , false) -> [0,0] ;;
 
 let rec checkForBox list_of_lists = 
 let list_of_rw_2d = (List.map rw_2d list_of_lists) in
 let need_to_box = (findCross list_of_rw_2d) in
 need_to_box;;
 
 let rec initArray param body =
   let rw_list_outter = (searchRW param body 0 1) in
   (searchLambda param body [rw_list_outter]);;
 
 let rec handle_param param body params =
 let rw_list = initArray param body in
 let need_to_box = checkForBox rw_list in
 if(need_to_box) then (box_tagging param body params)
 else body ;;
 
 
 let rec lambda_box_handler params body =
 List.fold_right (fun  param body-> handle_param param body params) params body ;;
 
 let rec box_main e = 
 match e with
 | If'(te, th , el) -> If' ( (box_main te) , (box_main th), (box_main el))
 | Seq'(exprList) -> Seq'(List.map (fun (element) -> (box_main element)) exprList)
 | Set'(x, y) -> Set'((box_main x), (box_main y))
 | BoxSet'(var, setTo) -> BoxSet'(var, (box_main setTo ))
 | Def'(x,y) -> Def'((box_main x),(box_main y)) 
 | Or'(exprList) -> Or'(List.map (fun (element) -> (box_main element)) exprList)
 | LambdaSimple'(stringList, body) -> LambdaSimple'(stringList, (lambda_box_handler stringList (box_main body)))
 | LambdaOpt'(stringList, extra, body) -> LambdaOpt'(stringList, extra, (lambda_box_handler (List.append stringList [extra]) (box_main body)))
 | Applic'(name, params) -> Applic' ((box_main name), List.map (fun (element) -> (box_main element)) params )
 | ApplicTP'(name, params) -> ApplicTP' ((box_main name), List.map (fun (element) -> (box_main element)) params )
 | _ -> e  ;;
 (** End Box **)
 
 let box_set e = 
  box_main e;;
 
 let run_semantics expr =
    (box_set (annotate_tail_calls
      (annotate_lexical_addresses expr)));;
   
 end;; (* struct Semantics *)
 