(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;
exception X_extract_params_inner;;
exception X_extract_params_outer;;
exception X_extract_args_inner;;
exception X_extract_args_outer;;
exception X_let_star_recursive;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)


let rec tag_parse sexpr =
 
  
  match sexpr with
    | Nil -> Const(Sexpr(Nil))
    | Number(x) -> Const(Sexpr(Number x))
    | Bool(x) ->  Const(Sexpr(Bool x))
    | Char(x) -> Const(Sexpr(Char x))
    | String(x) -> Const(Sexpr(String x))
    | Pair(Symbol("quote"), Pair (x, Nil)) -> Const(Sexpr(x))
    | Pair(Symbol("quasiquote"), Pair (x, Nil)) -> (quasiquote_Handler x)
    | Symbol(x) ->  Var (check_reserverd x)
    | Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) -> If(tag_parse test, tag_parse dit, tag_parse dif)
    | Pair(Symbol("if"), Pair(test, Pair(dit, Nil))) -> If(tag_parse test, tag_parse dit, Const(Void))
    | Pair(Symbol "if", cdr) -> raise X_syntax_error
    | Pair((Symbol "lambda") , (Pair (args, body)))  -> (lambda_Handler args body)
    | Pair(Symbol("define"), Pair(Symbol (var) , Pair (exp, Nil))) -> Def(Var (check_reserverd(var)), tag_parse exp)
    | Pair(Symbol("define"), Pair(Pair(var, argList), exprs)) -> tag_parse (Pair(Symbol ("define"), Pair(var, Pair(Pair(Symbol("lambda"),Pair(argList, exprs)), Nil))))
    | Pair(Symbol "define", cdr) -> raise X_syntax_error
    | Pair((Symbol "begin"), x) -> (begin_Handler x)
    | Pair(Symbol("set!"), Pair(Symbol(var), Pair(expr, Nil))) -> Set(Var var, tag_parse expr)
    | Pair(Symbol("or"), expr) -> (match expr with
                                    | Nil -> Const(Sexpr(Bool false))
                                    | Pair (car, cdr) -> (match cdr with
                                                          | Nil -> tag_parse (car)
                                                          | Pair(a , b) -> Or(List.map tag_parse (sexprs_to_list(expr)))
                                                          | _ -> raise X_syntax_error)
                                    | _ -> raise X_syntax_error)
    | Pair(Symbol("and"), expr) -> (and_Handler expr)
    | Pair(Symbol("cond"), ribs) -> (cond_Handler ribs)
    | Pair(Symbol("let"), Pair(ribs, body)) -> tag_parse (let_handler ribs body)
    | Pair(Symbol("let*"), Pair(Pair(firstRib, Nil), body)) -> let ribs = Pair(firstRib, Nil) in
                                                                          tag_parse (Pair(Symbol("let"), Pair(ribs, body)))
    | Pair(Symbol("let*"), Pair(Nil, body)) -> tag_parse (Pair(Symbol("let"), Pair(Nil, body)))
    | Pair(Symbol("let*"), Pair(Pair(firstRib, restRibs), body)) -> tag_parse (let_star_recursive_handler firstRib restRibs body)
    | Pair(Symbol("letrec"), Pair(ribs, body)) -> tag_parse (letrec_handler ribs body)
    | Pair(name, exprs) -> Applic(tag_parse name, List.map tag_parse (sexprs_to_list(exprs)))
    | _ -> raise X_syntax_error



  and and_Handler exprs = match exprs with
    | Nil -> Const(Sexpr(Bool true))
    | Pair(car, cdr) -> (match cdr with
                        | Nil -> tag_parse car
                        | _ -> If(tag_parse car,  tag_parse (Pair(Symbol("and"), cdr)), Const(Sexpr(Bool false))))
    | _ -> raise X_syntax_error

  and let_handler ribs body =
  let params = extract_params ribs in
  let args = extract_args ribs in
  Pair(Pair(Symbol "lambda", Pair(params, body)), args)
  

  and letrec_handler ribs body = 
    
    let args_sexps = extract_args ribs in
    let params_sexps = extract_params ribs in
    let args_list = sexprs_to_list args_sexps in
    let params_list = sexprs_to_list params_sexps in
    let new_ribs = List.fold_right (fun a b -> Pair(a, b)) (List.map (
      fun s -> match s with
    | (Pair(param, (Pair(s, Nil)))) -> Pair(param , Pair (Pair (Symbol("quote") , Pair(Symbol("whatever") , Nil)) , Nil ))
    | _ -> raise X_syntax_error ) (sexprs_to_list ribs)) Nil in
    let set_on_body = List.map2
      (fun param expr -> Pair ( Symbol("set!"), (Pair(param, (Pair(expr, Nil)))))) params_list args_list in
    let final_body = List.fold_right (fun a b -> Pair(a, b)) set_on_body body in
    Pair(Symbol("let"), Pair(new_ribs, final_body))

  




  and extract_params ribs = match ribs with
                            | Pair (car, cdr) -> (match car with
                                                | Pair (param, arg) -> Pair(param, extract_params(cdr))
                                                | Nil -> Nil
                                                | _ -> raise X_extract_params_inner)
                            | Nil -> Nil
                            | _ -> raise X_extract_params_outer

  and extract_args ribs = match ribs with
                            | Pair (car, cdr) -> (match car with
                                                | Pair (param, Pair(arg, Nil)) -> Pair(arg, extract_args(cdr))
                                                | Nil -> Nil
                                                | _ -> raise X_extract_args_inner)
                            | Nil -> Nil
                            | _ -> raise X_extract_args_outer

and let_star_recursive_handler firstRib restRibs body = match restRibs with
    | Pair (secondRib, rest) -> 
        Pair(Symbol "let", Pair(Pair(firstRib, Nil), Pair(Pair(Symbol "let*", Pair(Pair(secondRib, rest), body)), Nil)))
    | _ -> raise X_let_star_recursive

and cond_Handler ribs = match ribs with
                          | Pair(car, cdr) -> (match car with
                                              | Pair(Symbol("else"), exprs) -> if (sexpr_eq cdr Nil) then tag_parse (Pair(Symbol "begin" , exprs)) else (raise X_syntax_error)
                                              | Pair (test, exprs) -> (match exprs with
                                                                      | Pair(Symbol("=>"), proc) -> tag_parse (cond_to_let_handler test proc cdr)
                                                                      | _ -> If(tag_parse test, tag_parse (Pair(Symbol "begin" , exprs)), tag_parse (Pair(Symbol("cond"), cdr))))
                                              | Nil -> Const(Void)
                                              | _ -> raise X_syntax_error)
                          | Nil -> Const(Void)
                          | _ -> raise X_syntax_error
  
and cond_to_let_handler test proc restRibs = match restRibs with
                          | Nil -> Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(test, Nil)), Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, proc)), Nil)), Nil)), Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Nil))), Nil)))
                          | _ ->   Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(test, Nil)), Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil,proc)), Nil)), Pair(Pair(Symbol "rest", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(Pair(Symbol "cond", restRibs), Nil))), Nil)), Nil))), Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Pair(Pair(Symbol "rest", Nil), Nil)))), Nil)))
(*---quasiquote---*)
and quasiquote_Handler sexpr = 
                      match sexpr with
                      | Nil -> tag_parse (Pair(Symbol("quote"), Pair(sexpr , Nil)))
                      | Symbol(s) -> tag_parse (Pair(Symbol("quote"), Pair(sexpr , Nil)))
                      | Pair(Symbol("unquote"), Pair (x, Nil)) -> tag_parse x
                      | Pair(Symbol("unquote-splicing"), Pair (x, Nil)) -> raise X_syntax_error
                      | Vector(ls) -> 
                        let tagged_list = List.map (fun a -> Pair( Symbol ("quasiquote") , Pair(a,Nil))) ls   in
                        let proper_list = (List.fold_right (fun a b -> Pair(a, b)) tagged_list Nil) in
                        tag_parse (Pair((Symbol("vector")), proper_list))
                        
                      | Pair( Pair((Symbol("unquote-splicing")), (Pair( a , Nil ))) , b ) ->
                        tag_parse (Pair(Symbol("append"), (Pair (a , (Pair((Pair( Symbol ("quasiquote") , Pair (b, Nil))), Nil))))))
                      | Pair( a , (Pair((Symbol("unquote-splicing")), (Pair( b , Nil)))) ) ->    
                        tag_parse (Pair(Symbol("cons"), (Pair ( Pair( Symbol ("quasiquote") , Pair (a, Nil)) , Pair(b, Nil)))))
                      | Pair(a,b) -> 
                        let a = Pair( Symbol ("quasiquote") , Pair (a, Nil)) in
                        let b = Pair( Symbol ("quasiquote") , Pair (b, Nil)) in
                        tag_parse (Pair((Symbol("cons")), (Pair(a, (Pair(b, Nil))))))
                      | _ -> tag_parse (Pair(Symbol("quote"), Pair(sexpr , Nil)))

(*---begin---*)
and begin_Handler sexpr = 
                  let tagged_list = List.map tag_parse (sexprs_to_list(sexpr)) in
                  let size = List.length tagged_list in
                      (match size with
                      | 0 -> Const(Void)
                      | 1 -> List.nth tagged_list 0
                      | _ -> Seq(tagged_list))
                      
    
(*---lambda---*)
and lambda_Handler args body =
(match body with
| Nil -> raise X_syntax_error
                  | _ ->
      let rec args_handler args = 
        (match args with 
        | Nil -> ([],Nil)
        | Pair((Symbol car),cdr) -> 
          let (head,tail) = (args_handler cdr) in
          if(List.mem car head)
          then raise X_syntax_error
          else (car::head,tail)
        | a -> ([],args)) in


        let (v,vs) = (args_handler args) in
        let tagged_body = tag_parse (Pair((Symbol "begin"), body)) in

          (match vs with
          | Nil -> LambdaSimple (v, tagged_body )
          | Symbol (vs) -> if(List.mem vs v )
          then raise X_syntax_error
          else LambdaOpt (v,vs, tagged_body )
          | _ -> raise X_syntax_error))

(*---Utils functions---*)
and sexprs_to_list sexp =  match sexp with
          | Nil -> []
          | Pair(car,cdr) -> (match cdr with
                            | Nil -> [car]
                            | Pair(cadr, cddr) -> car :: sexprs_to_list(cdr)
                            | _ -> raise X_syntax_error)
          | _ -> raise X_syntax_error

and check_reserverd s =
    if (ormap (fun word -> word = s) reserved_word_list)
    then raise X_syntax_error else s;;

let tag_parse_expression sexpr = tag_parse sexpr;;

let tag_parse_expressions sexpr = List.map tag_parse (sexpr);;



end;; (* struct Tag_Parser *)
