
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "pc.ml";;
open PC;;
 exception X_not_yet_implemented;;
 exception X_this_should_not_happen;;
   
 type number =
   | Int of int
   | Float of float;;
   
 type sexpr =
   | Bool of bool
   | Nil
   | Number of number
   | Char of char
   | String of string
   | Symbol of string
   | Pair of sexpr * sexpr
   | Vector of sexpr list;;
 
 let rec sexpr_eq s1 s2 =
   match s1, s2 with
   | Bool(b1), Bool(b2) -> b1 = b2
   | Nil, Nil -> true
   | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
   | Number(Int n1), Number(Int n2) -> n1 = n2
   | Char(c1), Char(c2) -> c1 = c2
   | String(s1), String(s2) -> s1 = s2
   | Symbol(s1), Symbol(s2) -> s1 = s2
   | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
   | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
   | _ -> false;;

(**************)

module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

(*Tokens*)
let _charPrefix_ = word "#\\";;
let _hexPrefix_ = word_ci "x";;
let _charHexPrefix_ = caten _charPrefix_ _hexPrefix_;;
let _nt_digit_ = range '0' '9';;
let _nt_hexLetter_ = range_ci 'a' 'f';; 
let _nt_hexDigit_ = disj _nt_digit_ _nt_hexLetter_;; 
let _nt_dot_ = word ".";;
let _l_paren_ = word "(";;
let _l_paren_Vector_ = word "#(";;
let _r_paren_ = word ")";;
let _nt_letter_ = range_ci 'a' 'z';;
let _nt_punctuation_ = disj_list [char_ci '!'; char_ci '$'; char_ci '^'; char_ci '*'; char_ci '-'; char_ci '_'; char_ci '=' ;
                                 char_ci '+' ; char_ci '<'; char_ci '>'; char_ci '/'; char_ci '?'; char_ci ':'];;
let _nt_lBrack_ = word_ci "[";;
let _nt_lBrackVector_ = word_ci "#[";;
let _nt_rBrack_ = word_ci "]";;    
let _nt_auto_open_ = disj _nt_lBrack_ _l_paren_
let _nt_auto_close_ = disj _nt_rBrack_ _r_paren_
let _nt_auto_close_all_ = word "..."




(*---Number---*)


let _nt_plusSign_ = char_ci '+';;
let _nt_minusSign_ = char_ci '-';;
let _nt_sign_ = disj _nt_plusSign_ _nt_minusSign_;;
let _nt_natural_ = plus _nt_digit_;;
let _nt_numHexPrefix = word_ci "#x";;
let _nt_int_ = pack (caten (maybe _nt_sign_) _nt_natural_) (fun (sign,num) -> match sign with
                                                                              | (None|Some '+') ->  Number(Int (int_of_string(list_to_string num)))
                                                                              | Some '-' ->  Number(Int (-1 * int_of_string(list_to_string num)))
                                                                              | _ -> raise PC.X_no_match);;
let _nt_intForFloat_ =  pack (caten (maybe _nt_sign_) _nt_natural_) (fun (sign,num) -> match sign with
                                                                              | None -> num
                                                                              | Some '+' -> string_to_list(String.make 1 '+' ^ (list_to_string num))
                                                                              | Some '-' -> string_to_list(String.make 1 '-' ^ (list_to_string num))
                                                                              | _ -> raise X_no_match);;
let _nt_float_ = pack (caten (caten _nt_intForFloat_ _nt_dot_) _nt_natural_)
                  (fun ((full, dot),frac) ->  Number(Float (float_of_string((list_to_string full ^ ".") ^ (list_to_string frac)))));;

let _nt_hexNatural_ = plus _nt_hexDigit_;;
let _nt_hexInt_ = pack (caten _nt_numHexPrefix(caten (maybe _nt_sign_) _nt_hexNatural_)) (fun (_, (sign,num)) -> match sign with
                                                                              | (None|Some '+') ->  Number(Int (int_of_string("0x"^(list_to_string num))))
                                                                              | Some '-' ->   Number(Int (-1 * int_of_string("0x"^(list_to_string num))))
                                                                              | _ -> raise X_no_match);;

let _nt_hexIntForFloat_ =  pack (caten _nt_numHexPrefix (caten (maybe _nt_sign_) _nt_hexNatural_)) (fun (_,(sign,num)) -> match sign with
                                                                              | None -> num
                                                                              | Some '+' -> num
                                                                              | Some '-' -> string_to_list(String.make 1 '-' ^ (list_to_string num))
                                                                              | _ -> raise X_no_match);;

let _nt_hexFloat_ = pack (caten (caten _nt_hexIntForFloat_ _nt_dot_) _nt_hexNatural_)
                  (fun ((full, dot),frac) -> if ((String.contains (list_to_string full) '-')) then Number(Float(float_of_string("-0x" ^(list_to_string (List.tl full) ^ ".")^ (list_to_string frac))))
                                                        else  Number(Float(float_of_string("0x" ^((list_to_string full ^ ".") ^ (list_to_string frac))))));;


(*---Scientific notation---*)
let _nt_intScientific_ s=
  let _nt_eNotation_ =  word_ci "e" in
  let _packed_ =  pack (caten _nt_intForFloat_ _nt_eNotation_) (fun (num, e) -> List.append num e) in
  let _packed2_ = pack (caten _packed_ _nt_intForFloat_) (fun (base, power) -> List.append base power) in
  let _packed3_ = pack _packed2_ (fun num -> list_to_string num) in
  let _packed4_ = pack _packed3_ (fun num -> float_of_string num) in
  let makeScience = pack _packed4_ (fun num -> Number (Float num)) in 
  makeScience s;;


let _nt_floatForScience_ = pack (caten (caten _nt_intForFloat_ _nt_dot_) _nt_natural_)
                            (fun ((full, dot),frac) ->  (list_to_string full ^ ".") ^ (list_to_string frac));;

let _nt_floatScientific_ s = 
  let _nt_eNotation_ = word_ci "e" in
  let _packed_ = pack (caten _nt_floatForScience_ _nt_eNotation_ ) (fun (num, e) -> num^"e") in
  let _packed2_ = pack (caten _packed_ _nt_intForFloat_) (fun (base, power) -> List.append (string_to_list base) power) in
  let _packed3_ = pack _packed2_ (fun num -> list_to_string num) in
  let _packed4_ = pack _packed3_ (fun num -> float_of_string num) in
  let makeScience = pack _packed4_ (fun num -> Number (Float num)) in 
  makeScience s;;

  let _nt_Scientific_notation_ = disj_list [_nt_floatScientific_ ; _nt_intScientific_];;



(*---Symbol---*)
     
let toLower = (fun chr -> if (chr >='A' && chr<='Z') then (Char.chr (Char.code chr + 32))
                          else chr);;
let _nt_symbolChar_ = disj (disj _nt_letter_ _nt_digit_) _nt_punctuation_;;
let _nt_symbolString_ = plus _nt_symbolChar_;;
let _nt_symbol_ = pack (_nt_symbolString_) (fun myList -> Symbol(String.map toLower (list_to_string myList)));;
let _nt_Number_ =  pack (not_followed_by (disj_list [ _nt_hexFloat_ ; _nt_hexInt_ ; _nt_Scientific_notation_ ;_nt_float_ ;_nt_int_]) _nt_symbol_)  (fun a -> a) ;;


(*---Boolean---*)
let _nt_boolean_ = 
  let _nt_true_ = pack (word_ci "#t") (fun _-> Bool true) in
  let _nt_false_ = pack (word_ci "#f") (fun _-> Bool false) in
  not_followed_by (disj_list [_nt_true_;_nt_false_]) _nt_symbol_;;

(*---Chars---*)
let _named_chars_  =
  let _newline_ = word_ci "newline" in
  let _nul_ = word_ci "nul" in
  let _page_ = word_ci "page" in
  let _return_ = word_ci "return" in
  let _tab_ = word_ci "tab" in
  let _space_ = word_ci "space" in
  let _nul_ = word_ci "nul" in
  let _nt_nul_ = pack  _nul_ (fun c ->  (Char.chr 0)) in
  let _nt_charNewLine_ = pack  _newline_ (fun c ->  (Char.chr 10)) in
  let _nt_charReturn_ = pack  _return_ (fun c ->  (Char.chr 13)) in 
  let _nt_charTab_ = pack  _tab_ (fun c ->  (Char.chr 9)) in
  let _nt_charPage_ = pack _page_ (fun c ->  (Char.chr 12)) in
  let _nt_charSpace_ = pack _space_ (fun c ->  (Char.chr 32)) in
    disj_list [_nt_nul_ ; _nt_charNewLine_; _nt_charReturn_ ; _nt_charTab_ ; _nt_charPage_; _nt_charSpace_];;
   
let _nt_visibleChar_  =
  let _nt_any_range (s : char list) = const (fun ch -> Char.code ch > 32) s in
                                      pack _nt_any_range
                                                   (fun tl ->  (tl));;
let _nt_charHexadecimal_ = 
  let _digits_ = caten _hexPrefix_ (plus _nt_hexDigit_) in
                 pack  _digits_ (fun (hd , tl) -> 
                  (Char.chr (int_of_string((list_to_string ('0'::'x'::tl))))));;
  
let _nt_char_ = pack (caten _charPrefix_ (disj_list [ _named_chars_; _nt_charHexadecimal_ ; _nt_visibleChar_ ]))
                     (fun (_, c) -> Char c);;

(*---String---*)
let _nt_StringHexChar_ = pack (caten (caten (word_ci "\\")  _nt_charHexadecimal_) (word ";")) (fun ((_,tl),_) ->  tl );;
let _nt_StringMetaChar_ = 
  let _nt_stringMeta_Nul_ = pack (word "\\nul") (fun c ->  (Char.chr 0)) in
  let _nt_stringMeta_NewLine_ = pack (word "\\n") (fun c ->  (Char.chr 10)) in
  let _nt_stringMeta_Return_ = pack (word "\\r") (fun c ->  (Char.chr 13)) in
  let _nt_stringMeta_Tab_ = pack (word "\\t") (fun c ->  (Char.chr 9)) in
  let _nt_stringMeta_Page_ = pack (word "\\f") (fun c ->  (Char.chr 12)) in
  let _nt_stringMeta_BackSlash_ = pack (word "\\\\") (fun c ->  (Char.chr 92)) in  
  let _nt_stringMeta_DoubleQuote_ = pack (word "\\\"") (fun c ->  (Char.chr 34)) in
  disj_list [_nt_stringMeta_Nul_ ; _nt_stringMeta_NewLine_; _nt_stringMeta_Return_ ;
             _nt_stringMeta_Tab_ ; _nt_stringMeta_Page_;
             _nt_stringMeta_DoubleQuote_ ; _nt_stringMeta_BackSlash_];;

  let _nt_StringLiteralChar_ = pack (const (fun ch -> (Char.code ch != 34 && Char.code ch != 93))) (fun (hd) ->  hd);;

  let _nt_StringChar_ = disj_list [_nt_StringHexChar_ ;_nt_StringMetaChar_ ; _nt_StringLiteralChar_ ; ] ;;

  let _nt_String_ = 
       let _chars_ =  caten (caten (word "\"") (star _nt_StringChar_)) (word "\"") in
       pack _chars_ (fun ((_,chars),_) -> String (list_to_string chars));;
(*---Comments & whitespaces---*)

(*---Line comments---*)
let nt_startOfLineComment = word ";";;
let nt_endOfLine = char '\n';;
let nt_lineCommentContent = pack (caten nt_startOfLineComment (star (diff nt_any nt_endOfLine))) (fun (s,c) ->   ";"^(list_to_string c));;
let nt_lineCommentWithLine = pack (caten nt_lineCommentContent nt_endOfLine) (fun (s,e) ->  s^"\n");;
let nt_lineCommentWithInput = not_followed_by nt_lineCommentContent nt_any;;
let nt_lineComment = pack (disj nt_lineCommentWithLine nt_lineCommentWithInput) (fun _ -> String "");;



  let rec _Main_Parser_ s = 
    let _disjoint_ =  star ( _nt_sexpr_) in
    _disjoint_ s 
  
  and nt_comment_sexpr s =  
          let _star_ = caten (word "#;") _nt_sexpr_ in
          let _packed_ = pack _star_ (fun _ -> String "") in
          _packed_ s
  
  and _nt_comment_ s =  
  (*TODO: ADD LINE COMMENT*)
      let _disj_ = disj nt_comment_sexpr nt_lineComment in
      _disj_ s
  
  and nt_white_ s = 
          let _packed_ = pack (const (fun ch -> ch <= ' ')) (fun _ -> String "") in
          _packed_ s
  
  and _nt_skipped_ s = 
        let _disjoint_ =  disj nt_white_ _nt_comment_ in
        _disjoint_ s 
  
  and _make_skipped_ nt s=
      let _head_ =  caten (star _nt_skipped_) nt in
      let _chain_ = caten _head_ (star _nt_skipped_) in
      let _packed_ = pack _chain_ (fun ((_,e),_) -> e) in
      _packed_ s
  
  (*---Sexpr Parser---*)
  and _nt_sexpr_ s = 
      let _sexpr_with_skipped_ = List.map _make_skipped_ [  _nt_boolean_ ; _nt_char_ ; _nt_Number_ ;_nt_String_ ;
                      _nt_symbol_ ;_nt_List_ ; _nt_DottedList_ ; _nt_Vector_ ; _nt_Quoted_ ; _nt_QQuoted_ ; _nt_UnquotedSpliced_ ; _nt_Unquoted_ ; _nt_nil_ ; _auto_outside_ ; _auto_inside_Dot_] in
      let _disjoint_ = disj_list _sexpr_with_skipped_ in
                      _disjoint_ s 
  
  and _nt_nil_ s = 
        let headParen = caten _l_paren_ (caten (star _nt_skipped_) _r_paren_)  in
        let headBrack = caten _nt_lBrack_ (caten (star _nt_skipped_) _nt_rBrack_) in
        let head = pack (disj headParen headBrack) (fun _ -> Nil) in
        head s
  
  and _nt_List_ s =
      let _parenParse_ = caten  _l_paren_  (caten (star _nt_sexpr_) _r_paren_ ) in
      let _brackParse_ = caten _nt_lBrack_ (caten (star _nt_sexpr_) _nt_rBrack_) in
      let _unite_ = disj _parenParse_ _brackParse_ in
      let _packed_ = (pack _unite_ (fun (lp,(sexpr_list,_)) -> List.fold_right (fun a b -> Pair(a,b)) sexpr_list Nil)) in
      _packed_ s    
  
  
  and _nt_DottedList_ s =
      let _dotHeadParen_ =  caten (caten  _l_paren_ (plus _nt_sexpr_)) (char '.') in
      let _dotChainParen_ =  caten _dotHeadParen_ _nt_sexpr_  in
      let _chainParen_ = caten _dotChainParen_ _r_paren_ in
  
      let _dotHeadBracket_ =  caten (caten  _nt_lBrack_ (plus _nt_sexpr_)) (char '.') in
      let _dotChainBracket_ =  caten _dotHeadBracket_ _nt_sexpr_  in
      let _chainBracket_ = caten _dotChainBracket_ _nt_rBrack_ in
      
      let _unite_ = disj _chainParen_ _chainBracket_ in
      let _packed_ = pack _unite_ (fun ((((_,sexpr_list),_) , sexpr) , _) -> List.fold_right (fun a b -> Pair(a,b)) sexpr_list sexpr) in
      _packed_ s
  
  and _nt_Vector_ s =
      let _parenParse_ = caten _l_paren_Vector_ (caten (star _nt_sexpr_) _r_paren_) in
      let _brackParse_ = caten _nt_lBrackVector_ (caten (star _nt_sexpr_) _nt_rBrack_) in
      let _unite_ = disj _parenParse_ _brackParse_ in
      let _packed_ = pack _unite_ (fun (_,(sexpr_list,_)) ->  Vector sexpr_list) in
      _packed_ s   
  
    and _nt_Quoted_ s=
      let _chain_ = caten (word "\'") _nt_sexpr_ in
      let _packed_ = pack _chain_ (fun (_,sexpr) ->  Pair (Symbol("quote") , Pair(sexpr, Nil)))  in
      _packed_ s
  
    and _nt_QQuoted_ s=
      let _chain_ = caten (word "`") _nt_sexpr_ in
      let _packed_ = pack _chain_ (fun (_,sexpr) ->  Pair (Symbol("quasiquote") , Pair(sexpr, Nil)))  in
      _packed_ s
  
    and _nt_UnquotedSpliced_ s=
      let _chain_ = caten (word ",@") _nt_sexpr_ in
      let _packed_ = pack _chain_ (fun (_,sexpr) ->  Pair (Symbol("unquote-splicing") , Pair(sexpr, Nil)))  in
      _packed_ s
  
    and _nt_Unquoted_ s=
      let _chain_ = caten (word ",") _nt_sexpr_ in
      let _packed_ = pack _chain_ (fun (_,sexpr) ->  Pair (Symbol("unquote") , Pair(sexpr, Nil)))  in
      _packed_ s
    
  and _auto_inside_List_ s = 
      let _head_ = caten _nt_auto_open_  (star (disj (diff _nt_sexpr_ _auto_outside_) _auto_inside_)) in
      let _chain_ = caten  _head_ (maybe _nt_auto_close_) in
      let _packed_ = pack _chain_ (fun ((_,sexpr_list),_) -> List.fold_right (fun a b -> Pair(a,b)) sexpr_list Nil) in
      _packed_  s
  
  and _auto_inside_Dot_ s = 
      let _head_ = caten _nt_auto_open_  (star (disj (diff _nt_sexpr_ _auto_outside_) _auto_inside_)) in
      let _headDot_ = caten  _head_ (char '.') in
      let _chainDot_ = caten _headDot_   (disj (diff _nt_sexpr_ _auto_outside_) _auto_inside_)  in
      let _tail_ = caten _chainDot_  (maybe _nt_auto_close_) in
      let _packedDot_ = pack _tail_ (fun ((((_,sexpr_list),_) , sexpr) , _) -> List.fold_right (fun a b -> Pair(a,b)) sexpr_list sexpr) in
       _packedDot_ s
  
  and _auto_inside_ s = 
  let dis = disj _auto_inside_Dot_ _auto_inside_List_  in
  dis s
  
  and _auto_outside_ s = 
        let _chain_ = caten  _auto_inside_ _nt_auto_close_all_ in
        let _packed_ = pack _chain_ (fun (sexpr,_) ->   sexpr ) in
        _packed_ s;;
  
let rec first_element list = 
    match list with 
     | [] -> failwith "List is empty"
     | first_el::rest_of_list -> first_el         

let read_sexpr string = let (e, s) = _Main_Parser_ (string_to_list string) in
first_element e;;

let read_sexprs string = 
  let (e, s) = _Main_Parser_ (string_to_list string) in
    e;;
  
end;; (* struct Reader *)