(* ввести в консоли ocamlc -o <ex_name> hw1.mli hw1.ml t.ml *)

open Genlex;; (* модуль для лексического анализатора *)

(* определяем тип пеано и лямбда-выражений  *)

type peano = Z | S of peano;;

type lambda = 
		| Var of string
		| Abs of string * lambda
		| App of lambda * lambda;;

(* действия с арифметикой пеано*)

let rec int_of_peano x = match x with 
	| Z -> 0
	| S a -> 1 + int_of_peano a;;

let rec peano_of_int x = match x with 
	| 0 -> Z
	| x -> S (peano_of_int (x-1));;

let inc x = S x;;

let rec add x y = match (x,y) with 
	| (x, Z) -> x
	| (Z, y) -> y
	| (x, S b) -> S (add x b);;

let rec mul x y = match (x,y) with 
	| (x, Z) -> Z
	| (Z, y) -> Z
	| (x, S b) -> add x (mul b x);;

let rec sub x y = match (x,y) with 
	| (Z, y) -> Z
	| (x, Z) -> x
	| (S a, S b) -> sub a b;;

let rec power x y = match (x,y) with 
	| (x, Z) -> S Z 
	| (Z, y) -> Z
	| (x, S b) -> mul x (power x b);;
                     
let rec dop_rev x y = match (x,y) with 
	| (x, []) -> x
	| (x, h::ys) -> dop_rev (h::x) ys;;

(* функции, для работы с list *)

let rev x = match x with 
	| [] -> []
	| x -> dop_rev [] x;; 

let rec merge xs1 xs2 =
    match (xs1, xs2) with 
    | ([], xs2) -> xs2
    | (xs1, []) -> xs1
    | (x::s1, y::s2) -> if x>y then y::(merge xs1 s2) else x::(merge s1 xs2);;

let rec split_at i l = 
    match i with 
    | 0 -> ([], l)
    | _ -> (match l with
            | [] -> failwith "Пустой список" 
            | (x::xs) -> 
                    let res = split_at (i-1) xs in 
		    match res with 
		    | (lr, rr) -> (x::lr, rr));;

let rec merge_sort x = 
    let size = List.length x in 
    let halves = split_at (size/2) x in
        match halves with
	| _ when (size = 1 || size = 0) -> x
	| (half_l, half_r) -> merge (merge_sort half_l) (merge_sort half_r);;
                     
let rec print_int_list x = 
    match x with 
    | [] -> print_string " "
    | a::xs -> print_int a; print_string " "; print_int_list xs;;

(* функции для парсинга лямбда-выражений *)

let end_sym = ";";;
let lexer_lambda = make_lexer ["\\";".";"(";")";";"];;
let str_with_end_sym str = str^end_sym;;

let rec string_of_lambda x =
    match x with
    | Var l -> l
    | App (a,b) -> "(" ^ string_of_lambda a ^ " " ^ string_of_lambda b ^ ")"
    | Abs (s,e) -> "(\\" ^ s ^ "." ^ string_of_lambda e ^ ")";; 

let parse_lambda_of_tokens str_tokens =
    let token() = Stream.next str_tokens in
    let peek() = Stream.peek str_tokens in
    let br() = if (token() <> Kwd ")") then failwith "Неизвестный символ" in
    let comm() = if (token() <> Kwd ".") then failwith "Неизвестный символ" in
    
    let rec parse_lambda() =
	match (token()) with
        | Kwd "("  -> 
                let pl = parse_lambda() in
            	br(); 
                maybe pl;

        | Kwd "\\" ->
                let pa = parse_abs() in
     		(let abs = maybe pa in abs)

        | Ident s  ->
                let v = Var s in
     		maybe v;
                   
        | _ -> failwith "Неизвестный символ"

    and parse_abs() = 
        match (token()) with 
        | Ident s -> 
                comm();
                Abs(s, parse_lambda());
    	    
        | _ -> failwith "Неизвестный символ" 

    and maybe l_app = 
        match (peek()) with 
        | None   -> failwith "Неизвестная ошибка";
        | Some k -> 
                (match k with 
                 | Kwd ")"  -> l_app
      		     | Kwd ";"  -> l_app
                 | Kwd "\\" -> App(l_app, parse_lambda())
        	     | Kwd "("  -> let _ = token() and newp = parse_lambda() in (br(); maybe (App(l_app, newp)))
                 | Ident s  -> let _ = token() in maybe (App(l_app, Var(s))) 
                 | _ -> failwith "Неизвестный символ") in 

    parse_lambda();; 
 
let lambda_of_string x = parse_lambda_of_tokens (lexer_lambda(Stream.of_string (str_with_end_sym x)));;
