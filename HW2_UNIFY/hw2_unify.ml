type algebraic_term = Var of string | Fun of string * (algebraic_term list)

let rec find_max_in_list l = match l with
	| [] -> 0
	| x::xs -> max x (find_max_in_list xs);;

let rec find_max_length_in_term term = match term with
	| Var _ -> 0
	| Fun(x, y) -> max (String.length x) (find_max_in_list (List.map find_max_length_in_term y));;

let rec find_max_length_in_list l = match l with
	| [] -> 0
	| (x, y)::z -> max (max (find_max_length_in_term x) (find_max_length_in_term y)) (find_max_length_in_list z);;

let rec helper list_of_equations first_equation second_equation = match list_of_equations with
	| [] -> (first_equation, second_equation)
	| (x, y)::z -> helper z (first_equation@[x]) (second_equation@[y]);;

let system_to_equation list_of_equations = let var = (String.make (find_max_length_in_list list_of_equations)) 'f' in
									let pair_of_algebraic_terms =  helper list_of_equations ([]) ([]) in 
									(Fun (var^"123", fst pair_of_algebraic_terms), Fun (var^"123", snd pair_of_algebraic_terms));;

system_to_equation [(Var "x", Fun ("y", [Var "z"; Var "oo"])); (Fun ("q", [Var "z"; Var "p"]), Var "x"); (Var "x", Var "y")];;

module MM = Map.Make(String);;
let empty_map = MM.empty;;

let apply_substitution list_of_changes equation = let rec put_in_map list_of_changes cur_map = match list_of_changes with
																								| [] -> cur_map
																								| (x, y)::z -> put_in_map z (MM.add x y cur_map) in
												  let current_map = put_in_map list_of_changes empty_map in
												  let rec parsing_term equation = match equation with
												  									| Var x -> if (MM.mem x current_map) then (MM.find x current_map) else equation
												  									| Fun (x, y) -> Fun (x, List.map parsing_term y) in 
												  parsing_term equation;;


apply_substitution ([("y", Fun ("f", [Var "x"; Var "z"])); ("a", Var "x")]) (Fun ("g", [Var "y"; Var "a"]));;

let rec check_solution substitutions list_of_equations = match list_of_equations with
	| [] -> true
	| (x, y)::z -> ((apply_substitution substitutions x) = (apply_substitution substitutions y)) && (check_solution substitutions z);;

exception IncompatibleSystem

let rec contains variable term = let rec contains_with_list variable list_of_terms = match list_of_terms with
		| [] -> false
		| x::xs -> (contains variable x) || (contains_with_list variable xs) 
	in match term with
	| Var x -> if x = variable then true else false
	| Fun (x, y) -> contains_with_list variable y;;

let merge_list first_list second_list = let rec merging first_list second_list result_list = match (first_list, second_list) with
								| ([], []) -> result_list
								| (x::xs, y::ys) -> merging xs ys ((x, y)::result_list) in 
								merging first_list second_list [];;

let rec insert_in_equations substitutions list_of_equations = match list_of_equations with
	| [] -> []
	| (x, y)::z -> (apply_substitution substitutions x, apply_substitution substitutions y)::(insert_in_equations substitutions z);;

let rec solve_system_with_res system res = match system with
	| [] -> res
	| (left, right)::z -> if left = right then solve_system_with_res z res else match left with
						| Var x -> if contains x right then raise IncompatibleSystem else 
							solve_system_with_res (insert_in_equations [(x, right)] z) ((left, right)::(insert_in_equations [(x, right)] res))
						| Fun (x, y) -> match right with
							| Var xx -> solve_system_with_res ((right, left)::z) res
							| Fun (xx, yy) -> if (xx != x) || ((List.length y) != (List.length yy)) then raise IncompatibleSystem else 
								solve_system_with_res ((merge_list y yy)@z) res;;


let rec check_system system = match system with
	| [] -> []
	| (x, y)::z -> (match x with
		| Var xx -> if contains xx y then raise IncompatibleSystem else (xx, y)::(check_system z)
		| _ -> raise IncompatibleSystem);;

let solve_system system = try Some (check_system (solve_system_with_res system [])) with IncompatibleSystem  -> None;;
