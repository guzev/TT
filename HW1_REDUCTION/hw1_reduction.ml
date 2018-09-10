open Hw1;;

module SS = Set.Make(String);;

let empty_set = SS.empty;;

(* For memoisation, specifically to insert reference to lambda term in several places in current lambda term *)
type lambda_ref = Var_ref of string | App_ref of lambda_ref ref * lambda_ref ref | Abs_ref of string * lambda_ref ref;; 

let free_vars lambda_expression = 
	let rec find_free_vars lambda_expression set_of_vars = match lambda_expression with
		| Var x      -> SS.add x set_of_vars
		| App (x, y) -> SS.union (find_free_vars x set_of_vars) (find_free_vars y set_of_vars)
		| Abs (x, y) -> SS.remove x (find_free_vars y set_of_vars)
	in SS.elements (find_free_vars lambda_expression empty_set);;

let rec subst what_insert where_insert instead = match where_insert with
	| Abs (x, y) -> if x = instead then where_insert (* beacause it's bounded variable*) else Abs (x, subst what_insert y instead)
	| App (x, y) -> App (subst what_insert x instead, subst what_insert y instead)
	| Var x      -> if x = instead then what_insert else where_insert;;

let free_to_subst what_insert where_insert instead = 
		let free_vars_in_insert_lambda = SS.of_list (free_vars what_insert) in
		let rec helper where_insert instead depend_set = match where_insert with
			| Var x 	 -> if x = instead then (SS.is_empty (SS.inter depend_set free_vars_in_insert_lambda)) else true 
			| App (x, y) -> (helper x instead depend_set) && (helper y instead depend_set)
			| Abs (x, y) -> helper y instead (SS.add x depend_set)
		in helper where_insert instead empty_set;;

let is_term_beta_redex lambda_expression = match lambda_expression with
	| App (Abs (_, _), _) -> true
	| _ 				  -> false;;

let is_term_beta_redex_ref lambda_expression_ref = match !lambda_expression_ref with
	| Abs_ref (_, _) -> false
	| Var_ref x -> false
	| App_ref (x, y) -> match !x with
		| Abs_ref (_, _) -> true
		| _ -> false;;

let rec is_normal_form lambda_expression = if is_term_beta_redex lambda_expression then false else match lambda_expression with
		| Abs (x, y) -> is_normal_form y
		| Var x 	 -> true 
		| App (x, y) -> (is_normal_form x) && (is_normal_form y);;

let rec is_normal_form_ref lambda_expression_ref  = if is_term_beta_redex_ref lambda_expression_ref then false else match !lambda_expression_ref with
	| Var_ref x -> true
	| App_ref (x, y) -> (is_normal_form_ref x) && (is_normal_form_ref y)
	| Abs_ref (x, y) -> is_normal_form_ref y;;

let new_number = ref 0;;

let rec is_alpha_equivalent lambda1 lambda2 = match lambda1 with
	| Var x -> (match lambda2 with
		| Var y -> if x = y then true else false
		| _ -> false)
	| App (x, y) -> (match lambda2 with
		| App (x1, y1) -> (is_alpha_equivalent x x1) && (is_alpha_equivalent y y1)
		| _ -> false)
	| Abs (x, y) -> (match lambda2 with
		| Abs (x1, y1) -> new_number := (!new_number) + 1; is_alpha_equivalent (subst (Var ("t"^(string_of_int !new_number))) y x) (subst (Var ("t"^(string_of_int !new_number))) y1 x1)
		| _ -> false);;

let rec ref_from_lambda lambda_expression = match lambda_expression with
	| Var x -> ref (Var_ref x)
	| App (x, y) -> ref (App_ref (ref_from_lambda x, ref_from_lambda y))
	| Abs (x, y) -> ref (Abs_ref (x, ref_from_lambda y));;

let rec lambda_from_ref lambda_ref = match !lambda_ref with
	| Var_ref x -> Var x
	| App_ref (x, y) -> App (lambda_from_ref x, lambda_from_ref y)
	| Abs_ref (x, y) -> Abs (x, lambda_from_ref y);;

let rec subst_ref what_insert where_insert instead = match !where_insert with
	| Var_ref x -> if x = instead then what_insert else where_insert
	| Abs_ref (x, y) -> if x = instead then where_insert else (ref (Abs_ref (x, subst_ref what_insert y instead)))
	| App_ref (x, y) -> ref (App_ref (subst_ref what_insert x instead, subst_ref what_insert y instead));;

let rec normal_beta_reduction_ref lambda_expression_ref = if is_normal_form_ref lambda_expression_ref then lambda_expression_ref else match !lambda_expression_ref with
	| Var_ref x -> ref (Var_ref x) 
	| Abs_ref (x, y) -> ref (Abs_ref (x, normal_beta_reduction_ref y))
	| App_ref (x, y) -> match !x with
		| Abs_ref (o, z) -> subst_ref y z o
		| _ -> if is_normal_form_ref x then (ref (App_ref (x, normal_beta_reduction_ref y))) else (ref (App_ref (normal_beta_reduction_ref x, y)));;

let normal_beta_reduction lambda_expression = lambda_from_ref (normal_beta_reduction_ref (ref_from_lambda lambda_expression));;
	
let rec reduce_to_normal_form lambda_expression = if is_normal_form lambda_expression then lambda_expression else reduce_to_normal_form (normal_beta_reduction lambda_expression);;

print_string (string_of_bool (free_to_subst (Var "x") (Abs ("f", Abs ("x", App (Var "f", Var "x")))) "f"));;
print_string "\n";;
print_string (string_of_bool (free_to_subst (Var "x") (Abs ("f", Abs ("x", App (Var "f", Var "n")))) "n"));;
print_string "\n";;
print_string (string_of_bool (free_to_subst (Var "x") (Abs ("x", App (Var "y", Abs ("z", Var "n")))) "n"));;
print_string "\n";;
print_string (string_of_bool (free_to_subst (Var "f") (Abs ("f", Abs ("x", App (Var "n", Var "x")))) "n"));;
print_string "\n";;

print_string (string_of_bool (is_normal_form (Abs ("x", App (Var "y", Abs ("z", Var "n"))))));;
print_string "\n";;
print_string (string_of_bool (is_normal_form (App (Abs ("x", Var "y"), Var "x"))));;
print_string "\n";;

print_string (string_of_bool (is_alpha_equivalent (Abs ("x", App (Var "x", Var "z"))) (Abs ("y", App (Var "y", Var "a")))));;
print_string "\n";;
print_string (string_of_bool (is_alpha_equivalent (Abs ("x", App (Var "x", Var "z"))) (Abs ("y", App (Var "y", Var "z")))));;
print_string "\n";;

print_string (string_of_lambda (normal_beta_reduction (lambda_of_string ("(\\x.x x) (\\y. y y)"))));;
print_string "\n";;
print_string (string_of_lambda ( reduce_to_normal_form (lambda_of_string ("(\\x.\\y.x) (a) ((\\x.x x) (\\x. x x))"))));;
print_string "\n";;
