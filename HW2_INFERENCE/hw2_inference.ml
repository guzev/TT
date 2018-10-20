open Hw1;;
open Hw2_unify;;
open Hw1_reduction;;

module M = Map.Make(String);;
module S = Set.Make(String);;

let empty_map = M.empty;;
let empty_set = S.empty;;

type simp_type = S_Elem of string 
			   | S_Arrow of simp_type * simp_type ;;

type hm_lambda = HM_Var of string 
			   | HM_Abs of string * hm_lambda 
			   | HM_App of hm_lambda * hm_lambda 
			   | HM_Let of string * hm_lambda * hm_lambda ;;


type hm_type = HM_Elem of string 
			 | HM_Arrow of hm_type * hm_type 
			 | HM_ForAll of string * hm_type ;;

let rec from_term_to_type term = match term with
	| Hw2_unify.Fun (x, [y; z]) -> S_Arrow (from_term_to_type y, from_term_to_type z)
	| Hw2_unify.Var x 		  -> S_Elem x
	| _  			  -> failwith "Term is not converted to type";;

let rec from_type_to_term t = match t with
	| S_Arrow (x, y) -> Hw2_unify.Fun ("f", [from_type_to_term x; from_type_to_term y])
	| S_Elem x 		 -> Hw2_unify.Var x
	| _ 			 -> failwith "Type is not converted to Term";;

let id_for_type = ref 0;;

let new_name_of_type() = id_for_type := (!(id_for_type)) + 1; S_Elem ("new_type"^(string_of_int !(id_for_type)));;

let id_for_hm_type = ref 0;;

let new_name_of_hm_type() = id_for_hm_type := (!(id_for_hm_type)) + 1; "new_type_hm"^(string_of_int !(id_for_hm_type));;

let rec convert_system_to_term system = match system with
	| [] -> []
	| (x, y)::z  -> (from_type_to_term x, from_type_to_term y)::(convert_system_to_term z);;

let rec convert_system_to_type system = match system with
	| [] -> []
	| (x, y)::z -> (x, from_term_to_type y)::(convert_system_to_type z);;

let get_start_types lambda_expression = let fvs = Hw1_reduction.free_vars lambda_expression in 
										let rec adding_to_map list_of_vars map = match list_of_vars with
										| [] -> map
										| x::xs -> adding_to_map xs (M.add x (new_name_of_type()) map) in 
											adding_to_map fvs empty_map ;;

let rec get_system lambda_expression types = match lambda_expression with
										| Hw1.Var x -> ([], M.find x types) 
										| Hw1.Abs (x, y) -> let added_new_type = M.add x (new_name_of_type()) types in 
															let (solved_system, t) = get_system y added_new_type in 
															(solved_system, S_Arrow(M.find x added_new_type, t))
										| Hw1.App (x, y) -> let (systemx, t1) = get_system x types in
														let (systemy, t2) = get_system y types in 
														let new_type_for_app = new_name_of_type() in 
														([t1, S_Arrow(t2, new_type_for_app)] @ systemy @ systemx, new_type_for_app);;

let get_system_from_lambda lambda_expression = let types = get_start_types lambda_expression in get_system lambda_expression types;;

let infer_simp_type lambda_expression = let (solved_system, t) = get_system_from_lambda lambda_expression in 
												match solve_system (convert_system_to_term solved_system) with
												 | Some sol -> let applied_subst = apply_substitution sol (from_type_to_term t) in 
												 		Some (convert_system_to_type sol, from_term_to_type applied_subst)
												 | None -> None;;


let free_vars_in_hm_type t = let rec find_free_vars_in_hm_type t s = match t with
		| HM_Elem x -> if S.mem x s then empty_set else (S.add x empty_set)
		| HM_Arrow (x, y) -> S.union (find_free_vars_in_hm_type x s) (find_free_vars_in_hm_type y s)
		| HM_ForAll (x, y) -> find_free_vars_in_hm_type y (S.add x s) in
	find_free_vars_in_hm_type t empty_set;;

let free_vars_in_hm_lambda lambda_expression = let rec find_free_vars_in_hm_lambda lambda_expression s = match lambda_expression with
		| HM_Var x -> if S.mem x s then empty_set else (S.add x s)
		| HM_App (x, y) -> S.union (find_free_vars_in_hm_lambda x s) (find_free_vars_in_hm_lambda y s)
		| HM_Abs (x, y) -> find_free_vars_in_hm_lambda y (S.add x s)
		| HM_Let (x, l1, l2) -> S.union (find_free_vars_in_hm_lambda l1 s) (find_free_vars_in_hm_lambda l2 (S.add x s)) in 
	find_free_vars_in_hm_lambda lambda_expression empty_set;;

let add_to_map_free_vars value map = M.add value (HM_Elem (new_name_of_hm_type())) map ;;

let return_start_context lambda_expression = S.fold add_to_map_free_vars (free_vars_in_hm_lambda lambda_expression) empty_map;;

let substitution_in_type t substitutions = let rec applying_subst t s = match t with
		| HM_Elem x -> if (not (S.mem x s)) && (M.mem x substitutions) then M.find x substitutions else t 
		| HM_Arrow (x, y) -> HM_Arrow ((applying_subst x s), (applying_subst y s))
		| HM_ForAll (x, y) -> HM_ForAll (x, applying_subst y (S.add x s)) 
	in applying_subst t empty_set;;

let substitution_in_context context substitutions = let add_to_map_subst key value map = M.add key (substitution_in_type value substitutions) map in 
														M.fold add_to_map_subst context empty_map;;

let rec from_hm_lambda_to_algebraic_term lambda_expression = match lambda_expression with
	| HM_Elem x -> Hw2_unify.Var x
	| HM_Arrow (x, y) -> Hw2_unify.Fun ("f", [from_hm_lambda_to_algebraic_term x; from_hm_lambda_to_algebraic_term y])
	| _ -> failwith "can't be";;

let rec from_algebraic_term_to_hm_lambda at = match at with
	| Hw2_unify.Var x -> HM_Elem x
	| Hw2_unify.Fun ("f", [x; y]) -> HM_Arrow (from_algebraic_term_to_hm_lambda x, from_algebraic_term_to_hm_lambda y)
	| _ -> failwith "can't be";;

let free_vars_in_context context = let help_function_with_map key value s = S.union (free_vars_in_hm_type value) s in 
										M.fold help_function_with_map context empty_set;;

let clarification t = let rec elem_and_arrow t map = match t with
							| HM_ForAll (x, y) -> failwith "can't be"
							| HM_Elem x -> if M.mem x map then M.find x map else t
							| HM_Arrow (x, y) -> HM_Arrow (elem_and_arrow x map, elem_and_arrow y map) in 
					  let rec forall_and_other t map = match t with
					  		| HM_ForAll (x, y) -> forall_and_other y (M.add x (HM_Elem (new_name_of_hm_type())) map)
					  		| _ -> elem_and_arrow t map in 
					  forall_and_other t empty_map;;

let convert_to_hm_forall key value = HM_ForAll(key, value);;

let general lambda_expression context = let fv_context = free_vars_in_context context in 
										let fv_hm_lambda = free_vars_in_hm_type lambda_expression in 
										let filter_set key s = if S.mem key fv_context then s else S.add key s in 
										let help_set = S.fold filter_set fv_hm_lambda empty_set in 
										S.fold convert_to_hm_forall help_set lambda_expression;;

let merge_two_maps key x y = match (x, y) with
	| (Some x1, None) -> Some x1
	| (None, Some y1) -> Some y1
	| (Some x1, Some y1) -> Some y1;;

let mult_subst s1 s2 =  let help_subst x = substitution_in_type x s1 in 
						let new_s2 = M.map help_subst s2 in 
						M.merge merge_two_maps s1 new_s2;;

let rec convert_list_to_hm l = match l with
	| [] -> []
	| (x, y)::z -> (x, from_algebraic_term_to_hm_lambda y)::(convert_list_to_hm z);;

let rec convert_list_to_map l map = match l with
	| [] -> map
	| (x, y)::z -> convert_list_to_map z (M.add x y map);;

let rec implementation_algorithm_w lambda_expression context = match lambda_expression with
	| HM_Var x -> (empty_map, clarification (M.find x context))
	| HM_Abs (x, y) -> (let new_name = HM_Elem (new_name_of_hm_type()) in 
					   let helper = M.add x new_name (M.remove x context) in 
					   let (s1, t1) = implementation_algorithm_w y helper in 
					   (s1, HM_Arrow (substitution_in_type new_name s1, t1)))
	| HM_Let (x, l1, l2) -> (let (s1, t1) = implementation_algorithm_w l1 context in 
						   let new_context = substitution_in_context context s1 in 
						   let helper = M.add x (general t1 new_context) (M.remove x new_context) in 
						   let (s2, t2) = implementation_algorithm_w l2 helper in 
						   (mult_subst s2 s1, t2))
	| HM_App (x, y) -> (let (s1, t1) = implementation_algorithm_w x context in 
					   let (s2, t2) = implementation_algorithm_w y (substitution_in_context context s1) in 
					   let new_name = HM_Elem (new_name_of_hm_type()) in 
					   let s = Hw2_unify.solve_system [from_hm_lambda_to_algebraic_term (substitution_in_type t1 s2), from_hm_lambda_to_algebraic_term (HM_Arrow(t2, new_name))] in 
					   (match s with
					   		| Some solution -> (let cnv_to_hm = convert_list_to_hm solution in 
					   							let cnv_to_map = convert_list_to_map cnv_to_hm empty_map in 
					   							let sub = mult_subst cnv_to_map (mult_subst s2 s1) in 
					   							(sub, substitution_in_type new_name sub))
					   		| None -> failwith "can't solve"));;

let transform_to_cor key value l = (key, value)::l ;;

let algorithm_w lambda_expression = try (let (context, t) = implementation_algorithm_w lambda_expression (return_start_context lambda_expression) in 
											Some (M.fold transform_to_cor context [], t)) 
									with _ -> None;;
