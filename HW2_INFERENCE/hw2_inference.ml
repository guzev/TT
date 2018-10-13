open Hw1;;
open Hw2_unify;;
open Hw1_reduction;;

module M = Map.Make(String);;
module S = Set.Make(String);;

let empty_map = M.empty;;

type simp_type = S_Elem of string 
			   | S_Arrow of simp_type * simp_type ;;

type hm_lambda = HM_Var of string 
			   | HM_Abs of string * lambda 
			   | HM_App of lambda * lambda 
			   | HM_Let of string * lambda * lambda ;;

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
