type prop = T | F | L of string | Not of prop | 
		And of (prop*prop) | Or of (prop * prop) |
		Impl of (prop*prop) | Iff of (prop*prop);;

type 'a set = Set of ('a list);;
type node = Node of (prop*bool) | NULL;;
type tableau = Leaf of node*int*((string*bool) list) | Alpha of node*tableau | Beta of node*tableau*tableau;;

type assig = Sat of (((string*bool) list) list) | Fal of (((string*bool) list) list);;


(* Helpful functions *)




(* Main Work *)

let rec contains_str l a = match l with
| [] -> false
| (p, q)::l1 -> if (p = a) then true else contains_str l1 a;
;;

exception InvalidError;;

let rec find_val l a = match l with
| [] -> false
| (p, q)::l1 -> if (p = a) then q else find_val l1 a;
;;

let rec contains_inside rho x = match rho with
| [] -> false
| x1::rho1 -> (x = x1) || contains_inside rho1 x
;;

let rec map f l = match l with
| [] ->	[]
| x::xs -> (f x)::(map f xs)
;;


let rec is_really_equal rho1 rho2 = match rho1 with
| [] -> true
| a::rho -> (contains_inside rho2 a) && (is_really_equal rho rho2)
;;

let rec contains_l a l = match l with
| [] -> false
| b::l1 -> (a = b) || (contains_l a l1)
;;

let rec remove a l = match l with
| [] -> l
| b::l1 -> if(a = b) then l1 else b::(remove a l1)
;;

let return_first remaining = match remaining with
| a::r -> a
;;


let is_equal rho1 rho2 = (is_really_equal rho1 rho2) && (is_really_equal rho2 rho1);; 


let rec select_node table remaining = match table with
| Leaf(n, x, rho) -> return_first (remove n remaining)
| Alpha(Node(p, b), t1) -> (let remain = (remove (Node(p, b)) remaining)in 
						(match p with
							| And(p1, p2) -> select_node t1 ((Node(p1, true))::(Node(p2, true))::remain)
							| Or(p1, p2) -> select_node t1 ((Node(p1, false))::(Node(p2, false))::remain)
							| Impl(p1, p2) -> select_node t1 ((Node(p1, true))::(Node(p2, false))::remain)
							| Not(p1) -> select_node t1 ((Node(p1, not b))::remain)
							| T -> select_node t1 remain
							| F -> select_node t1 remain
							| L(s) -> select_node t1 remain
						))
| Beta(Node(p, b), t1, t2) -> (let remain = (remove (Node(p, b)) remaining) in 
							(match p with
								| And(p1, p2) -> if (select_node t1 ((Node(p1, true))::remain) = NULL) then select_node t2 ((Node(p2, true))::remain)
												 else select_node t1 ((Node(p1, true))::remain)
								| Or(p1, p2) -> if (select_node t1 ((Node(p1, false))::remain) = NULL) then select_node t2 ((Node(p2, false))::remain)
												 else select_node t1 ((Node(p1, false))::remain)

								| Impl(p1, p2) -> if (select_node t1 ((Node(p1, false))::remain) = NULL) then select_node t2 ((Node(p2, true))::remain)
												 else select_node t1 ((Node(p1, false))::remain)
								| Iff(p1, p2) -> if(b = true) then
													if(select_node t1 ((Node(p1, true))::(Node(p2, true))::remain) = NULL) then select_node t1 ((Node(p1, false))::(Node(p2, false))::remain)
													else select_node t1 ((Node(p1, true))::(Node(p2, true))::remain)
												else 
													if(select_node t1 ((Node(p1, false))::(Node(p2, true))::remain) = NULL) then select_node t1 ((Node(p1, true))::(Node(p2, false))::remain)
													else select_node t1 ((Node(p1, false))::(Node(p2, true))::remain)

							));;


let rec contrad_path table remaining = match table with
| Leaf(Node(p, b), x, rho) -> if(contains_l (Node(p, not b)) remaining ) then Leaf(Node(p, b), -1, rho) 
							  else Leaf(Node(p, b), x, rho)

| Alpha(Node(p, b), t1) -> (let remain = (remove (Node(p, b)) remaining)in 
						(match p with
							| And(p1, p2) -> Alpha(Node(p, b), contrad_path t1 ((Node(p1, true))::(Node(p2, true))::remain))
							| Or(p1, p2) -> Alpha(Node(p, b), contrad_path t1 ((Node(p1, false))::(Node(p2, false))::remain))
							| Impl(p1, p2) -> Alpha(Node(p, b), contrad_path t1 ((Node(p1, true))::(Node(p2, false))::remain))
							| Not(p1) -> Alpha(Node(p, b), contrad_path t1 ((Node(p1, not b))::remain))
							| T -> Alpha(Node(p, b), contrad_path t1 remain)
							| F -> Alpha(Node(p, b), contrad_path t1 remain)
							| L(s) -> Alpha(Node(p, b), contrad_path t1 remain)
						))
| Beta(Node(p, b), t1, t2) -> (let remain = (remove (Node(p, b)) remaining) in 
							(match p with
								| And(p1, p2) -> Beta(Node(p, b), contrad_path t1 ((Node(p1, true))::remain), contrad_path t2 ((Node(p2, true))::remain))
								| Or(p1, p2) -> Beta(Node(p, b), contrad_path t1 ((Node(p1, false))::remain), contrad_path t2 ((Node(p2, false))::remain))

								| Impl(p1, p2) -> Beta(Node(p, b), contrad_path t1 ((Node(p1, false))::remain), contrad_path t2 ((Node(p2, true))::remain))

								| Iff(p1, p2) -> if(b = true) then
													Beta(Node(p, b), contrad_path t1 ((Node(p1, true))::(Node(p2, true))::remain), contrad_path t2 ((Node(p2, false))::(Node(p1, false))::remain))
												else 
													Beta(Node(p, b), contrad_path t1 ((Node(p1, false))::(Node(p2, true))::remain), contrad_path t2 ((Node(p2, true))::(Node(p1, false))::remain))
												
							));;



let rec is_valid tree rho remaining = match tree with
| Leaf(Node(p, b), x, rho1) -> if (contains_l (Node(p, b)) remaining) then 
	(let remain = (remove (Node(p, b)) remaining) in
	(match p with
	| L(s) -> if(contains_str rho s) then 
				(
					if(find_val rho s != b) then 
					(
						if(x != -1) then false
						else (is_equal rho1 rho)
					)
					else 
					(
						if(x != 1) then false
						else (is_equal rho1 rho) 
					)
				)
			else
			(
				if(x != 1) then false
				else is_equal ((s, b)::rho) rho1
			)
	| T -> if(b = true) then 
			(
				if(x != 1) then false
				else (is_equal rho1 rho) 
			)
			else
			(
				if(x != -1) then false
				else (is_equal rho1 rho) 
			)
	| F -> if(b = false) then 
			(
				if(x != 1) then false
				else (is_equal rho1 rho) 
			)
			else
			(
				if(x != -1) then false
				else (is_equal rho1 rho) 
			)
	| And(p1, p2) -> if(x != 0) then false
					 else (is_equal rho1 rho)
	| Or(p1, p2) -> if(x != 0) then false
					 else (is_equal rho1 rho)
	| Impl(p1, p2) -> if(x != 0) then false
					 else (is_equal rho1 rho)
	| Iff(p1, p2) -> if(x != 0) then false
					 else (is_equal rho1 rho)
	| Not(p1) -> if(x != 0) then false
					 else (is_equal rho1 rho)
	)
	)
	else false

| Alpha(Node(p, q), t1) -> if (contains_l (Node(p, q)) remaining) then 
	(let remain = (remove (Node(p, q)) remaining) in
	(	match p with
		| And(p1, p2) -> if(q=true) then (is_valid t1 rho ((Node(p1, true))::(Node(p2, true))::remain))
					 else false

		| Or(p1, p2) -> if(q=false) then (is_valid t1 rho ((Node(p1, false))::(Node(p2, false))::remain))
					 else false

		| Impl(p1, p2) -> if(q=false) then (is_valid t1 rho ((Node(p1, true))::(Node(p2, false))::remain))
					 else false

		| Not(p1) -> is_valid t1 rho ((Node(p1, not q))::remain)
		| T -> if (q = false) then false
				else is_valid t1 rho remaining
		| F -> if (q = true) then false
				else is_valid t1 rho remaining
		| L(s) -> if (contains_str rho s) then (is_valid (Leaf(Node(L(s), q), 1, rho)) rho remaining) && (is_valid t1 rho remaining)
				  else (is_valid (Leaf(Node(L(s), q), 1, (s, q)::rho)) rho remaining) && (is_valid t1 ((s, q)::rho) remaining)

		| _ -> false
	) 
	)
					

	else false


| Beta(Node(p, q), t1, t2) -> if(contains_l (Node(p, q)) remaining) then 
	(let remain = (remove (Node(p, q)) remaining) in
		(match p with 
			| And(p1, p2) -> if(q=false) then ((is_valid t1 rho ((Node(p1, false))::remain)) && (is_valid t2 rho ((Node(p2, false))::remain)))
						 	else false
			| Or(p1, p2) -> if(q=true) then ((is_valid t1 rho ((Node(p1, true))::remain)) && (is_valid t2 rho ((Node(p2, true))::remain)))
						 	else false
			| Impl(p1, p2) -> if(q=true) then ((is_valid t1 rho ((Node(p1, false))::remain)) && (is_valid t2 rho ((Node(p2, true))::remain)))		  
						 	else false
		 	| Iff(p1, p2) -> if(q=true) then (is_valid t1 rho ((Node(p1, true))::(Node(p2, true))::remain)) && (is_valid t2 rho ((Node(p1, false))::(Node(p2, false))::remain))
					 		else (is_valid t1 rho ((Node(p1, false))::(Node(p2, true))::remain)) && (is_valid t2 rho ((Node(p1, true))::(Node(p2, false))::remain))
			| _ -> false
		)			
	)
					else false

;;



let valid_tableau table = match table with
| Alpha(n, a) -> is_valid table [] [n]
| Beta(n, a, b) -> is_valid table [] [n]
| Leaf(n, a, b) -> is_valid table [] [n]
;;



let rec step_develop tree remaining = match tree with
| Leaf(Node(p, b), 0, rho) -> (match p with  
	| T -> if(b = true) then match remaining with
				| [] -> Leaf(Node(p, b), 1, rho)
				| x1::remain -> Alpha(Node(p, b), step_develop (Leaf(x1, 0, rho)) remain)
			else Leaf(Node(p, b), -1, rho)

	| F -> if(b = false) then match remaining with
				| [] -> Leaf(Node(p, b), 1, rho)
				| x1::remain -> Alpha(Node(p, b), step_develop (Leaf(x1, 0, rho)) remain)
			else Leaf(Node(p, b), -1, rho)

	| L(s) -> if (contains_str rho s) then 
				(
					if(find_val rho s != b) then Leaf(Node(p, b), -1, rho)
					else  match remaining with
						| [] -> Leaf(Node(p, b), 1, rho)
						| x1::remain -> Alpha(Node(p, b), step_develop (Leaf(x1, 0, rho)) remain)
				)
			else 
			(
				match remaining with
				| [] -> Leaf(Node(p, b), 1, (s, b)::rho)
				| x1::remain -> Alpha(Node(p, b), step_develop (Leaf(x1, 0, (s, b)::rho)) remain)
			)

	| And(p1, p2) -> if(b=true) then Alpha(Node(p, b), step_develop (Leaf(Node(p1, true), 0, rho)) ((Node(p2, true))::remaining))
					 else Beta(Node(p, b), step_develop (Leaf(Node(p1, false), 0, rho)) remaining, step_develop (Leaf(Node(p2, false), 0, rho)) remaining)

	| Not(p1) -> Alpha(Node(p, b), step_develop (Leaf(Node(p1, not b), 0, rho)) remaining)

	| Or(p1, p2) -> if(b=false) then Alpha(Node(p, b), step_develop (Leaf(Node(p1, false), 0, rho)) ((Node(p2, false))::remaining))
				 	else Beta(Node(p, b), step_develop (Leaf(Node(p1, true), 0, rho)) remaining, step_develop (Leaf(Node(p2, true), 0, rho)) remaining)

	| Impl(p1, p2) -> if(b=false) then Alpha(Node(p, b), step_develop (Leaf(Node(p1, true), 0, rho)) ((Node(p2, false))::remaining))
					 else Beta(Node(p, b), step_develop (Leaf(Node(p1, false), 0, rho)) remaining, step_develop (Leaf(Node(p2, true), 0, rho)) remaining)
	| Iff(p1, p2) -> if(b=false) then Beta(Node(p, b), step_develop (Leaf(Node(p1, false), 0, rho)) ((Node(p2, true))::remaining), step_develop (Leaf(Node(p1, true), 0, rho)) ((Node(p2, false))::remaining))
					 else Beta(Node(p, b), step_develop (Leaf(Node(p1, true), 0, rho)) ((Node(p2, true))::remaining), step_develop (Leaf(Node(p1, false), 0, rho)) ((Node(p2, false))::remaining))
)
| _ -> raise InvalidError
;;

let check_tautology p = step_develop (Leaf(Node(p, false), 0, [])) [] ;;

let check_contradiction p = step_develop (Leaf(Node(p, true), 0, [])) [];;

let rec assignments table out = match table with
| Leaf(n, 1, rho) -> (rho)::out
| Alpha(_, t) -> assignments t out
| Beta(_, t1, t2) -> let x = assignments t1 out in assignments t2 x
| _ -> out
;;
	

let find_assignments n = match n with 
| Node(a, true) -> [Sat(assignments (step_develop (Leaf(n, 0, [])) []) []); Fal(assignments (step_develop (Leaf(Node(a, false), 0, [])) []) [])]
| Node(a, false) -> [Sat(assignments (step_develop (Leaf(n, 0, [])) []) []); Fal(assignments (step_develop (Leaf(Node(a, true), 0, [])) []) [])]
;;



let p1 = And(T, F);;
let p2 = And(T, T);;
let p3 = Or(T, F);;
let p4 = Or(F, F);;
let p5 = Impl(T, F);;
let p6 = Impl(F, T);;

let p7 = Or(T, L "a");;
let p8 = And(F, L "b");;
let p9 = Impl(F, L "c");;
let p10 = Iff(T, L "d");;

let p11 = Impl(p1, p2);;
let p12 = Not(Iff(p3, p4));;

let p13 = Iff(p10, p9);;

let p14 = Not(And(p7, p8));;
let p15 = Iff(Or(p7, p8), p9);;
let p16 = Impl(Iff(p10, p9), p2);;
let p17 = Not(And(Iff(p7, p8), Or(p8, p10)));;

let p18 = And(And(Or(L "a", L "b"), And(T, L "c")), T);;


let t1 = check_tautology p1;;
let t2 = check_tautology p2;;
let t3 = check_tautology p3;;
let t4 = check_tautology p4;;
let t5 = check_tautology p5;;
let t6 = check_tautology p6;;
let t7 = check_tautology p7;;
let t8 = check_tautology p8;;
let t9 = check_tautology p9;;
let t10 = check_tautology p10;;
let t11 = check_tautology p11;;
let t12 = check_tautology p12;;
let t13 = check_tautology p13;;
let t14 = check_tautology p14;;
let t15 = check_tautology p15;;
let t16 = check_tautology p16;;
let t17 = check_tautology p17;;
let t18 = check_tautology p18;;


let t2 = Alpha(Node(And(T, F), false), Leaf(Node(L "nothing", false), 1, []));;
