type prop = L of string | Impl of prop*prop | Not of prop;;

type 'a set = Set of ('a list);;

type hprooftree = Leaf of (prop set)*prop 
                | Node of (prop set)*prop*hprooftree*hprooftree;;




(* Helpful functions *)

let rec map f l = match l with
| [] ->[]
| x::xs -> (f x)::(map f xs);;  

let rec foldl f e l = match l with
| [] -> e
| x::xs -> foldl f (f e x) xs;;



(* Set Operations *)
let rec contains l a = match l with
| [] -> false
| b::l1 -> (a = b) || (contains l1 a)
;;

let member s a = match s with
| Set(l) -> contains l a
;;

let rec unite l1 l2 = match l1 with
| [] -> l2
| a::l -> (if (contains l2 a) then (unite l l2) else (unite l (a::l2)))
;;

let union s1 s2 = match s1, s2 with
| (Set(l1), Set(l2)) -> Set(unite l1 l2)
;;


let rec intersect l1 l2 l3 = match l1 with
| [] -> l3
| a::l -> (if (contains l2 a) then (intersect l l2 (a::l3)) 
			else (intersect l l2 l3))
;;

let intersection s1 s2 = match s1, s2 with
| (Set(l1), Set(l2)) -> Set(intersect l1 l2 [])
;;

let rec differ l1 l2 l3 = match l1 with
| [] -> l3
| a::l -> (if (contains l2 a) then (differ l l2 l3) 
			else (differ l l2 (a::l3)))
;;

let difference s1 s2 = match s1, s2 with
| (Set(l1), Set(l2)) -> Set(differ l1 l2 [])
;;

let annd a b = a && b;;


let lsubset l1 l2 =
 	let arr = map (contains l2) l1 in 
 	foldl annd true arr
;;

let subset s1 s2 = match s1, s2 with
| (Set(l1), Set(l2)) -> lsubset l1 l2
;;

let rec length l = match l with
| [] -> 0
| a::l1 -> 1+(length l1)
;;

let len s = match s with
| Set(l) -> length l
;;

(* Set operations ended *)

let k = Impl(L "p", Impl(L "q", L "p"));;

let s1 = Impl(L "p", Impl(L "q", L "r"));;

let s2 = Impl(Impl(L "p", L "q"), Impl(L "p", L "r"));;

let s = Impl(s1, s2);;

let r1 = Impl(Not(L "p"), Not(L "q"));;

let r2 = Impl(Impl(Not(L "p"), L "q"), L "p");;

let r = Impl(r1, r2);;


let form_k p q = Impl(p, Impl(q, p));;

let form_s p q r = let s1 = Impl(p, Impl(q, r)) in let s2 = Impl(Impl(p, q), Impl(p, r)) in Impl(s1, s2);;


let is_K p = match p with
| Impl(p1, Impl(p2, p3)) -> p1 = p3
| _ -> false
;;

let is_S p = match p with
| Impl(Impl(p1, Impl(p2, p3)), Impl(Impl(p4, p5), Impl(p6, p7))) -> (p1 = p4) && (p4 = p6) && (p2 = p5) && (p3 = p7)
| _ -> false
;;

let is_R p = match p with
| Impl(Impl(Not p1, Not p2), Impl(Impl(Not p3, p4), p5)) -> (p1 = p3) && (p3 = p5) && (p2 = p4)
| _ -> false
;;

let rec is_subset g1 g2 = match g1 with
| [] -> true
| a::g -> contains g2 a && is_subset g2 g
;;

let is_equal_list g1 g2 = is_subset g1 g2 && is_subset g2 g1
;;

exception Error;;


let check_valid_node n = match n with
| Node(gamma, p, Leaf(gamma1, Impl(p1, p2)), Leaf(gamma2, p3)) 				-> (p1 = p3) && (p = p2) && subset gamma gamma1 && subset gamma1 gamma2 && subset gamma2 gamma
| Node(gamma, p, Node(gamma1, Impl(p1, p2), _, _), Node(gamma2, p3, _, _))  -> (p1 = p3) && (p = p2) && subset gamma gamma1 && subset gamma1 gamma2 && subset gamma2 gamma
| Node(gamma, p, Leaf(gamma1, Impl(p1, p2)), Node(gamma2, p3, _, _)) 		-> (p1 = p3) && (p = p2) && subset gamma gamma1 && subset gamma1 gamma2 && subset gamma2 gamma
| Node(gamma, p, Node(gamma1, Impl(p1, p2), _, _), Leaf(gamma2, p3)) 		-> (p1 = p3) && (p = p2) && subset gamma gamma1 && subset gamma1 gamma2 && subset gamma2 gamma
| _ -> raise Error
;;

let rec valid_hprooftree tree = match tree with
| Leaf(gamma, p) 			-> member gamma p || is_K p || is_S p || is_R p
| Node(gamma, p, t1, t2) 	-> check_valid_node tree && valid_hprooftree t1 && valid_hprooftree t2
;;



let rec pad tree delta = match tree with
| Leaf(gamma, p) 			-> Leaf(union gamma delta, p)
| Node(gamma, p, t1, t2) 	-> Node(union gamma delta, p, pad t1 delta, pad t2 delta)
;;


let rec smallest_delta tree = match tree with
| Leaf(gamma, p) 			-> if(is_K p || is_R p || is_S p) then Set([]) else Set([p])
| Node(gamma, p, t1, t2) 	-> union (smallest_delta t1) (smallest_delta t2)
;;

let rec update_delta tree delta = match tree with
| Leaf(gamma, p) 			-> Leaf(delta, p)
| Node(gamma, p, t1, t2) 	-> Node(delta, p, update_delta t1 delta, update_delta t2 delta)
;;

let prune tree = let delta = smallest_delta tree in update_delta tree delta
;;

exception NotInside;;

let rec search_prop p treeList = match treeList with
| [] -> raise NotInside
| (Leaf(gamma, p1))::tl 			-> if(p1 = p) then Leaf(gamma, p1) else search_prop p tl
| (Node(gamma, p1, t1, t2))::tl 	-> if(p1 = p) then Node(gamma, p1, t1, t2) else search_prop p tl
;;


let rec graft_temp tree proofs = match tree with
| Leaf(delta, p) -> if(is_K p || is_R p || is_S p) then tree else search_prop p proofs
| Node(delta, p, t1, t2) -> Node(delta, p, graft_temp t1 proofs, graft_temp t2 proofs)
;;

let rec graft tree proofs = let temp = graft_temp tree proofs in match proofs with
| [] -> temp
| (Node(delta, p1, t1, t2))::_ -> update_delta temp delta
| (Leaf(delta, p1))::_ -> update_delta temp delta
;;

let base_proof gamma p q = Node(gamma, Impl(p, q), Leaf(gamma, form_k q p), Leaf(gamma, q));;

let p_impl_p gamma p = 	let k1 = form_k p (Impl(p, p)) in
						let s1 = form_s p (Impl(p, p)) p in 
						let k2 = form_k p p in 
						let z1 = Node(gamma, Impl(k2, Impl(p, p)), Leaf(gamma, s1), Leaf(gamma, k1)) in 
						Node(gamma, Impl(p, p), z1, Leaf(gamma, k2))
;;


let rec deduction tree p gamma = match tree with
| Leaf(gamma1, q) -> if(p = q) then p_impl_p gamma p else base_proof gamma p q
| Node(gamma1, q, t1, t2) -> (match t1 with
	| Leaf(gamma2, Impl(r, q2)) | Node(gamma2, Impl(r, q2), _, _) -> 
							let left = Node(gamma, Impl(Impl(p, r), Impl(p, q)), Leaf(gamma, form_s p r q), deduction t1 p gamma) 
							in let right = deduction t2 p gamma 
							in Node(gamma, Impl(p, q), left, right)
    | _ -> raise Error
	)
;;


let rec dedthm tree p = match tree with
| Leaf(gamma, a) | Node(gamma, a, _, _) -> let gammadash = difference gamma (Set [p]) in deduction tree p gammadash;;

(* Example *)

let gamma = Set []
let p1 = L "p";;
let q1 = Impl(p1, p1);;
let r1 = p1;;
let k1 = form_k p1 q1;;
let s1 = form_s p1 q1 r1;;
let rem1 = Impl(Impl(p1, q1), Impl(p1, r1))

let h1 = Node(gamma, rem1, Leaf (gamma, s1), Leaf (gamma, k1));;
let k2 = form_k p1 p1;;

let h2 = Node(gamma, Impl(p1, p1), h1, Leaf(gamma, k2));;

valid_hprooftree h1;;
valid_hprooftree h2;;

let s1 = Set [L "q"];;

let new_h2 = pad h2 s1;;

prune new_h2;;

let gamma2 = Set [rem1];;
let h3 = Node(gamma2, Impl(p1, p1), Leaf(gamma2, rem1), Leaf(gamma2, k2));;

let proofl = [h1];;
graft h3 proofl;;

valid_hprooftree (dedthm h3 rem1);;

let p1 = L "p1";;
let q1 = L "q1";;
let p2 = L "p2";;

(* let q1 = Impl(p, q);; *)
let gamma = Set [p2; Impl(p2, Impl(p1, q1)); L "k"];;

let h5 = Node(gamma, Impl(p1, q1), Leaf(gamma, Impl(p2, Impl(p1, q1)), Leaf(gamma, p2)));;
