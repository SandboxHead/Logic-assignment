type prop = T | F | L of string | Not of prop | 
		And of (prop*prop) | Or of (prop * prop) |
		Impl of (prop*prop) | Iff of (prop*prop);;

type 'a set = Set of ('a list);;

type ndprooftree = 	  Hyp of (prop set)*prop 
					| InsT of (prop set)*prop
					| InsImpl of (prop set)*prop*ndprooftree
					| ElemImpl of (prop set)*prop*ndprooftree*ndprooftree
					| IntNot of (prop set)*prop*ndprooftree
					| ClassNot of (prop set)*prop*ndprooftree
					| InsAnd of (prop set)*prop*ndprooftree*ndprooftree
					| ElemAndL of (prop set)*prop*ndprooftree
					| ElemAndR of (prop set)*prop*ndprooftree 
					| InsOrL of (prop set)*prop*ndprooftree
					| InsOrR of (prop set)*prop*ndprooftree
					| ElemOr of (prop set)*prop*ndprooftree*ndprooftree*ndprooftree
;;

(* let val x  = match x with 
| T -> true
| _ -> false
;;
 *)
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

let sameset s1 s2 = subset s1 s2 && subset s2 s1;;


let rec length l = match l with
| [] -> 0
| a::l1 -> 1+(length l1)
;;

let len s = match s with
| Set(l) -> length l
;;

let getProp tree = match tree with
| Hyp(_, q) 				-> q
| InsT(__, q) 				-> q
| InsImpl(_, q, _) 			-> q
| ElemImpl(_, q, _, _) 		-> q
| IntNot(_, q, _) 			-> q
| ClassNot(_, q, _) 		-> q
| InsAnd(_, q, _, _) 		-> q
| ElemAndL(_, q, _) 		-> q
| ElemAndR(_, q, _) 		-> q
| InsOrL(_, q, _) 			-> q
| InsOrR(_, q, _) 			-> q
| ElemOr(_, q, _, _, _) 	-> q
;;

let getGamma tree = match tree with
| Hyp(gamma1, q) 				-> gamma1
| InsT(gamma1, q) 				-> gamma1
| InsImpl(gamma1, q, _) 		-> gamma1
| ElemImpl(gamma1, q, _, _) 	-> gamma1
| IntNot(gamma1, q, _) 			-> gamma1
| ClassNot(gamma1, q, _) 		-> gamma1
| InsAnd(gamma1, q, _, _) 		-> gamma1
| ElemAndL(gamma1, q, _) 		-> gamma1
| ElemAndR(gamma1, q, _) 		-> gamma1
| InsOrL(gamma1, q, _) 			-> gamma1
| InsOrR(gamma1, q, _) 			-> gamma1
| ElemOr(gamma1, q, _, _, _) 	-> gamma1
;;


exception Error;;


let rec checkNode tree gamma p = match tree with
| Hyp(gamma1, q) 				-> p=q && sameset gamma gamma1
| InsT(gamma1, q) 				-> p=q && sameset gamma gamma1
| InsImpl(gamma1, q, _) 		-> p=q && sameset gamma gamma1
| ElemImpl(gamma1, q, _, _) 	-> p=q && sameset gamma gamma1
| IntNot(gamma1, q, _) 			-> p=q && sameset gamma gamma1
| ClassNot(gamma1, q, _) 		-> p=q && sameset gamma gamma1
| InsAnd(gamma1, q, _, _) 		-> p=q && sameset gamma gamma1
| ElemAndL(gamma1, q, _) 		-> p=q && sameset gamma gamma1
| ElemAndR(gamma1, q, _) 		-> p=q && sameset gamma gamma1
| InsOrL(gamma1, q, _) 			-> p=q && sameset gamma gamma1
| InsOrR(gamma1, q, _) 			-> p=q && sameset gamma gamma1
| ElemOr(gamma1, q, _, _, _) 	-> p=q && sameset gamma gamma1
;;


exception Normalised;;


let rec find_rpair_temp table = match table with
| Hyp(gamma, p) -> []
| InsT(gamma, p) -> []
| ElemImpl(gamma, p, t1, t2) -> (match t1 with
	| InsImpl(gamma1, q, t3) -> [table]
	| _ -> let x1 = find_rpair_temp t1 in 
		if(List.length x1 = 0) then find_rpair_temp t2 else x1 
) 
| ElemOr(gamma, p, t1, t2, t3) -> (match t1 with
	| InsOrL(_, _, _) | InsOrR(_, _, _) -> [table]
	| _ -> let x1 = find_rpair_temp t1 in 
		(if(List.length x1 = 0) then 
			(let x2 = find_rpair_temp t2 in 
				if(List.length x2 = 0) then find_rpair_temp t3 else x2)
		else x1)
)

| ElemAndL(gamma, p, t1) -> (match t1 with
	| InsAnd(_, _, _, _) -> [table]
	| _ -> find_rpair_temp t1
)
| ElemAndR(gamma, p, t1) -> (match t1 with
	| InsAnd(_, _, _, _) -> [table]
	| _ -> find_rpair_temp t1 
)
| InsImpl(gamma, p, t1) -> find_rpair_temp t1
| InsAnd(gamma, p, t1, t2) -> let x1 = find_rpair_temp t1 in 
	if(List.length x1 = 0) then find_rpair_temp t2 else x1

| InsOrL(gamma, p, t1) -> find_rpair_temp t1
| InsOrR(gamma, p, t1) -> find_rpair_temp t1
| ClassNot(gamma, p, t1) -> find_rpair_temp t1
| IntNot(gamma, p, t1) -> find_rpair_temp t1
;;

let find_rpair table = let x = find_rpair_temp table in (
	match x with
	| [] -> raise Normalised
	| a::_ -> a
)
;;

let rec pad tree delta = match tree with
| Hyp(gamma, p) -> Hyp(union gamma delta, p)
| InsT(gamma, p) -> InsT(union gamma delta, p)
| InsImpl(gamma, p, t1) -> InsImpl(union gamma delta, p, pad t1 delta)
| ElemImpl(gamma, p, t1, t2) -> ElemImpl(union gamma delta, p, pad t1 delta, pad t2 delta)
| IntNot(gamma, p, t1) -> IntNot(union gamma delta, p, pad t1 delta)
| ClassNot(gamma, p, t1) -> ClassNot(union gamma delta, p, pad t1 delta)
| InsAnd(gamma, p, t1, t2) -> InsAnd(union gamma delta, p, pad t1 delta, pad t2 delta)
| ElemAndL(gamma, p, t1) -> ElemAndL(union gamma delta, p, pad t1 delta)
| ElemAndR(gamma, p, t1) -> ElemAndR(union gamma delta, p, pad t1 delta)
| InsOrL(gamma, p, t1) -> InsOrL(union gamma delta, p, pad t1 delta)
| InsOrR(gamma, p, t1) -> InsOrR(union gamma delta, p, pad t1 delta)
| ElemOr(gamma, p, t1, t2, t3) -> ElemOr(union gamma delta, p, pad t1 delta, pad t2 delta, pad t3 delta)
;;


let rec proof_temp p prooflist = match prooflist with
| [] -> raise Error;
| proof::pl -> if(getProp proof = p) then proof else proof_temp p pl
;;

let rec graft_temp tree prooflist delta gamma = match tree with

| Hyp(delta1, p) -> if(member delta p) then let x = try Some(pad (proof_temp p prooflist) (difference delta1 delta)) with Error -> None in
					(match x with 
						| Some(t) -> t
						| None -> Hyp(union gamma (difference delta1 delta), p)
					)
					else Hyp(union gamma (difference delta1 delta), p)

| Hyp(delta1, p) -> if(member delta p) then pad (proof_temp p prooflist) (difference delta1 delta)
					else Hyp(union gamma (difference delta1 delta), p)
| InsT(delta1, p) -> InsT(union gamma (difference delta1 delta), p)
| InsImpl(delta1, p, t1) -> InsImpl(union gamma (difference delta1 delta), p, graft_temp t1 prooflist delta gamma)
| ElemImpl(delta1, p, t1, t2) -> ElemImpl(union gamma (difference delta1 delta), p, graft_temp t1 prooflist delta gamma, graft_temp t2 prooflist delta gamma)
| IntNot(delta1, p, t1) -> IntNot(union gamma (difference delta1 delta), p, graft_temp t1 prooflist delta gamma)
| ClassNot(delta1, p, t1) -> ClassNot(union gamma (difference delta1 delta), p, graft_temp t1 prooflist delta gamma)
| InsAnd(delta1, p, t1, t2) -> InsAnd(union gamma (difference delta1 delta), p, graft_temp t1 prooflist delta gamma, graft_temp t2 prooflist delta gamma)
| ElemAndL(delta1, p, t1) -> ElemAndL(union gamma (difference delta1 delta), p, graft_temp t1 prooflist delta gamma)
| ElemAndR(delta1, p, t1) -> ElemAndR(union gamma (difference delta1 delta), p, graft_temp t1 prooflist delta gamma)
| InsOrL(delta1, p, t1) -> InsOrL(union gamma (difference delta1 delta), p, graft_temp t1 prooflist delta gamma)
| InsOrR(delta1, p, t1) -> InsOrR(union gamma (difference delta1 delta), p, graft_temp t1 prooflist delta gamma)
| ElemOr(delta1, p, t1, t2, t3) -> ElemOr(union gamma (difference delta1 delta), p, graft_temp t1 prooflist delta gamma, graft_temp t2 prooflist delta gamma, graft_temp t3 prooflist delta gamma)
;;

let graft tree prooflist = match prooflist with
| [] -> graft_temp tree prooflist (getGamma tree) (Set [])
| p1::_ -> graft_temp tree prooflist (getGamma tree) (getGamma p1)
;;
exception Err;;

let simplify1 tree = match tree with
| ElemImpl(gamma, p, t1, t2) -> (match t1 with
	| InsImpl(gamma1, q, t3) -> graft t3 [t2]
	| _ -> raise Err
)
| ElemOr(gamma, p, t1, t2, t3) -> (match t1 with
	| InsOrL(gamma1, q, t4) -> graft t4 [t2]
	| InsOrR(gamma1, q, t4) -> graft t4 [t3]
	| _ -> raise Err
)
| ElemAndL(gamma, p, t1) -> (match t1 with
	| InsAnd(gamma1, q, t2, t3) -> t2
	| _ -> raise Err
)
| ElemAndR(gamma, p, t1) -> (match t1 with
	| InsAnd(gamma1, q, t2, t3) -> t3
	| _ -> raise Err
)
| _ -> raise Err
;;

let rec normalise tree = match tree with
| Hyp(gamma, p) -> Hyp(gamma, p)
| InsT(gamma, p) -> tree
| InsImpl(gamma, p, t1) -> tree
| ElemImpl(gamma, p, t1, t2) -> (match t1 with
	| InsImpl(gamma1, q, t3) -> normalise (graft t3 [t2])
	| _ -> ElemImpl(gamma, p, normalise t1, normalise t2)
) 
| IntNot(gamma, p, t1) -> IntNot(gamma, p, normalise t1)
| ClassNot(gamma, p, t1) -> ClassNot(gamma, p, normalise t1)
| InsAnd(gamma, p, t1, t2) -> InsAnd(gamma, p, normalise t1, normalise t2)
| ElemAndL(gamma, p, t1) -> (match t1 with
	| InsAnd(gamma1, q, t2, t3) -> normalise t2
	| _ -> raise Error
)
| ElemAndR(gamma, p, t1) -> (match t1 with
	| InsAnd(gamma1, q, t2, t3) -> normalise t3
	| _ -> raise Error
)
| InsOrL(gamma, p, t1) -> InsOrL(gamma, p, normalise t1)
| InsOrR(gamma, p, t1) -> InsOrR(gamma, p, normalise t1)
| ElemOr(gamma, p, t1, t2, t3) -> (match t1 with
	| InsOrL(gamma1, q, t4) -> normalise (graft t4 [t2])
	| InsOrR(gamma1, q, t4) -> normalise (graft t4 [t3])
	| _ -> raise Error
)
;;

(* Example *)
let p = L "p";;
let q = L "q";;

let gamma = Set [p; q];;
let anded = And(p, q);;

let e1 = ElemAndL(gamma, p, InsAnd(gamma, anded, Hyp(gamma, p), Hyp(gamma, q)));;

find_rpair e1;;
simplify1 e1;;
normalise e1;;

(* Example 2 *)

let e2 = ElemAndR(gamma, q, InsAnd(gamma, anded, Hyp(gamma, p), Hyp(gamma, q)));;
find_rpair e2;;
simplify1 e2;;
normalise e2;;


(* Example 3 *)
let e4 = ElemImpl(gamma, q, InsImpl(gamma, Impl(p, q), Hyp(gamma, q)), Hyp(gamma, p));;
simplify1 e4;;
normalise e4;;

(* Example 4 *)

let e3 = ElemImpl(gamma, q, InsImpl(gamma, Impl(p, q), e2), e1);;
simplify1 e3;;
normalise e3;;

(* Example 5 *)

let gamma1 = Set [F; p];;
let gamma2 = Set [F];;

let part1 = IntNot(gamma1, q, Hyp(gamma1, F));;
let part2 = IntNot(gamma2, p, Hyp(gamma2, F));;

let part3 = InsImpl(gamma2, Impl(p, q), part1);;
let part4 = ElemImpl(gamma2, q, part3, part2);;

