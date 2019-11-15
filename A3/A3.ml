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

let rec valid_ndprooftree tree = match tree with
| Hyp(gamma, p) -> member gamma p
| InsT(gamma, p) -> p=T
| InsImpl(gamma, Impl(p, q), t1) ->  checkNode t1 (union gamma (Set [p])) q 
									&& valid_ndprooftree t1 
| ElemImpl(gamma, q, t1, t2) -> checkNode t1 gamma (Impl(getProp t2, q)) 
								&& valid_ndprooftree t1 
								&& valid_ndprooftree t2
| IntNot(gamma, p, t1) -> checkNode t1 gamma F && valid_ndprooftree t1
| ClassNot(gamma, p, t1) -> checkNode t1 (union gamma (Set [Not(p)])) F
							 && valid_ndprooftree t1
| InsAnd(gamma, And(p, q), t1, t2) -> checkNode t1 gamma p 
										&& checkNode t2 gamma q
										&& valid_ndprooftree t1 
										&& valid_ndprooftree t2
| ElemAndL(gamma, p, t1) -> (match getProp t1 with 
		| And(p1, q1) -> (p1 = p) 
						&& checkNode t1 gamma (And(p1, q1)) 
						&& valid_ndprooftree t1
		| _ -> false
	)
| ElemAndR(gamma, q, t1) -> (match getProp t1 with 
		| And(p1, q1) -> (q1 = q) 
						&& checkNode t1 gamma (And(p1, q1))
						&& valid_ndprooftree t1
		| _ -> false
	)
| InsOrL(gamma, Or(p, q), t1) -> checkNode t1 gamma p 
								&& valid_ndprooftree t1
| InsOrR(gamma, Or(p, q), t1) -> checkNode t1 gamma q 
								&& valid_ndprooftree t1
| ElemOr(gamma, r, t1, t2, t3) -> (match getProp t1 with
		| Or(p, q) -> checkNode t1 gamma (Or(p, q))
					&& checkNode t2 (union gamma (Set [p])) r
					&& checkNode t3 (union gamma (Set [q])) r
					&& valid_ndprooftree t1
					&& valid_ndprooftree t2
					&& valid_ndprooftree t3
		| _ -> false
	)
| _ -> false
;;

exception Error;;

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

let rec prune_temp tree = match tree with
| Hyp(gamma, p) -> Set [p]
| InsT(gamma, p) -> Set []
| InsImpl(gamma, p, t1) -> prune_temp t1
| ElemImpl(gamma, p, t1, t2) -> union (prune_temp t1) (prune_temp t2)
| IntNot(gamma, p, t1) -> prune_temp t1
| ClassNot(gamma, p, t1) -> prune_temp t1
| InsAnd(gamma, p, t1, t2) -> union (prune_temp t1) (prune_temp t2)
| ElemAndL(gamma, p, t1) -> prune_temp t1
| ElemAndR(gamma, p, t1) -> prune_temp t1
| InsOrL(gamma, p, t1) -> prune_temp t1
| InsOrR(gamma, p, t1) -> prune_temp t1
| ElemOr(gamma, p, t1, t2, t3) -> union (union (prune_temp t1) (prune_temp t2)) (prune_temp t3)
;;

let rec replace_gamma tree delta = match tree with
| Hyp(gamma, p) -> Hyp(delta, p)
| InsT(gamma, p) -> InsT(delta, p)
| InsImpl(gamma, Impl(p, q), t1) -> InsImpl(delta, Impl(p, q), replace_gamma t1 (union delta (Set [p])))
| ElemImpl(gamma, q, t1, t2) -> ElemImpl(delta, q, replace_gamma t1 delta, replace_gamma t2 delta)
| IntNot(gamma, p, t1) -> IntNot(delta, p, replace_gamma t1 delta)
| ClassNot(gamma, p, t1) -> ClassNot(delta, p, replace_gamma t1 (union delta (Set [Not p])))
| InsAnd(gamma, p, t1, t2) -> InsAnd(delta, p, replace_gamma t1 delta, replace_gamma t2 delta)
| ElemAndL(gamma, p, t1) -> ElemAndL(delta, p, replace_gamma t1 delta)
| ElemAndR(gamma, p, t1) -> ElemAndR(delta, p, replace_gamma t1 delta)
| InsOrL(gamma, p, t1) -> InsOrL(delta, p, replace_gamma t1 delta)
| InsOrR(gamma, p, t1) -> InsOrR(delta, p, replace_gamma t1 delta)
| ElemOr(gamma, r, t1, t2, t3) -> let x = getProp t1 in (match x with
			| Or(p, q) -> ElemOr(gamma, r, replace_gamma t1 delta, replace_gamma t2 (union delta (Set [p])), replace_gamma t3 (union delta (Set [q])))
			| _ -> raise Error
		)
;;


let prune tree = let delta = intersection (prune_temp tree) (getGamma tree) in replace_gamma tree delta;;



exception Error;;

let rec proof_temp p prooflist = match prooflist with
| [] -> raise Error;
| proof::pl -> if(getProp proof = p) then proof else proof_temp p pl
;;

let rec graft_temp tree prooflist delta gamma = match tree with
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




(* Test Case 1 - Hyp, ImpInt*)

let a = InsImpl(Set [] , Impl(L "x", L "x"), Hyp(Set [L "x"], L "x"));;
valid_ndprooftree a;;
let b = pad a (Set [L("y")]);;

valid_ndprooftree b;;
let c = prune b;;
valid_ndprooftree c;;

(* Test Case 2 - ImpEli, OrEli*)

let a = ElemImpl(Set [L "y"; Impl(L "y", L "x")], L "x", Hyp(Set [L "y"; Impl(L "y", L "x")], Impl(L "y", L "x")), Hyp(Set [L "y"; Impl(L "y", L "x")], L "y"));;

valid_ndprooftree a;;
let b = pad a (Set [L("z")]);;
valid_ndprooftree b;;
let c = prune b;;
valid_ndprooftree c;;
let gamma = Set [Or(L("p"),L("q")); L("p"); L("q"); Impl(L("p"), L("y")); Impl(L("q"), L("y")); Impl(L("p"), L("x"))];;
let gr = ElemOr(gamma, L("y") , Hyp(gamma, Or(L("p"),L("q"))), ElemImpl(gamma, L("y"), Hyp(gamma, Impl(L("p"), L("y"))), Hyp(gamma, L("p"))), ElemImpl(gamma, L("y"), Hyp(gamma, Impl(L("q"), L("y"))), Hyp(gamma, L("q"))));;

valid_ndprooftree gr;;

let gr2 = InsImpl(gamma, Impl(L "y", L "x"), ElemImpl(union (Set [L "y"]) gamma, L "x", Hyp(union (Set [L "y"]) gamma, Impl(L "p", L "x")), Hyp(union (Set [L "y"]) gamma, L "p")));;

let d = graft a [gr; gr2];;

valid_ndprooftree d;;

(* Test Case 3 - AndInt, OrIntL, Tr *)

let gamma = Set [L("p");L("q")];;

let a = InsAnd(gamma, And(Or(L "p", L "q"), And(T, L "q")), InsOrL(gamma, Or(L "p", L "q"), Hyp(gamma, L "p")), InsAnd(gamma, And(T, L "q"), InsT(gamma, T), Hyp(gamma, L "q")));;
valid_ndprooftree a;;
let b = pad a (Set [L("z")]);;
valid_ndprooftree b;;
let c = prune b;;
valid_ndprooftree c;;

(* Test Case 4 - AndElL, AndElR *)
let gamma = Set [And(L("r"),And(L("p"), L("q")))];;

let a = ElemAndL(gamma, L "p", ElemAndR(gamma, And(L "p", L "q"), Hyp(gamma, And(L "r", And(L "p", L "q")))));;
valid_ndprooftree a;;
let b = pad a (Set [L("z")]);;
valid_ndprooftree b;;
let c = prune b;;
valid_ndprooftree c;;

(* Test Case 5 - OrIntR,NotItu *)
let gamma = Set [L("p"); Not(L("p")); Impl(L "p", F)];;
let a = InsOrR(gamma, Or(L "p", L "q"), IntNot(gamma, L "q", ElemImpl(gamma, F, Hyp(gamma, Impl(L "p", F)), Hyp(gamma, L "p"))));;
valid_ndprooftree a;;

let b = pad a (Set [L("z")]);;

valid_ndprooftree b;;
let c = prune b;;
valid_ndprooftree c;;
