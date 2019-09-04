(* Type def *)
type prop = T | F | L of string | Not of prop | 
		And of (prop*prop) | Or of (prop * prop) |
		Impl of (prop*prop) | Iff of (prop*prop);;

type 'a set = Set of ('a list);;

type path = Path of (int list);;


(* Helpful functions *)

let rec map f l = match l with
| [] ->	[]
| x::xs -> (f x)::(map f xs);;  

let rec foldl f e l = match l with
| [] -> e
| x::xs -> foldl f (f e x) xs;;



(* Set Operations *)
let rec contains l a = match l with
| [] -> false
| b::l1 -> (if (a=b) then true
			else (contains l1 a))
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



let rec letters p = match p with
| T -> Set([])
| F -> Set([])
| L(a) -> Set([a])
| Not(a) -> letters a
| And(a, b) -> union (letters a) (letters b)
| Or(a, b) -> union (letters a) (letters b)
| Impl(a, b) -> union (letters a) (letters b)
| Iff(a, b) -> union (letters a) (letters b)
;;

let rec subprop p1 p2 l s = 
(
	if p1=p2 then (union (Set([Path l])) s) 
	else match p1 with
	| T -> s
	| F -> s
	| L(a) -> s
	| Not(a) -> subprop a p2 (l@[0]) s
	| And(a, b) -> (let x = subprop a p2 (l@[-1]) s in 
					subprop b p2 (l@[1]) x)
	| Or(a, b) -> (let x = subprop a p2 (l@[-1]) s in 
					subprop b p2 (l@[1]) x)
	| Impl(a, b) -> (let x = subprop a p2 (l@[-1]) s in 
					subprop b p2 (l@[1]) x)
	| Iff(a, b) -> (let x = subprop a p2 (l@[-1]) s in 
					subprop b p2 (l@[1]) x)
)
;;

exception NotSubProp;;

let subprop_at p1 p2 = let x = subprop p1 p2 [] (Set([])) in 
	match x with 
	| Set([]) -> raise NotSubProp
	| _ -> x
;;









let rec ht p = match p with
| T -> 0
| F -> 0
| And(a, b) -> max (ht a) (ht b) + 1
| Or(a, b) -> max (ht a) (ht b) + 1
| Impl(a, b) -> max (ht a) (ht b) + 1
| Iff(a, b) -> max (ht a) (ht b) + 1
| Not (a) -> (ht a) + 1
| L (a) -> 0
;;

let rec size p = match p with
| T -> 1
| F -> 1
| And(a, b) -> (size a) + (size b) + 1
| Or(a, b) -> (size a) + (size b) + 1
| Impl(a, b) -> (size a) + (size b) + 1
| Iff(a, b) -> (size a) + (size b) + 1
| Not (a) -> (size a) + 1
| L (a) -> 1
;;

let rec truth p table = match p with
| T -> true
| F -> false
| And(a, b) -> (truth a table) && (truth b table)
| Or(a, b) -> (truth a table) || (truth b table)
| Not(a) -> not (truth a table)
| Impl(a, b) -> ((not (truth a table)) || (truth b table))
| Iff(a, b) -> (truth (Impl(a, b)) table) && (truth (Impl(b, a)) table)
| L(s) -> table s
;;

(* NNF forms *)

let rec andornot p = match p with
| T -> T
| F -> F
| L(a) -> L(a)
| Not(a) -> Not(andornot a)
| And(a, b) -> And(andornot a, andornot b)
| Or(a, b) -> Or(andornot a, andornot b)
| Impl(a, b) -> Or(Not(andornot a), andornot b)
| Iff(a, b) -> And(andornot(Impl(a, b)), andornot(Impl(b, a)))
;;
exception TypeError of string;;

let rec nnnf p1 = match p1 with
| L(a) -> L(a)
| T -> T
| F -> F
| Not(L(a)) -> Not(L(a))
| Not(T) -> F
| Not(F) -> T
| Not(And(a, b)) -> Or(nnnf (Not(a)), nnnf (Not (b)))
| Not(Or(a, b)) -> And(nnnf (Not(a)), nnnf (Not (b)))
| Not(Not(a)) -> nnnf a
| Not(_) -> raise (TypeError "Iff and Impl not allowed!")
| And(a, b) -> And(nnnf a, nnnf b)
| Or(a, b) -> Or(nnnf a, nnnf b)
| Impl(_, _) -> raise (TypeError "Impl not allowed!")
| Iff(_, _) -> raise (TypeError "Iff not allowed!")
;;

let rec nnf p = nnnf (andornot p);;


let rec distr_or p1 p2 = match (p1, p2) with
| (a, And (b, c)) -> And (distr_or a b , distr_or a c)
| (And (a, b), c) -> And (distr_or a c, distr_or b c)
| (a, b) -> Or (a, b)
;;

let rec prop_cnf p = match p with
| L a -> p
| T -> T
| F -> F
| Not(_) -> p
| And(a, b) -> And (prop_cnf a, prop_cnf b)
| Or(a, b) -> distr_or (prop_cnf a) (prop_cnf b)
| _ -> raise (TypeError "Iff or Impl not allowed!")
;;

let cnf p = prop_cnf (nnf p)
;;

let rec dist_and p1 p2 = match p1, p2 with
| (a, Or(b, c)) -> Or(dist_and a b, dist_and a c)
| (Or(a, b), c) -> Or(dist_and a c, dist_and b c)
| (a, b) -> And(a, b)
;;

let rec prop_dnf p = match p with
| L a -> p 
| T -> T
| F -> F
| Not(a) -> p 
| And(a, b) -> dist_and (prop_dnf a) (prop_dnf b)
| Or(a, b) -> Or(prop_dnf a, prop_dnf b)
| _ -> raise (TypeError "Iff or Impl not allowed!")
;;

let dnf p = prop_dnf (nnf p);;



(* Examples *)

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


ht p1;;
ht p2;;
ht p3;;
ht p4;;
ht p5;;
ht p6;;
ht p7;;
ht p8;;
ht p9;;
ht p10;;
ht p11;;
ht p12;;
ht p13;;
ht p14;;
ht p15;;
ht p16;;
ht p17;;

size p1;;
size p2;;
size p3;;
size p4;;
size p5;;
size p6;;
size p7;;
size p8;;
size p9;;
size p10;;
size p11;;
size p12;;
size p13;;
size p14;;
size p15;;
size p16;;
size p17;;

letters p7;;
letters p8;;
letters p9;;
letters p10;;
letters p13;;
letters p14;;
letters p15;;
letters p16;;
letters p17;;



let prop1 = Or(Or(And(L "a", L "b"), And(L "c", L "d")), And(L "e", L "f"));;


let prop2 = 
And                                                                        
 (And                                                                      
   (And (Or (Or (L "a", L "c"), L "e"), Or (Or (L "b", L "c"), L "e")),    
    And (Or (Or (L "a", L "d"), L "e"), Or (Or (L "b", L "d"), L "e"))),   
  And                                                                      
   (And (Or (Or (L "a", L "c"), L "f"), Or (Or (L "b", L "c"), L "f")),    
    And (Or (Or (L "a", L "d"), L "f"), Or (Or (L "b", L "d"), L "f"))))   
;;

let prop3 = And(And(Or(L "a", L "b"), Or(L "c", L "d")), And(L "e", L "f"));;

nnf p17;;
nnf p16;;

cnf p17;;
cnf p16;;
cnf prop1;;
cnf prop2;;

dnf p17;;
dnf p16;;
dnf prop1;;
dnf prop2;;

