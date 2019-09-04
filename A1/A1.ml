type prop = T | F | L of string | Not of prop | 
		And of (prop*prop) | Or of (prop * prop) |
		Impl of (prop*prop) | Iff of (prop*prop);;

type 'a set = Set of ('a list);;
type node = Node of (prop*bool);;
type tableau = NULL | Table of (node*tableau*tableau);;

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

(* Proposition functions *)

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

let rec equal p1 p2 = match p1, p2 with
| T, T -> true
| F, F -> true
| (And(a, b), And(c, d)) -> ((equal a c) && (equal b d)) || ((equal a d) && (equal b c)) 
| (Or(a, b), And(c, d)) -> ((equal a c) && (equal b d)) || ((equal a d) && (equal b c)) 
| (Impl(a, b), And(c, d)) -> ((equal a c) && (equal b d))
| (Iff(a, b), And(c, d)) -> ((equal a c) && (equal b d))
| Not(a), Not(b) -> equal a b
| _, _ -> false
;;


