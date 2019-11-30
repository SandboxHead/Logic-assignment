type prop = True | False | L of int | Not of prop |
And of (prop*prop) | Or of (prop * prop) |
Impl of (prop*prop) | Iff of (prop*prop);;


type node = Node of int*int*int | Leaf of int;;

type forward = T of (int, node) Hashtbl.t;;
type backward = H of (node, int) Hashtbl.t;;


let add (T t) v = let l = Hashtbl.length t in
Hashtbl.add t l v;
l;;

let rec andornot p = match p with
| True -> True
| False -> False
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
| True -> True
| False -> False
| Not(L(a)) -> Not(L(a))
| Not(True) -> False
| Not(False) -> True
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
| True -> True
| False -> False
| Not(_) -> p
| And(a, b) -> And (prop_cnf a, prop_cnf b)
| Or(a, b) -> distr_or (prop_cnf a) (prop_cnf b)
| _ -> raise (TypeError "Iff or Impl not allowed!")
;;

let cnf p = prop_cnf (nnf p)
;;



let init_t num_vars =
let a = T (Hashtbl.create 100) in
let b = add a (Leaf (num_vars+1)) in
let c = add a (Leaf (num_vars+1)) in
a
;;

exception Error;;

let var (T t) u = match Hashtbl.find t u with
| Node (a, _, _) -> a
| Leaf (a) -> a
;;

let low (T t) u = match Hashtbl.find t u with
| Node (_, a, _) -> a
| Leaf(_) -> raise Error
;;

let high (T t) u = match Hashtbl.find t u with
| Node (_, _, a) -> a
| Leaf(_) -> raise Error
;;

let init_h = H (Hashtbl.create 100);;

let member (H t) n = Hashtbl.find_opt t n != None;;

let lookup (H t) n = Hashtbl.find t n;;

let insert (H t) n u = Hashtbl.add t n u;;

let mk t t1 i l h =
if l=h then l
else if member t1 (Node(i, l ,h)) then lookup t1 (Node(i, l, h))
else let u = add t (Node(i, l, h)) in
let x = insert t1 (Node(i, l, h)) u in u;;


let rec subst p v q = match p with
| L v1 -> if(v=v1) then q else p
| Not p1 -> Not (subst p1 v q)
| And(p1, p2) -> And(subst p1 v q, subst p2 v q)
| Or(p1, p2) -> Or(subst p1 v q, subst p2 v q)
| Impl(p1, p2) -> Impl(subst p1 v q, subst p2 v q)
| Iff(p1, p2) -> Iff(subst p1 v q, subst p2 v q)
| _ -> p
;;

let rec minimise p = match p with
| Not p1 -> let q1 = minimise p1 in
if q1 = True then False else if q1 = False then True else Not q1

| And(p1, p2) -> let q1 = minimise p1 in let q2 = minimise p2 in
if (q1=True && q2=True) then True
else if (q1 = False || q2 = False) then False
else And(q1, q2)

| Or(p1, p2) -> let q1 = minimise p1 in let q2 = minimise p2 in
if (q1=True || q2=True) then True
else if (q1 = False && q2 = False) then False
else Or(q1, q2)

| Impl(p1, p2) -> let q1 = minimise p1 in let q2 = minimise p2 in
if (q1=True && q2=False) then False
else if (q1=False || q2 = True) then True
else Impl(q1, q2)

| Iff(p1, p2) -> let q1 = minimise p1 in let q2 = minimise p2 in
if (q1 = True && q2 = True) then True
else if (q1 = False && q2 = False) then True
else if (q1 = False && q2 = True ) then False
else if (q1 = True && q2 = False ) then False
else Iff(q1, q2)
| _ -> p
;;




let rec build_dash t h p i n =
if i > n then
if p = False then 0 else 1
else
let v0 = build_dash t h (minimise (subst p i False)) (i+1) n in
let v1 = build_dash t h (minimise (subst p i True)) (i+1) n in
mk t h i v0 v1
;;


let build t h p n = build_dash t h p 0 n;;

let is_leaf u = match u with
| 0 | 1 -> true
| _ -> false
;;

let foldtbl a b c = (a,b)::c;;


let rec app u1 u2 g op t h =
	if Hashtbl.find_opt g (u1, u2) != None then Hashtbl.find g (u1, u2)
	else let u =
	if (is_leaf u1 && is_leaf u2) then op u1 u2
	else if var t u1 = var t u2 then mk t h (var t u1) (app (low t u1) (low t u2) g op t h) (app (high t u1) (high t u2) g op t h)
	else if var t u1 < var t u2 then mk t h (var t u1) (app (low t u1) u2 g op t h) (app (high t u1) u2 g op t h)
	else mk t h (var t u1) (app u1 (low t u2) g op t h) (app u1 (high t u2) g op t h)
	in let temp = Hashtbl.add g (u1, u2) u in u;;

let apply t h op u1 u2 = let g = Hashtbl.create 100 in app u1 u2 g op t h;;

let rec restrict t h u j b =
	if var t u > j then u
	else if var t u < j then mk t h (var t u) (restrict t h (low t u) j b) (restrict t h (high t u) j b)
	else if b = 0 then restrict t h (low t u) j b
	else restrict t h (high t u) j b
	;;

let rec pow a b = match b with
| 0 -> 1
| _ -> (pow a (b-1)) * a
;;

let rec count t u = 
	if u = 0 then 0
	else if u = 1 then 1
	else ((pow 2 ((var t (low t u)) - (var t u) - 1 )) *  (count t (low t u))) + ((pow 2 ((var t (high t u)) - (var t u) - 1 )) *  (count t (high t u)))
;;

let satcount t u = (pow 2 (var t u - 1)) * (count t u)
;;

let rec anysat t u = 
	if u = 0 then raise Error
	else if u=1 then []
	else if low t u = 0 then  (var t u, 1)::(anysat t (high t u))
	else (var t u, 0)::(anysat t (low t u))
;;

let rec append_all l1 v value = match l1 with
| [] -> []
| a::l2 -> ((v, value)::a)::(append_all l2 v value)
;;


let rec allsat t u = 
	if u = 0 then []
	else if u = 1 then [[]]
	else (append_all (allsat t (low t u)) (var t u) 0)@(append_all (allsat t (high t u)) (var t u) 1) 
;;


let rec sim t h d u = 
	if d = 0 then 0
	else if u <= 1 then u
	else if d = 1 then mk t h (var t u) (sim t h d (low t u)) (sim t h d (high t u))
	else if (var t d = var t u) then
		if (low t d = 0) then sim t h (high t d) (high t u)
		else if (high t d = 0) then sim t h (low t d) (low t u)
		else mk t h (var t u) (sim t h (low t d) (low t u)) (sim t h (high t d) (high t u))
	else if (var t d < var t u) then mk t h (var t d) (sim t h (low t d) u) (sim t h (high t d) u)
	else mk t h (var t u) (sim t h d (low t u)) (sim t h d (high t u))
;;

let simplify t h d u = sim t h d u;;


let p1 = And(Iff(L 1, L 2), Iff(L 3, L 4));;

let t = init_t 4;;

let h = init_h;;


let tree = build t h p1 4;;

let fold_tbl (T t) = Hashtbl.fold foldtbl t [];;

let len (T t) = Hashtbl.length t;;


fold_tbl t;;

(* Examples *)

let vx1 = L 1;;
let vx2 = L 2;;
let vx3 = L 3;;

let p0 = Iff(vx1, vx2);;
let p1 = Or(p0,vx3);;
let p2 = Or(vx2,vx3);;
let np1 = Not(p1);;


let p1' = nnf(p1);;
let p1'' = cnf(p1);;
let np1' = nnf(np1);;
let np1'' = cnf(np1);;

let t = init_t 3;;
let h = init_h;;

(* build ROBDDs *)
let tt = build t h True 3;;
let tf = build t h False 3;;

let tvx1 = build t h vx1 3;;
let tp2 = build t h p2 3;;
let tp0 = build t h p0 3;;
let tp1 = build t h p1 3;;
let tp1' = build t h p1' 3;;
let tp1'' = build t h p1'' 3;;

let tnp1 = build t h np1 3;;
let tnp1' = build t h np1' 3;;
let tnp1'' = build t h np1'' 3;;

(* Testcase #1 *)
tp1 == tp1';;
tp1 == tp1'';;
tnp1 == tnp1';;
tnp1 == tnp1'';;


(* Testcase #2 *)
let andd p1 p2 = 
	if(p1 = 1 && p2 = 1) then 1 else 0
;;

let orr p1 p2 = 
	if(p1 = 1 || p2 = 1) then 1 else 0
;;

let tp1anp1 = apply t h andd tp1 tnp1;;
tp1anp1 == tf;;

let tp1onp1 = apply t h orr tp1 tnp1;;
tp1onp1 == tt;;


(* Testcase #3 *)

let tp1rv30 = restrict t h tp1 3 0;;
tp1rv30 == tp0;;
let tp1rv31 = restrict t h tp1 3 1;;
tp1rv31 =  tt;;


(* Testcase #4 *)
allsat t tp1;;
satcount t tp1;;
anysat t tp1;;



(* Testcase #5 *)
let tstp2tp1 = simplify t h tp2 tp1;;
tstp2tp1 == tt;;
let tstvx1tp1 = simplify t h tvx1 tp1;;
tstvx1tp1 == tp2;;
