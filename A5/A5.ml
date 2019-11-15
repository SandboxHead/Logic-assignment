type symbol = Sym of string;;
type variable = Var of string;;

type 'a set = Set of ('a list);;

type term = V of variable | Node of symbol*(term list);;


type literal = Pos of term | Neg of term;;
(* type clause = Set of literal;; *)


(* Part 1 *)
(* Checks if all arity are positive or not. *)
let rec check_neg l = match l with
| [] -> true
| (a, b)::xs -> (if b<0 then false else (check_neg xs) );;


let rec check_term a l = match l with
| [] -> true
| (Sym(x), y)::xs ->(if x=a then false else (check_term a xs) ) ;;

(* check repetation of a symbol in signature. *)
let rec check_dup l = match l with
| [] -> true 
| (Sym(x), y)::xs -> (check_term x xs) && (check_dup xs);;


let signature =  [(Sym "a", 3); (Sym "b", 1); (Sym "c", 0)];;

(* Check validy of a given signature. *)
let check_sig l = check_neg l && check_dup l;;

(* Part 2 *)

let rec map f l = match l with
| [] ->	[]
| x::xs -> (f x)::(map f xs);;  

let rec foldl f e l = match l with
| [] -> e
| x::xs -> foldl f (f e x) xs;;

let andd a b = a && b;;


exception InvalidInput
let rec get_arity s a = match s with
| [] -> raise InvalidInput
| (Sym x,y)::xs -> if (a=x) then y else (get_arity xs a);;

(* Checks if a term is valid according to a given correct signature. *)
let rec wfterm s t= match t with
| V x -> true
| Node(Sym a, b) -> (let x = (if(List.length b = get_arity s a) then true else false) in
		(x && (foldl andd true (map (wfterm s) b))));;

(* Part 3 *)

let add a b = a+b;;

let rec my_max a l = match l with
| [] -> a;
| x::xs -> (if x>a then my_max x xs else my_max a xs);;

let rec ht t = match t with
| V x -> 0
| Node(a, []) -> 0 
| Node(a, b) -> 1 + my_max 0 (map ht b);; 


let rec size t = match t with
| V x -> 1
| Node(a, b) -> 1 + foldl add 0 (map size b);;  

let arr_concat a b = a@b;;

let uniq l =
  let rec tail_uniq a l =
    match l with
      | [] -> a
      | (Var y)::tl -> tail_uniq ((Var y)::a) (List.filter (fun (Var x) -> ((compare x y)!=0)) tl) in
  tail_uniq [] l;;

(* let uniq lst =
  let rec is_member n mlst =
    match mlst with
    | [] -> false
    | h::tl ->
        begin
          if h=n then true
          else is_member n tl
        end
  in
  let rec loop lbuf =
    match lbuf with
    | [] -> []
    | h::tl ->
        begin
        let rbuf = loop tl
        in
          if is_member h rbuf then rbuf
          else h::rbuf
        end
  in
  loop lst;; *)

let rec vars t = let x = (match t with
| V x -> [x]
| Node(a, []) -> [] 
| Node(a, b) ->  foldl arr_concat [] (map vars b)) in
 uniq x;;
(* Part 4 *)

(* Substitution could be done best by using a hash table from variable to term. 
We could access any elementin constant time and it's also a finite domain mapping *)
let substitution = Hashtbl.create 20;;
 
(* Part 6 *)

(* Given a term t and a substitution sigma, it gives a substituted term of given term *)
let rec subst sigma t = match t with
| V a -> (if (List.length (Hashtbl.find_all sigma a) = 0) then V a else
		   Hashtbl.find sigma a)
| Node(a, []) -> Node(a, [])
| Node(a, b) -> Node(a, map (subst sigma) b);;

(* Part 5 *)
(* A base function to show hashtable in form of list to use inside fold function. *)
let foldtbl a b c = (a,b)::c;;

(* Expands a substitution by adding extra key-value pairs in it. *)
let rec addelem t l = match l with 
| [] -> ()
| (a, b)::xs -> (if not (Hashtbl.mem t a) then Hashtbl.add t a b; 
				 addelem t xs);;

(* Apply subst function on all the values of substitution s wrt substitution s2 *)
let rec replace_val s l s2 = match l with
| [] -> ()
| (a,b)::xs -> Hashtbl.replace s a (subst s2 (Hashtbl.find s a));
			   replace_val s xs s2;;				 

(* compose two substitution s1 and s2. *)
let composition s1 s2 = 
	let s3 = Hashtbl.copy s1 in
		(replace_val s3 (Hashtbl.fold foldtbl s1 []) s2; 
		addelem s3 (Hashtbl.fold foldtbl s2 []);
		s3);;

(* Part 7 *)

exception NOT_UNIFIABLE;;

(* finds most general unifier *)
let rec mgu t1 t2 =  match (t1, t2) with
| (V x, V y) -> (let t = (Hashtbl.create 1) in 
					if not (x=y)  then Hashtbl.add t x t2; t)
| (V x, Node(a,[])) -> (let t = (Hashtbl.create 1) in 
							 Hashtbl.add t x t2; t)
| (Node(a,[]), V x) -> (let t = (Hashtbl.create 1) in 
							 Hashtbl.add t x t1; t)
| (V x, Node(a, b)) -> (if (List.mem x (vars t2)) then raise NOT_UNIFIABLE else
						(let t = (Hashtbl.create 1) in 
							 Hashtbl.add t x t2; t))
| (Node(a, b), V x) -> (if (List.mem x (vars t1)) then raise NOT_UNIFIABLE else
						(let t = (Hashtbl.create 1) in 
							 Hashtbl.add t x t1; t))
| (Node(a,[]), Node(b,[])) -> (if (a=b) then Hashtbl.create 1 else raise NOT_UNIFIABLE)
| (Node(a, b), Node(c, d)) -> if not (a=c) then raise NOT_UNIFIABLE else
	 (match (b,d) with
	 ([], []) -> Hashtbl.create 1
	|(x::xs, y::ys) -> (let temp_tbl = (mgu x y) in
			 composition temp_tbl (mgu (Node(a, (map (subst temp_tbl) xs))) (Node(a, (map (subst temp_tbl) ys))))
			)
	);;



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
exception Error;;



(* RESOLUTION *)

let rec check_single_unification l1 c = match c with
| Set([]) -> false
| Set (l2::cla) -> (match (l1, l2) with
    | Pos(t1), Pos(t2) -> check_single_unification l1 (Set(cla))
    | Neg(t1), Neg(t2) -> check_single_unification l1 (Set(cla))
    | Pos(t1), Neg(t2) -> let x = (try Some(mgu t1 t2) with NOT_UNIFIABLE -> None) in
        (match x with
          | Some(_) -> true
          | None -> check_single_unification l1 (Set(cla))
        )
    | Neg(t1), Pos(t2) -> let x = (try Some(mgu t1 t2) with NOT_UNIFIABLE -> None) in
        (match x with
          | Some(_) -> true
          | None -> check_single_unification l1 (Set(cla))
        )
)
;;


let rec check_unification c1 c2 = match c1 with
| Set([]) -> false
| Set(l1::others) -> check_single_unification l1 c2 || check_unification (Set(others)) c2
;;


let rec get_clause c1 clauses = match clauses with
| [] -> []
| c2::cla -> if(check_unification c1 c2) then [c2] else get_clause c1 cla
;;

let rec select_clauses clauses = match clauses with
| Set([]) -> raise Error
| Set(c1::cla) -> let c2 = get_clause c1 cla in 
                  if (List.length c2 = 0) then select_clauses (Set(cla))
                  else (c1, List.hd c2)
;;

let rec do_single_unification l1 c = match c with
| Set([]) -> raise Error
| Set(l2::cla) -> (match (l1, l2) with 
    | Pos(t1), Pos(t2) -> do_single_unification l1 (Set(cla))
    | Neg(t1), Neg(t2) -> do_single_unification l1 (Set(cla))
    | Pos(t1), Neg(t2) -> let x = (try Some(mgu t1 t2) with NOT_UNIFIABLE -> None) in
        (match x with
          | Some(uni) -> (l1, l2, uni)
          | None -> do_single_unification l1 (Set(cla))
        )
    | Neg(t1), Pos(t2) -> let x = (try Some(mgu t1 t2) with NOT_UNIFIABLE -> None) in
        (match x with
          | Some(uni) -> (l1, l2, uni)
          | None -> do_single_unification l1 (Set(cla))
        )

)
;;

let rec do_unification c1 c2 = match c1 with
| Set([]) -> []
| Set(l1::others) -> if(check_single_unification l1 c2) 
                        then (do_single_unification l1 c2)::(do_unification (Set(others)) c2)
                     else do_unification (Set(others)) c2
;;

let rec substitute_all uni c = match c with
| Set([]) -> Set []
| Set((Pos(a))::c1) -> union (Set [Pos(subst uni a)]) (substitute_all uni (Set c1))
| Set((Neg(a))::c1) -> union (Set [Neg(subst uni a)]) (substitute_all uni (Set c1))
;;


let rec one_step_resolution c1 c2 l1 l2 uni = substitute_all uni (union (difference c1 (Set[l1])) (difference c2 (Set[l2])));;

let rec try_unification c1 c2 l clauses = match l with
| [] -> []
| (l1, l2, uni)::extras -> let x = one_step_resolution c1 c2 l1 l2 uni in 
                            if(member clauses x) then try_unification c1 c2 extras clauses
                            else x::(try_unification c1 c2 extras clauses)
;;

let rec check_contradiction l = match l with
| [] -> false
| (Set(a))::b -> if(List.length a = 0) then true else check_contradiction b
;;


let rec real_resolution c1 rem_clauses clauses = match rem_clauses with
| Set([]) -> (true, Set [])
| Set(c2::cla) -> (match try_unification c1 c2 (do_unification c1 c2) clauses with
  | [] -> real_resolution c1 (Set cla) clauses
  | l -> if (check_contradiction l) then (false, union clauses (Set l)) else (true, union clauses (Set l)) 
)
;;

let rec head_real_resolution clauses all_clauses = match clauses with
| Set [] -> (true, all_clauses)
| Set (a::others) -> let x = real_resolution a (Set others) all_clauses in (match x with
  | false, _ -> x
  | true, Set [] -> head_real_resolution (Set others) all_clauses
  | true, li -> head_real_resolution li li
)
;;

let resolution clauses = head_real_resolution clauses clauses;;


(* signatures *)

let ss1 = [(Sym "a", 0); (Sym "f", 2); (Sym "g", 1); (Sym "b", 0)];;
let ss2 = [(Sym "b", -1); (Sym "f", 2); (Sym "g", 1)];;
let ss3 = [(Sym "d", 5); (Sym "f", 2); (Sym "g", 3)];;
let ss4 = [(Sym "a", 0); (Sym "f", 2); (Sym "g", 1); (Sym "g", 1)];;
let ss5 = [];;
let ss6 = [(Sym "a", 3); (Sym "c", 1); (Sym "g", 1); (Sym "b", 2)];;


check_sig ss1;;
check_sig ss2;;
check_sig ss3;;
check_sig ss4;;
check_sig ss5;;
check_sig ss6;;

let t = Node(Sym "c", [V(Var "g")]);;
let u = Node (Sym "b", [t; V(Var"a")]);;
let v = Node (Sym "a", [u;u;t]);;
let w = Node (Sym "a", [v; u; V(Var "x")]);;

wfterm ss6 u;;
wfterm ss6 v;;
wfterm ss6 w;;

ht t;;
ht u;;
ht v;;
ht w;;

size t;;
size u;;
size v;;
size w;;

vars t;;
vars u;;
vars v;;
vars w;;


let substitution = Hashtbl.create 10;;
Hashtbl.add substitution (Var "a") (V (Var "b"));;
Hashtbl.add substitution (Var "x") (w);;
Hashtbl.fold foldtbl substitution [];;     


subst substitution t;;
subst substitution u;;
subst substitution v;;
subst substitution w;;

let subs2 = Hashtbl.create 10;;
Hashtbl.add subs2 (Var "b") w;;
Hashtbl.add subs2 (Var "x") (V(Var "a"));;
Hashtbl.fold foldtbl subs2 [];;


let subs3 = composition substitution subs2;;
Hashtbl.fold foldtbl subs3 [];;

let subs4 = composition subs2 substitution;;
Hashtbl.fold foldtbl subs4 [];;

(* let x = V(Var "x");;
let y = V(Var "y");;
let mgu1 = mgu x y;;
Hashtbl.fold foldtbl mgu1 [];;

let x1 = Node (Sym "a", []);;
let mgu2 = mgu x x1;;
Hashtbl.fold foldtbl mgu2 [];;

let x2 = Node (Sym "b", [x]);;
let x3 = Node (Sym "b", [x1]);;
let mgu3 = mgu x2 x3;;
Hashtbl.fold foldtbl mgu3 [];;

let x4 = Node (Sym "c", []);;
let x5 = Node (Sym "d", [x2; x4]);;
let x6 = Node (Sym "d", [x3; x]);;
let mgu4 = mgu x5 x6;;
Hashtbl.fold foldtbl mgu4 [];;

let x7 = Node (Sym "e", [x5; x2]);;
let x8 = Node (Sym "e", [x6; x3]);;
let mgu4 = mgu x7 x8;;
Hashtbl.fold foldtbl mgu4 [];;
 *)

let x = V (Var "x");;
let a = Node (Sym "a", []);;
let b = Node (Sym "b", []);;
let hxa = Node (Sym "h", [x;a]);;
let hba = Node (Sym "h", [b;a]);;
let mgu5 = mgu hxa hba;;
Hashtbl.fold foldtbl mgu5 [];;
subst mgu5 hxa = subst mgu5 hba;;

let hbx = Node (Sym "h", [b;x]);;
let z = V (Var "z");;
let hxz = Node (Sym "h",[x;z]);;
let mgu6 = mgu hbx hxz;;
Hashtbl.fold foldtbl mgu6 [];;
subst mgu6 hbx = subst mgu6 hxz;;

let gh = Node (Sym "g", [hxa; hbx]);;
let ghh = Node (Sym "g", [hba; hxz]);;
let mgu7 = mgu gh ghh;;
Hashtbl.fold foldtbl mgu7 [];;
subst mgu7 gh = subst mgu7 ghh;;

let y = V (Var "y");;
let ghy = Node (Sym "g", [hxa; y]);;
let gzh = Node (Sym "g", [z; hbx]);;
let mgu8 = mgu ghy gzh;;
Hashtbl.fold foldtbl mgu8 [];;
subst mgu8 ghy = subst mgu8 gzh;;


(* Example PQ *)

let p = V(Var "x");;
let q = V(Var "y");;

let p1 = Pos(p);;
let q1 = Pos(q);;
let p2 = Neg(p);;
let q2 = Neg(q);;

let c1 = Set [p1; q1];;
let c2 = Set [p2; q1];;
let c3 = Set [p1; q2];;
let c4 = Set [p2; q2];;

let cs = Set [c1; c2; c3; c4];;


(* Example 1 *)
let c1 = Set [p1];;
let c2 = Set [q1];;
let c3 = Set [p2; q2];;
let cs1 = Set [c1; c2; c3];;
let r1 = resolution cs1;;

(* Example 2 *)
let a = V(Var "a");;
let h = V(Var "h");;
let i = V(Var "i");;
let m = V(Var "m");;

let a1 = Pos(a);;
let a2 = Neg(a);;
let h1 = Pos(h);;
let h2 = Neg(h);;


let i1 = Pos(i);;
let i2 = Neg(i);;
let m1 = Pos(m);;
let m2 = Neg(m);;


let c1 = Set [a2; h1];;
let c2 = Set [h2];;
let c3 = Set [i2; h1];;
let c4 = Set [m1; a1];;
let c5 = Set [m2; i1];;

let cl2 = Set [c1; c2; c3; c4; c5];;

let r2 = resolution cl2;;

(* Example 3 *)

let r = V (Var "r");;
let r1 = Pos(r);;
let r2 = Neg(r);;

let c1 = Set [p1];;
let c2 = Set [p2; q1];;
let c3 = Set [p2; q2; r1];;
let c4 = Set [r2];;

let cl3 = Set [c1; c2; c3; c4];;
let r3 = resolution cl3;;

(* Example 4 *)
let lulu = Node(Sym "lulu", []);;
let fifi = Node(Sym "fifi", []);;

let t1 = Node(Sym "mother", [lulu; fifi]);;
let x = V (Var "x");;
let y = V (Var "y");;

let t2 = Node(Sym "mother", [x; y]);;
let t3 = Node(Sym "parent", [x; y]);;

let t4 = Node(Sym "Alive", [x]);;
let t5 = Node(Sym "Older", [x; y]);;
let t6 = Node(Sym "Alive", [lulu]);;
let t7 = Node(Sym "Older", [lulu; fifi]);;

let l1 = Pos(t1);;
let l2 = Neg(t2);;
let l3 = Pos(t3);;
let l4 = Neg(t3);;
let l5 = Neg(t4);;
let l6 = Pos(t5);;
let l7 = Pos(t6);;
let l8 = Pos(t7);;

let c1 = Set [l1];;
let c2 = Set [l2; l3];;
let c3 = Set [l4; l5; l6];;
let c4 = Set [l7];;
let c5 = Set [l8];;

let cl4 = Set [c1; c2; c3; c4; c5];;
let r4 = resolution cl4;;


(* Example 4 *)
let c1 = Set [p1];;
let c2 = Set [q1];;
let c3 = Set [p2; q2];;
let cs1 = Set [c1; c2; c3];;
let r1 = resolution cs1;;

let sc = select_clauses cs1;;
let c1 = Set [Pos (V (Var "x"))];;
let c2 = Set [Neg (V (Var "x")); Neg (V (Var "y"))];;

let l1 = Pos (V (Var "x"));;
let l2 = Neg (V (Var "x"));;

one_step_resolution c1 c2 l1 l2 (mgu (V (Var "x")) (V (Var "x")));;

(* Reason for termination *)
(* 
My code of resolution will always terminate because number of literals are finite, suppose n. A literal can either exist of not exits
in a clause. So, this gives us a maximum of 2^n different clauses. Now, in one iteration of my resolution step, At least one more new 
clause is added to the set of clauses. So, it will take a worst case of 2^n steps to reach maximum clause possible. Then in the next
step, because no more clause will be added, the algorithm will definetly terminate.  
 *)



