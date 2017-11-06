type variable = string;;
type symbol = string;;
type arity= int;;

type term = V of variable | Node of symbol * (term list);;
type signature = (symbol * arity) list;;

let rec sig_list x= match x with
                    []->[]
                    |(p,q)::xs-> p:: sig_list xs;;

let rec find_val r s= match s with
                     []->true
                     |x::xs-> if (x=r) then false
                                   else find_val r xs;;

let rec find_zero x= match x with
                     []->false
                     |(p,q)::[]->if (q=0) then true else false
                     |(p,q)::xs-> if (q=0) then true else find_zero xs;;

let rec check_sig x  = match x with
                      []->false
                      |(p,q)::[]-> if(q=0 || q>0) then true else false
                      |(p,q)::xs ->if (q=0 || q>0) then (if (find_val p (sig_list xs)) then check_sig xs else false) else false;;

let rec find_arity x p= match x with
                        []-> -1
                       |(r,s)::xs -> if (r=p) then s else find_arity xs p;;

let rec size x= match x with
                []->0
                |x::xs->1+(size xs);;

let rec map f l= match l with
                   []->[]
                  |x::xs-> (f x)::(map f xs);;
let rec maps f l t= match l with
                     []->[]
                  |x::xs-> (f x t)::(maps f xs t);;

let rec find x= match x with
					[]->true
					|x::xs -> if (x) then find xs else false;;


let rec wfterm x y = match x with
	                  V(n)->true
	                 |Node(p,[])->if (find_val p (sig_list y)) then false else true
	                 |Node(p,q)-> if (find_val p (sig_list y)) then false else (if ((find_arity y p)=(size q)) then (find (maps wfterm q y)) else false);;


let rec max p y = match p with
                  []->y
                 |x::xs -> if (x>y) then max xs x else max xs y;;

let rec ht x = match x with
                V(n)->0
               |Node(p,[])->0
               |Node(p,q)-> 1 + (max (map ht q) (-1));;


let rec sum x = match x with
                []->0
                |x::xs-> x + (sum xs);;

let rec size x= match x with
                 V(n)->1
                |Node(p,[])->1
                |Node(p,q)-> 1+ (sum (map size q)) ;;



let rec map1 f l= match l with
                   []->[]
                  |x::xs-> (f x)@(map1 f xs);;

let rec varst x = match x with
                 V(n)->[n]
                |Node(p,[])-> []
                |Node(p,q)-> (map1 varst q);;
let rec remove_extra l= match l with
                        []->[]
                        |x::xs -> if (find_val x xs) then x::(remove_extra xs) else  remove_extra xs;;

let rec vars x= remove_extra (varst x);;

type substitution = (variable * term) list;;

let rec find_sub x y= match y with
                      []-> x
                      |(p,q)::xs-> if (x=p) then q else find_sub x xs;;

let rec subst x y= match x with
                    V(n)-> find_sub x y
                   |Node(p,[])-> Node(p,[])
                   |Node(p,q)-> Node(p,maps subst q y)
               ;;
               
let rec substitution_composition x y= match (x,y) with
                                    ([],[])->[]
                                   |([], (p,q)::xs)->(p,q)::xs
                                   |((p,q)::xs,[])->(p,q)::xs
                                   |((p1,q1)::xs1,(p2,q2)::xs2)-> if (q1=p2 || find_val q1 (sig_list xs2)) then (p1,q2)::substitution_composition xs1 y else substitution_composition xs1 y  ;;
exception NOT_UNIFIABLE;;

let rec map_uni f l t= match (l,t) with
                        ([],[])->[]
                      |([],y::ys)->raise NOT_UNIFIABLE
                      |(x::xs,[])->raise NOT_UNIFIABLE
                      |(x::xs , y::ys)-> (f x y)@(map_uni f xs ys);;

let rec find_uni y x= match y with
                      V(a)-> if(x=y) then true else false
                     |Node(p,[])->false
                     |Node(p,q)-> if (find (maps find_uni q x)) then true else false;;

let rec mgus x y= match (x,y) with
                 (V(a),V(b))->if (a=b) then [] else [(V(b),V(a))]
                 |(Node(a,[]),Node(b,[]))->if(a=b) then [] else raise NOT_UNIFIABLE
                 |(V(a),Node(b,[]))-> [(Node(b,[]),V(a))]
                 |(Node(b,[]), V(a))-> [(V(a), Node(b,[]))]
                 |(V(a), Node(p,q))-> if (find_val (V(a)) q) then raise NOT_UNIFIABLE else [((Node(p,q),V(a)))]
                 |(Node(p,q), V(a))-> if (find_val (V(a)) q) then raise NOT_UNIFIABLE else [(V(a), Node(p,q))]
                 |(Node(p1,q1), Node(p2,q2))-> if (p1 = p2) then map_uni mgus q1 q2 else raise NOT_UNIFIABLE;;


let mgu x y= remove_extra(mgus x y);;


let sig1 = [("X",0);("Y",0);("f",1);("g",2);("h",3);("*",2)];;
let sig2 =[("X",0);("Y",0);("Z",0);("f",1);("g",2);("f",3);("*",2)];;
let term1 = (Node ("f",[V "X"]));;
let term2 = (Node ("g",[V "X";Node("h",[Node("f",[V "X"]);V "Y"])]));;
let term3 = (Node ("g",[V "X";Node("*",[V "Y";Node ("*",[V "X";V "Y"])])]));;
let term4 = (Node("g",[V "X";Node("*",[V "Y";V "X"])]));;
let term5 = (Node("g",[V"Z";Node("*",[V "X";V "Z"])]));;
let term6 = (Node("g",[V "Z";Node("g",[V "X";V "Z"])]));;

let sub1 = [(V "Y", V "U");(V "X", Node("*",[V "Y";V "Y"]))];;

(*--------------------------------------------------------------------------------------------------*)
sig_list sig1;;
check_sig sig1;;(*- : bool = true# *)
check_sig sig2;;(*- : bool = false*)
wfterm term1 sig1;;(*- : bool = true#*)
wfterm term2 sig1;;(*- : bool = false*)
ht term1;;(*- : int = 1#*)
ht term3;;(*- : int = 3*)

size term1;;(*- : int = 2#*)
size term3;;(*- : int = 7*)

vars term1;;(*- : variable list = ["X"]#*)
vars term3;;(*- : variable list = ["X"; "Y"]*)

(*substitution_composition sub1 sub1;;*)
subst term3 sub1;;(*- : term = Node ("g",[Node ("*", [V "U"; V "U"]);Node ("*", [V
"U"; Node ("*", [Node ("*", [V "U"; V "U"]); V "U"])])])*)


mgu term4 term5;;
mgu term4 term6;;(*one of the possible solutions: <{V "U"/V "X"} {V "X"/V "Y"}># *)
(*Exception: NOT_UNIFIABLE*)



