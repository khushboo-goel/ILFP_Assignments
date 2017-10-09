type variable = string;;
type symbol = string;;

type term = V of variable | Node of symbol * (term list);;

(*let signature=[("1",0);("0",0);("s",2);("x",2)];;*)

let rec sig_list x= match x with
                    []->[]
                    |(p,q)::xs-> p:: sig_list xs;;

let rec find_val r s= match s with
                     []->true
                     |x::xs-> if (x=r) then false
                                   else find_val r xs;;

let rec find_zero x= match x with
                     []->false
                     |(p,q)::xs-> if (q=0) then true else find_zero xs;;

let rec check_sig x = match x with
                      []->false
                      |[(p,q)]-> if (find_zero x) then true else false
                      |(p,q)::xs -> if (q < 0) then false else( if (q=0 || q>0) then ( if (find_val p (sig_list xs)) then check_sig xs else false ) else false ) ;;

let rec find_arity x p= match x with
                        []->
                       |(r,s)::xs-> if (r=p) then s else find_arity xs p;;

let rec wfterm x y = match x with
	                  V(n)->true
	                 |Node(p,[])->if (find_val p (sig_list y)) then true else false
	                 |Node(p,q)-> if (find_val p (sig_list y)) then ( if (size q)) else false;;

let rec map f l= match l with
                   []->[]
                  |x::xs-> (f x)::(map f xs);;

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

let rec vars x = match x with
                 V(n)->[n]
                |Node(p,[])-> []
                |Node(p,q)-> (map1 vars q);;
