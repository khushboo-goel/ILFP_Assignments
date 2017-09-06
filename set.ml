(*COL765 : ASSIGNMENT-1 : Submitted To: Prof. Sanjiva Prasad
                 S        Submitted by: Khushboo Goel(2017MCS2084) 




Assignment is to represent finite sets (of any arbitrary type 'a)

(a) using OCaml lists.
    Representation invariant: a set is represented as a list without duplicates.*)


type set = int list;;


(*Some additional functions to check the Representation Invariant of the set*)

let rec find_val s r= match s with
                  []->false
                 |x::xs-> if (x=r) then true
                                   else find_val xs r;;

let rec append l1 l2= match l1 with
                      []->l2
                     | x::xs-> x::(append xs l2);;

let rec islist s l = match s with 
                    []-> true
                    |x::xs-> if (find_val l x) then false
                                          else (islist xs (append l [x]));;

(*Map function of the list, which maps a function fover the list l*)
let rec map f l= match l with
                   []->[]
                  |x::xs-> (f x)::(map f xs);;


(* Function dedined to be used in powerset program*)
let func a b = a::b;;

(*1. emptyset s:- represents the empty set, if the given s set is empty or not.*)

let emptyset=[];;


let empty s= match s with
             []->true
            |x->false;;




(*2. member s x :- returns true if and only if x is in s. *)
let rec member s r= match s with
                  []->false
                 |x::xs-> if (x=r) then true
                                   else member xs r;;



(*3. card s:- returns the cardinality i.e. number of elements in the set s.*)
let rec card s = match s with
                  []->0
                 | x::xs-> 1 + (card xs);;



(*4. union s1 s2:- returns the union of sets s1 and s2*)
let rec union s1 s2 = match s1 with 
                          []->s2
                          |x::xs -> match s2 with 
                                     []->s1
                                     | y::ys-> if (member s2 x) then (union xs s2)
                                                              else x ::(union xs s2 );;



(*5. intersection s1 s2:- returns the intersection of s1 and s2*)
let rec intersect s1 s2 = match s1 with 
                          []->[]
                          |x::xs -> match s2 with 
                                     []->[]
                                     | y::ys-> if (member s2 x) then x::intersect xs s2
                                                              else intersect xs s2;;


(*6. difference s1 s2:- returns the set consisting of elements of s1 which are not in s2*)
let rec difference s1 s2= match s1 with 
                          []->[]
                          |x::xs -> match s2 with 
                                    []-> s1
                                   | y::ys -> if (member s2 x) then difference xs s2
                                                             else x::difference xs s2;;


let rec product_r s1 s2= match s1 with
                         []->[]
                         |x::xs-> match s2 with 
                               []->[]
                               | y::ys-> ((x,y)::(product_r [x] ys));;



(*7. product s1 s2:- returns the cartesian product of s1 and s2.*)
let rec product s1 s2 = match s1 with 
                        []->[]
                        |x::xs-> match s2 with 
                                 []->[]
                                 |y::ys-> (product_r [x] s2) @ (product xs s2);;



(*8. powerset s:-returns the set of subsets of s.*)
let rec powerset s = match s with 
                       []->[[]]
                      |x::xs -> (map (func x) (powerset xs))@(powerset xs);;




(*9. subset s1 s2:- returns true if and only if s1 is a subset of s2.*)
let rec subset s1 s2= match s1 with 
                  []->true
                  |x::xs-> match s2 with
                           []-> false
                           |y::ys-> if (member s2 x) then subset xs s2
                                                   else false;;



(*10.equalset s1 s2:- returns true if and only if  set s1 is equal to set s2.*)
let rec equalsets s1 s2= if (subset s1 s2) then 
                                               (if (subset s2 s1) then true
                                                                 else false)
                                           else false;;








(* (b) Representing a set i by its characteristic function [Recall that f_s is the characteristic function of set s when x \in s iff  f_s (x) = true ]*)


(*The two characteristic functions are defined below, namely funct_x and funct_y*)
let funct_x l= match l with 
             1|3|7->true
             |_ ->false;;


let funct_y l= match l with 
             2|3|7|8->true
             |_ ->false;;


(* 1. emptyset:- represents the empty set.*)
let emptyset = false;;


(* 2. member_cx s x:- returns true if and only if x is in s.*)
let member_cx s x = s x;;


(* 3. union_c s1 s2:- returns the union of sets s1 and s2. This function takes the a list as an input and compare it with the union of the two characteristic function s1 and s2*)
let rec union_c s1 s2 x =  match x with
                        []->[]
                        |x::xs -> if ((s1 x) || (s2 x)) then true::(union_c s1 s2 xs) else false::(union_c s1 s2 xs);;


(* 4. intersect_c s1 s2:- returns the intersection of s1 and s2. This function takes the a list as an input and compare it with the intersection of the two characteristic function s1 and s2*)
let rec intersect_c s1 s2 x = match x with
                          []->[]
                          |x::xs -> if ((s1 x) && (s2 x)) then true::(intersect_c s1 s2 xs) else false::(intersect_c s1 s2 xs);;



(* 5. difference_c s1 s2:- returns the set consisting of elements of s1 which are not in s2. This function takes the a list as an input and compare it with the set difference of the two characteristic function s1 and s2*)
let rec difference_c s1 s2 x = match x with
                          []->[]
                          |x::xs -> if ((s1 x) && not( (s2 x))) then true::(difference_c s1 s2 xs) else false::(difference_c s1 s2 xs);;



(* 6. product_c s1 s2:- returns the cartesian product of s1 and s2. This function takes the a list as an input and compare it with the cartesian product of the two characteristic function s1 and s2*)
let rec product_c s1 s2 x = match x with
                        []->[]
                        |(r,s)::rx -> if ((s1 r) && (s2 s)) then true::(product_c s1 s2 rx) else false::(product_c s1 s2 rx);;




                           


