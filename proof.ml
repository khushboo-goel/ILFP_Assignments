type prop = P of string
            | T 
            | F
            | Not of prop 
            | And of prop * prop
            | Or of prop * prop 
            | Implies of prop * prop
;;

type sequent = prop list * prop;;

let max a b = if (a>b) then a else b;;
let rec member s r= match s with
                  []->false
                 |x::xs-> if (x=r) then true
                                   else member xs r;;
let rec find_val s r= match s with
                  []->false
                 |x::xs-> if (x=r) then true
                                   else find_val xs r;;

let rec append l1 l2 = match l1 with
                        []->l2
                        |x::xs -> if (find_val l2 x) then (append xs l2) else x::(append xs l2);;


let rec intersect s1 s2 = match s1 with 
                          []->[]
                          |x::xs -> match s2 with 
                                     []->[]
                                     | y::ys-> if (member s2 x) then x::intersect xs s2
                                                              else intersect xs s2;;
let rec intersection s1 s2 = match s1 with 
                          []->[]
                          |x::xs -> match s2 with 
                                     y -> if (member s1 y) then x::intersection xs y
                                                              else intersection xs y;;
let rec union s1 s2 = match s1 with 
                          []->s2
                          |x::xs -> match s2 with 
                                     []->s1
                                     | y::ys-> if (member s2 x) then (union xs s2)
                                                              else x ::(union xs s2 );;
let rec difference s1 s2= match s1 with 
                          []->[]
                          |x::xs -> match s2 with 
                                    []-> s1
                                   | y::ys -> if (member s2 x) then difference xs s2
                                                             else x::difference xs s2;;

let rec subset s1 s2= match s1 with 
                  []->true
                  |x::xs-> match s2 with
                           []-> false
                           |y::ys-> if (member s2 x) then subset xs s2
                                                   else false;;


let rec equalsets s1 s2= if (subset s1 s2) then 
                                               (if (subset s2 s1) then true
                                                                 else false)
                                           else false;;
exception Blank_array;;															  



type prooftree  = Ass of sequent 
                 |TI of sequent 
                 |FE of sequent
                 |ImpI of prooftree * sequent 
                 |ImpE of prooftree * prooftree * sequent 
                 |AndI of prooftree * prooftree * sequent 
                 |AndEleft of prooftree * sequent 
                 |AndEright of prooftree * sequent 
                 |OrIleft of prooftree * sequent 
                 |OrIright of prooftree * sequent 
                 |OrE of prooftree * prooftree * prooftree * sequent 
                 |NotClass of  prooftree * sequent 
                 |NotIntu of prooftree * sequent ;;


let rec ht x = match x with
                  Ass(s)->0 
                 |TI(s) ->0 
                 |FE(s) ->0
                 |ImpI(p,s)-> 1+ht(p)
                 |ImpE(p1,p2,s)-> 1 + (max (ht(p1))(ht(p2)))
                 |AndI(p1,p2,s)-> (max(ht(p1)) (ht(p2)))+1
                 |AndEleft(p,s)-> ht(p)+1
                 |AndEright(p,s)-> ht(p)+1
                 |OrIleft(p,s)-> ht(p)+1
                 |OrIright(p,s)-> ht(p)+1
                 |OrE(p1,p2,p3,s)-> 1 + (max (max (ht (p1)) (ht (p2))) (ht(p3)))
                 |NotClass(p,s)-> ht(p)+1 
                 |NotIntu(p,s)-> ht(p)+1 ;;              

let rec size x=match x with
                  Ass(s)->1 
                 |TI(s) ->1 
                 |FE(s) ->1
                 |ImpI(p,s)-> 1+ size(p)
                 |ImpE(p1,p2,s)-> 1 + size(p1)+size(p2)
                 |AndI(p1,p2,s)-> 1 + size(p1)+size(p2)
                 |AndEleft(p,s)-> size(p)+1
                 |AndEright(p,s)-> size(p)+1
                 |OrIleft(p,s)-> size(p)+1
                 |OrIright(p,s)-> size(p)+1
                 |OrE(p1,p2,p3,s)-> 1+ size(p1)+size(p2)+size(p3)
                 |NotClass(p,s)-> size(p)+1 
                 |NotIntu(p,s)-> size(p)+1 ;;  


(*Define the function wfprooftree that check that a given candidate proof tree is indeed a well-formed proof tree (i.e., the main formula is of the form expected by the rule, the side formulas are consistent with the main formula, and the extra formulas agree as specified in each rule).*)
(*let rec verify p2 y g1 = match p2 with 
                                                                                                                                                                                                           Ass((g2,r2))-> (if (equalsets g g2) && (r2= x) then true else false)
                                                                                                                                                                                                           |TI((g2,r2)) -> (if (equalsets g g2) && (r2 = x) then true else false)
                                                                                                                                                                                                           |FE((g2,r1)) ->(if (equalsets g g2) && (r2 = x) then true else false)
                                                                                                                                                                                                           |ImpI(px2,(g2,r2))->(if (equalsets g g2) && (r2 =x) then true else false) 
                                                                                                                                                                                                           |ImpE(px,py,(g1,r1))-> (if (equalsets g g2) && (r2 =x) then true else false)
                                                                                                                                                                                                           |AndI(px,py,(g1,r1))-> (if (equalsets g g2) && (r2 =x) then true else false)
                                                                                                                                                                                                           |AndEleft(px,(g1,r1))-> (if (equalsets g g2) && (r2 =x) then true else false)
                                                                                                                                                                                                           |AndEright(px,(g1,r1))-> (if (equalsets g g2) && (r2 =x) then true else false)
                                                                                                                                                                                                           |OrIleft(px,(g1,r1))-> (if (equalsets g g2) && (r2 =x) then true else false)
                                                                                                                                                                                                           |OrIright(px,(g1,r1))-> (if (equalsets g g2) && (r2 =x) then true else false)
                                                                                                                                                                                                           |OrE(px,py,pz,(g1,r1))->(if (equalsets g g2) && (r2 =x) then true else false)
                                                                                                                                                                                                           |NotClass(px,(g1,r1))-> (if (equalsets g g2) && (r2 =x) then true else false) 
                                                                                                                                                                                                           |NotIntu(px,(g1,r1))->(if (equalsets g g2) && (r2 =x) then true else false)
                                                                                                                                                                                                           |_->false;;


let rec wfprooftree u = match u with
                         Ass((g,r))-> (if (find_val g r) then true else false)
		                    |TI((g,r)) -> (if(r=T) then true else false) 
						            (*|FE((g,r)) ->(if((find_val g [F]) and (find_val g r)) then true else false);;*) 
						            |ImpI(p,(g,Implies(x,y)))-> (if (wfprooftree p) then (match p with Ass((g1,r1))-> (if (equalsets(union g [x]) g1) && (r1 =y) then true else false)
																					 |TI((g1,r1)) -> (if (equalsets(union g [x]) g1) && (r1 = y) then true else false)
																					 |FE((g1,r1)) ->(if (equalsets(union g [x]) g1) && (r1 = y) then true else false)
																					 |ImpI(px,(g1,r1))->(if (equalsets(union g [x]) g1) && (r1 =y) then true else false) 
																					 |ImpE(px,py,(g1,r1))-> (if (equalsets(union g [x]) g1) && (r1 =y) then true else false)
																					 |AndI(px,py,(g1,r1))-> (if (equalsets(union g [x]) g1) && (r1 =y) then true else false)
																					 |AndEleft(px,(g1,r1))-> (if (equalsets(union g [x]) g1) && (r1 =y) then true else false)
																					 |AndEright(px,(g1,r1))-> (if (equalsets(union g [x]) g1) && (r1 =y) then true else false)
																					 |OrIleft(px,(g1,r1))-> (if (equalsets(union g [x]) g1) && (r1 =y) then true else false)
																					 |OrIright(px,(g1,r1))-> (if (equalsets(union g [x]) g1) && (r1 =y) then true else false)
																					 |OrE(px,py,pz,(g1,r1))->(if (equalsets(union g [x]) g1) && (r1 =y) then true else false)
																					 |NotClass(px,(g1,r1))-> (if (equalsets(union g [x]) g1) && (r1 =y) then true else false) 
																					 |NotIntu(px,(g1,r1))->(if (equalsets(union g [x]) g1) && (r1 =y) then true else false)
                                           |_-> false)
						                                                  else false)
						 |ImpE(p1,p2,(g,r))-> (if ((wfprooftree p1) && (wfprooftree p2)) then ( (match p1 with
                                                                                           Ass((g1,Implies(x,y)))-> (if (equalsets g g1) && (r =y) then verify p2 y g1 else false)
                                                                                           |TI((g1,Implies(x,y))) -> (if (equalsets g g1) && (r = y) then true else false)
                                                                                           |FE((g1,Implies(x,y))) ->(if (equalsets g g1) && (r = y) then true else false)
                                                                                           |ImpI(px,(g1,Implies(x,y)))->(if (equalsets g g1) && (r =y) then true else false) 
                                                                                           |ImpE(px,py,(g1,Implies(x,y)))-> (if (equalsets g g1) && (r =y) then true else false)
                                                                                           |AndI(px,py,(g1,Implies(x,y)))-> (if (equalsets g g1) && (r =y) then true else false)
                                                                                           |AndEleft(px,(g1,Implies(x,y)))-> (if (equalsets g g1) && (r =y) then true else false)
                                                                                           |AndEright(px,(g1,Implies(x,y)))-> (if (equalsets g g1) && (r =y) then true else false)
                                                                                           |OrIleft(px,(g1,Implies(x,y)))-> (if (equalsets g g1) && (r =y) then true else false)
                                                                                           |OrIright(px,(g1,Implies(x,y)))-> (if (equalsets g g1) && (r =y) then true else false)
                                                                                           |OrE(px,py,pz,(g1,Implies(x,y)))->(if (equalsets g g1) && (r =y) then true else false)
                                                                                           |NotClass(px,(g1,Implies(x,y)))-> (if (equalsets g g1) && (r =y) then true else false) 
                                                                                           |NotIntu(px,(g1,Implies(x,y)))->(if (equalsets g g1) && (r =y) then true else false)
                                                                                           |_-> false
                                                                                                                                                                                ) && match p2 with 
                                                                                                                                                                                                           Ass((g2,r2))-> (if (equalsets g g2) && (r2= x) then true else false)
                                                                                                                                                                                                           |TI((g2,r2)) -> (if (equalsets g g2) && (r2 = x) then true else false)
                                                                                                                                                                                                           |FE((g2,r1)) ->(if (equalsets g g2) && (r2 = x) then true else false)
                                                                                                                                                                                                           |ImpI(px2,(g2,r2))->(if (equalsets g g2) && (r2 =x) then true else false) 
                                                                                                                                                                                                           |ImpE(px,py,(g1,r1))-> (if (equalsets g g2) && (r2 =x) then true else false)
                                                                                                                                                                                                           |AndI(px,py,(g1,r1))-> (if (equalsets g g2) && (r2 =x) then true else false)
                                                                                                                                                                                                           |AndEleft(px,(g1,r1))-> (if (equalsets g g2) && (r2 =x) then true else false)
                                                                                                                                                                                                           |AndEright(px,(g1,r1))-> (if (equalsets g g2) && (r2 =x) then true else false)
                                                                                                                                                                                                           |OrIleft(px,(g1,r1))-> (if (equalsets g g2) && (r2 =x) then true else false)
                                                                                                                                                                                                           |OrIright(px,(g1,r1))-> (if (equalsets g g2) && (r2 =x) then true else false)
                                                                                                                                                                                                           |OrE(px,py,pz,(g1,r1))->(if (equalsets g g2) && (r2 =x) then true else false)
                                                                                                                                                                                                           |NotClass(px,(g1,r1))-> (if (equalsets g g2) && (r2 =x) then true else false) 
                                                                                                                                                                                                           |NotIntu(px,(g1,r1))->(if (equalsets g g2) && (r2 =x) then true else false)
                                                                                                                                                                                                           |_->false)  else false)
						 |AndI(p1,p2,(g,And(x,y)))->(if ((wfprooftree p1) && (wfprooftree p2)) then ((match p1 with
                                                                                           Ass((g1,r1))-> (if (equalsets g g1) && (r1 =x) then true else false)
                                                                                           |TI((g1,r1)) -> (if (equalsets g g1) && (r1 = x) then true else false)
                                                                                           |FE((g1,r1)) ->(if (equalsets g g1) && (r1 = x) then true else false)
                                                                                           |ImpI(px,(g1,r1))->(if (equalsets g g1) && (r1 =x) then true else false) 
                                                                                           |ImpE(px,py,(g1,r1))-> (if (equalsets g g1) && (r1 =x) then true else false)
                                                                                           |AndI(px,py,(g1,r1))-> (if (equalsets g g1) && (r1 =x) then true else false)
                                                                                           |AndEleft(px,(g1,r1))-> (if (equalsets g g1) && (r1 =x) then true else false)
                                                                                           |AndEright(px,(g1,r1))-> (if (equalsets g g1) && (r1 =x) then true else false)
                                                                                           |OrIleft(px,(g1,r1))-> (if (equalsets g g1) && (r1 =x) then true else false)
                                                                                           |OrIright(px,(g1,r1))-> (if (equalsets g g1) && (r1 =x) then true else false)
                                                                                           |OrE(px,py,pz,(g1,r1))->(if (equalsets g g1) && (r1 =x) then true else false)
                                                                                           |NotClass(px,(g1,r1))-> (if (equalsets g g1) && (r1 =x) then true else false) 
                                                                                           |NotIntu(px,(g1,r1))->(if (equalsets g g1) && (r1 =x) then true else false)
                                                                                           |_->false
                                                                                                                                                                                )) && (match p2 with 
                                                                                                                                                                                                           Ass((g2,r2))-> (if (equalsets g g2) && (r1 =y) then true else false)
                                                                                                                                                                                                           |TI((g2,r2)) -> (if (equalsets g g2) && (r1 = y) then true else false)
                                                                                                                                                                                                           |FE((g2,r1)) ->(if (equalsets g g2) && (r1 = y) then true else false)
                                                                                                                                                                                                           |ImpI(px2,(g2,r2))->(if (equalsets g g2) && (r1 =y) then true else false) 
                                                                                                                                                                                                           |ImpE(px,py,(g1,r1))-> (if (equalsets g g2) && (r1 =y) then true else false)
                                                                                                                                                                                                           |AndI(px,py,(g1,r1))-> (if (equalsets g g2) && (r1 =y) then true else false)
                                                                                                                                                                                                           |AndEleft(px,(g1,r1))-> (if (equalsets g g2) && (r1 =y) then true else false)
                                                                                                                                                                                                           |AndEright(px,(g1,r1))-> (if (equalsets g g2) && (r1 =y) then true else false)
                                                                                                                                                                                                           |OrIleft(px,(g1,r1))-> (if (equalsets g g2) && (r1 =y) then true else false)
                                                                                                                                                                                                           |OrIright(px,(g1,r1))-> (if (equalsets g g2) && (r1 =y) then true else false)
                                                                                                                                                                                                           |OrE(px,py,pz,(g1,r1))->(if (equalsets g g2) && (r1 =y) then true else false)
                                                                                                                                                                                                           |NotClass(px,(g1,r1))-> (if (equalsets g g2) && (r1 =y) then true else false) 
                                                                                                                                                                                                           |NotIntu(px,(g1,r1))->(if (equalsets g g2) && (r1 =y) then true else false)
                                                                                                                                                                                                           |_->false)  else false)						 
						  |AndEleft(p,(g,r))-> (if (wfprooftree p) then ( match p with 
                                                             |TI((g1,And(x,y))) -> (if ((r=x) and (equalsets g g1)) then true else false)
                                                             |FE((g1,And(x,y))) ->(if ((r=x) and (equalsets g g1)) then true else false)
                                                             |ImpI(px,(g1,r1))->(false)
                                                             |ImpE(px,py,(g1,And(x,y)))->(if ((r=x) and (equalsets g g1)) then true else false)
                                                             |AndI(px,py,(g1,And(x,y)))-> (if ((r=x) and (equalsets g g1)) then true else false)
                                                             |AndEleft(px,(g1,And(x,y)))-> (if ((r=x) and (equalsets g g1)) then true else false)
                                                             |AndEright(px,(g1,And(x,y)))-> (if ((r=x) and (equalsets g g1)) then true else false)
                                                             |OrIleft(px,(g1,And(x,y)))-> (false)
                                                             |OrIright(px,(g1,And(x,y)))-> (false)
                                                             |OrE(px,py,pz,(g1,And(x,y)))->(if ((r=x) and (equalsets g g1)) then true else false)
                                                             |NotClass(px,(g1,And(x,y)))-> (if ((r=x) and (equalsets g g1)) then true else false) 
                                                             |NotIntu(px,(g1,And(x,y)))->(if ((r=x) and (equalsets g g1)) then true else false)
                                                             |_-> false)  else false)
						 |AndEright(p,(g,r))-> (if (wfprooftree p) then (  match p with 
                                                              Ass((g1,And(x,y)))-> (if (( r=y) and (equalsets g g1)) then true else false)
                                                             |TI((g1,And(x,y))) -> (if (( r=y) and (equalsets g g1)) then true else false)
                                                             |FE((g1,And(x,y))) ->(if (( r=y) and (equalsets g g1)) then true else false)
                                                             |ImpI(px,(g1,r1))->(false)
                                                             |ImpE(px,py,(g1,And(x,y)))->(if (( r=y) and (equalsets g g1)) then true else false)
                                                             |AndI(px,py,(g1,And(x,y)))-> (if (( r=y) and (equalsets g g1)) then true else false)
                                                             |AndEleft(px,(g1,And(x,y)))-> (if (( r=y) and (equalsets g g1)) then true else false)
                                                             |AndEright(px,(g1,And(x,y)))-> (if (( r=y) and (equalsets g g1)) then true else false)
                                                             |OrIleft(px,(g1,And(x,y)))-> (false)
                                                             |OrIright(px,(g1,And(x,y)))-> (false)
                                                             |OrE(px,py,pz,(g1,And(x,y)))->(if (( r=y) and (equalsets g g1)) then true else false)
                                                             |NotClass(px,(g1,And(x,y)))-> (if (( r=y) and (equalsets g g1)) then true else false) 
                                                             |NotIntu(px,(g1,And(x,y)))->(if (( r=y) and (equalsets g g1)) then true else false)
                                                             |_-> false )  else false)
						 |OrIleft(p,(g,Or(x,y)))-> (if (wfprooftree p) then ( match p with 
                                                              Ass((g1,r1))-> (if (( r1=x) and (equalsets g g1)) then true else false)
                                                             |TI(g1,r1) -> (if (( r1=x) and (equalsets g g1)) then true else false)
                                                             |FE((g1, r1)) ->(if (( r1=x) and (equalsets g g1)) then true else false)
                                                             |ImpI(px,(g1,r1))->(if (( r1=x) and (equalsets g g1)) then true else false)
                                                             |ImpE(px,py,(g1,r1 ))->(if (( r1=x) and (equalsets g g1)) then true else false)
                                                             |AndI(px,py,(g1,r1 ))->(if (( r1=x) and (equalsets g g1)) then true else false)
                                                             |AndEleft(px,(g1,r1))->(if (( r1=x) and (equalsets g g1)) then true else false)
                                                             |AndEright(px,(g1,r1))->(if (( r1=x) and (equalsets g g1)) then true else false)
                                                             |OrIleft(px,(g1,r1))->(if (( r1=x) and (equalsets g g1)) then true else false)
                                                             |OrIright(px,(g1,r1 ))->(if (( r1=x) and (equalsets g g1)) then true else false)
                                                             |OrE(px,py,pz,(g1,r1))->(if (( r1=x) and (equalsets g g1)) then true else false)
                                                             |NotClass(px,(g1,r1 ))->(if (( r1=x) and (equalsets g g1)) then true else false) 
                                                             |NotIntu(px,(g1, r1))->(if (( r1=x) and (equalsets g g1)) then true else false)
                                                             |_-> false )  else false)
						|OrIright(p,(g,Or(x,y)))-> (if (wfprooftree p) then (  match p with 
                                                              Ass((g1,r1))-> (if (( r1=y) and (equalsets g g1)) then true else false)
                                                             |TI(g1,r1) -> (if (( r1=y) and (equalsets g g1)) then true else false)
                                                             |FE((g1, r1)) ->(if (( r1=y) and (equalsets g g1)) then true else false)
                                                             |ImpI(px,(g1,r1))->(if (( r1=y) and (equalsets g g1)) then true else false)
                                                             |ImpE(px,py,(g1,r1 ))->(if (( r1=y) and (equalsets g g1)) then true else false)
                                                             |AndI(px,py,(g1,r1 ))->(if (( r1=y) and (equalsets g g1)) then true else false)
                                                             |AndEleft(px,(g1,r1))->(if (( r1=y) and (equalsets g g1)) then true else false)
                                                             |AndEright(px,(g1,r1))->(if (( r1=y) and (equalsets g g1)) then true else false)
                                                             |OrIleft(px,(g1,r1))->(if (( r1=y) and (equalsets g g1)) then true else false)
                                                             |OrIright(px,(g1,r1 ))->(if (( r1=y) and (equalsets g g1)) then true else false)
                                                             |OrE(px,py,pz,(g1,r1))->(if (( r1=y) and (equalsets g g1)) then true else false)
                                                             |NotClass(px,(g1,r1 ))->(if (( r1=y) and (equalsets g g1)) then true else false) 
                                                             |NotIntu(px,(g1, r1))->(if (( r1=y) and (equalsets g g1)) then true else false)
                                                             |_-> false )  else false)
						 (*|OrE(p1,p2,p3,(g,r))->(if ((wfprooftree p1) && (wfprooftree p2) && (wfprooftree p3)) then ((match p1 with
                                                                                                           |TI((g1,Or(x,y))) -> (if ((r=x) and (equalsets g g1)) then true else false)
                                                                                                           |FE((g1,Or(x,y))) ->(if ((r=x) and (equalsets g g1)) then true else false)
                                                                                                           |ImpI(px,(g1,r1))->(false)
                                                                                                           |ImpE(px,py,(g1,Or(x,y)))->(if ((r=x) and (equalsets g g1)) then true else false)
                                                                                                           |AndI(px,py,(g1,Or(x,y)))-> (if ((r=x) and (equalsets g g1)) then true else false)
                                                                                                           |AndEleft(px,(g1,Or(x,y)))-> (if ((r=x) and (equalsets g g1)) then true else false)
                                                                                                           |AndEright(px,(g1,Or(x,y)))-> (if ((r=x) and (equalsets g g1)) then true else false)
                                                                                                           |OrIleft(px,(g1,Or(x,y)))-> (false)
                                                                                                           |OrIright(px,(g1,Or(x,y)))-> (false)
                                                                                                           |OrE(px,py,pz,(g1,Or(x,y)))->(if ((r=x) and (equalsets g g1)) then true else false)
                                                                                                           |NotClass(px,(g1,Or(x,y)))-> (if ((r=x) and (equalsets g g1)) then true else false) 
                                                                                                           |NotIntu(px,(g1,Or(x,y)))->(if ((r=x) and (equalsets g g1)) then true else false)
                                                                                                           |_-> false) && (match p2 with) && (match p3 with))  else false)
						 *)|NotClass(p,(g,r))-> (if (wfprooftree p) then ( match p with
                                                              Ass((g1,r1))-> (if ((find_val g1 Not(r)) and (equalsets g1 (union g ([Not(r)]))) and (r1=F)) then true else false)
                                                             |TI(g1,r1) -> (if ((find_val g1 Not(r)) and (equalsets g1 (union g ([Not(r)])))and (r1=F)) then true else false)
                                                             |FE((g1, r1)) ->(if ((find_val g1 Not(r)) and (equalsets g1 (union g ([Not(r)]))) and (r1=F)) then true else false)
                                                             |ImpI(px,(g1,r1))->(if ((find_val g1 Not(r)) and (equalsets g1 (union g ([Not(r)]))) and (r1=F)) then true else false)
                                                             |ImpE(px,py,(g1,r1 ))->(if ((find_val g1 Not(r)) and (equalsets g1 (union g ([Not(r)]))) and (r1=F)) then true else false)
                                                             |AndI(px,py,(g1,r1 ))->(if ((find_val g1 Not(r)) and (equalsets g1 (union g ([Not(r)]))) and (r1=F)) then true else false)
                                                             |AndEleft(px,(g1,r1))->(if ((find_val g1 Not(r)) and (equalsets g1 (union g ([Not(r)]))) and (r1=F)) then true else false)
                                                             |AndEright(px,(g1,r1))->(if ((find_val g1 Not(r)) and (equalsets g1 (union g ([Not(r)]))) and (r1=F)) then true else false)
                                                             |OrIleft(px,(g1,r1))->(if ((find_val g1 Not(r)) and (equalsets g1 (union g ([Not(r)]))) and (r1=F)) then true else false)
                                                             |OrIright(px,(g1,r1 ))->(if ((find_val g1 Not(r)) and (equalsets g1 (union g ([Not(r)]))) and (r1=F)) then true else false)
                                                             |OrE(px,py,pz,(g1,r1))->(if ((find_val g1 Not(r)) and (equalsets g1 (union g ([Not(r)]))) and (r1=F)) then true else false)
                                                             |NotClass(px,(g1,r1 ))->(if ((find_val g1 Not(r)) and (equalsets g1 (union g ([Not(r)]))) and (r1=F)) then true else false) 
                                                             |NotIntu(px,(g1, r1))->(if ((find_val g1 Not(r)) and (equalsets g1 (union g ([Not(r)]))) and (r1=F)) then true else false)
                                                             |_-> false )  else false)
						 |NotIntu(p,(g,r))-> (if (wfprooftree p) then ( match p with 
                                                              Ass((g1,r1))-> (if ((find_val g1 r) and (equalsets g1 (union g ([r]))) and (r1=F)) then true else false)
                                                             |TI(g1,r1) -> (if ((find_val g1 r) and (equalsets g1 (union g ([r])))and (r1=F)) then true else false)
                                                             |FE((g1, r1)) ->(if ((find_val g1 r) and (equalsets g1 (union g ([r]))) and (r1=F)) then true else false)
                                                             |ImpI(px,(g1,r1))->(if ((find_val g1 r) and (equalsets g1 (union g ([r]))) and (r1=F)) then true else false)
                                                             |ImpE(px,py,(g1,r1 ))->(if ((find_val g1 r) and (equalsets g1 (union g ([r]))) and (r1=F)) then true else false)
                                                             |AndI(px,py,(g1,r1 ))->(if ((find_val g1 r) and (equalsets g1 (union g ([r]))) and (r1=F)) then true else false)
                                                             |AndEleft(px,(g1,r1))->(if ((find_val g1 r) and (equalsets g1 (union g ([r]))) and (r1=F)) then true else false)
                                                             |AndEright(px,(g1,r1))->(if ((find_val g1 r) and (equalsets g1 (union g ([r]))) and (r1=F)) then true else false)
                                                             |OrIleft(px,(g1,r1))->(if ((find_val g1 r) and (equalsets g1 (union g ([r]))) and (r1=F)) then true else false)
                                                             |OrIright(px,(g1,r1 ))->(if ((find_val g1 r) and (equalsets g1 (union g ([r]))) and (r1=F)) then true else false)
                                                             |OrE(px,py,pz,(g1,r1))->(if ((find_val g1 r) and (equalsets g1 (union g ([r]))) and (r1=F)) then true else false)
                                                             |NotClass(px,(g1,r1 ))->(if ((find_val g1 r) and (equalsets g1 (union g ([r]))) and (r1=F)) then true else false) 
                                                             |NotIntu(px,(g1, r1))->(if ((find_val g1 r) and (equalsets g1 (union g ([r]))) and (r1=F)) then true else false)
                                                             |_-> false ) else false) ;;
                                                             *) 
(*Write a function pad, that given a well-formed proof tree and a set of additional assumptions, creates a new well-formed proof tree with the set of additional assumptions added at each node. (F1)*)

let rec pad x y = match x with
                 Ass(s)-> ( match s with
                              (g,r)->Ass((append g y),r))     
                 |TI(s) -> (match s with
                              (g,r)->TI((append g y),r)) 
                 |FE(s) -> (match s with
                              (g,r)->FE((append g y),r))
                 |ImpI(p,s)-> (match s with
                              (g,r)->ImpI((pad p y), ((append g y),r)))
                 |ImpE(p1,p2,s)->  (match s with
                              (g,r)->ImpE((pad p1 y),( pad p2 y),((append g y),r)))
                 |AndI(p1,p2,s)->  (match s with
                              (g,r)->AndI((pad p1 y),(pad p2 y),((append g y),r)))
                 |AndEleft(p,s)-> (match s with
                              (g,r)->AndEleft((pad p y),((append g y),r)))
                 |AndEright(p,s)->  (match s with
                              (g,r)->AndEright((pad p y),((append g y),r)))
                 |OrIleft(p,s)->  (match s with
                              (g,r)->OrIleft((pad p y),((append g y),r)))
                 |OrIright(p,s)->  (match s with
                              (g,r)->OrIright((pad p y),((append g y),r)))
                 |OrE(p1,p2,p3,s)->  (match s with
                              (g,r)->OrE((pad p1 y),(pad p2 y),(pad p3 y),((append g y),r)))
                 |NotClass(p,s)-> (match s with
                              (g,r)->NotClass((pad p y),((append g y),r)))  
                 |NotIntu(p,s)->  (match s with
                              (g,r)->NotIntu((pad p y),((append g y),r)))
;;  

(*Write a function pare that given a well-formed proof tree, returns a well-formed proof tree with minimal assumptions in each sequent.   (F2)*)  

let rec parex x y = match x with
                    Ass((g,r))-> y @[r]
                   |TI((g,r)) -> y @[r]
                   |FE((g,r)) -> y @[r]
                   |ImpI(p,(g,r))-> parex p y
                   |ImpE(p1,p2,(g,r))-> (parex p1 y ) @ (parex p2 y)
                   |AndI(p1,p2,(g,r))-> (parex p1 y)@(parex p2 y)
                   |AndEleft(p,(g,r))-> parex p y
                   |AndEright(p,(g,r))-> parex p y
                   |OrIleft(p,(g,r))-> parex p y
                   |OrIright(p,(g,r))-> parex p y
                   |OrE(p1,p2,p3,(g,r))->(parex p1 y)@(parex p2 y)@(parex p3 y)
                   |NotClass(p,(g,r))-> parex p y 
                   |NotIntu(p,(g,r))-> parex p y;; 

let rec change_tree t x = match t with
                    Ass((g,r))-> Ass(( intersect g x), r)
                   |TI((g,r)) ->TI((intersect g x), r)
                   |FE((g,r)) -> FE((intersect g x), r)
                   |ImpI(p,(g,Implies(c,d)))->ImpI((change_tree p x), ((intersect g x), Implies(c,d)))
                   |ImpE(p1,p2,(g,r))-> ImpE((change_tree p1 x),(change_tree p2 x), ((intersect g x), r)) 
                   |AndI(p1,p2,(g,r))-> AndI((change_tree p1 x),(change_tree p2 x), ((intersect g x), r))
                   |AndEleft(p,(g,r))-> AndEleft((change_tree p x), ((intersect g x), r))
                   |AndEright(p,(g,r))-> AndEright((change_tree p x), ((intersect g x), r))
                   |OrIleft(p,(g,r))-> OrIleft((change_tree p x), ((intersect g x), r))
                   |OrIright(p,(g,r))-> OrIright((change_tree p x), ((intersect g x), r))
                   |OrE(p1,p2,p3,(g,r))->OrE((change_tree p1 x),(change_tree p2 x),(change_tree p3 x), ((intersect g x), r))
                   |NotClass(p,(g,r))-> NotClass((change_tree p x), ((intersect g x), r)) 
                   |NotIntu(p,(g,r))-> NotIntu((change_tree p x), ((intersect g x), r));; 



let rec pare x= match x with
                    Ass((g,r))->(change_tree x (parex x [] ))
                   |TI((g,r)) ->(change_tree x (parex x [] ))
                   |FE((g,r)) -> (change_tree x (parex x [] ))
                   |ImpI(p,(g,r))-> (change_tree x (parex x []))
                   |ImpE(p1,p2,(g,r))-> (change_tree x (parex x []))
                   |AndI(p1,p2,(g,r))-> (change_tree x (parex x []))
                   |AndEleft(p,(g,r))->(change_tree x (parex x []))
                   |AndEright(p,(g,r))->(change_tree x (parex x []))
                   |OrIleft(p,(g,r))-> (change_tree x (parex x []))
                   |OrIright(p,(g,r))-> (change_tree x (parex x []))
                   |OrE(p1,p2,p3,(g,r))->(change_tree x (parex x []))
                   |NotClass(p,(g,r))-> (change_tree x (parex x [])) 
                   |NotIntu(p,(g,r))-> (change_tree x (parex x []));;


  
(* Write a function graft that given a proof tree pi_0 of D |- p and a list of i proof trees pi_i for G |- q_i for each q_i   in D, returns a proof
 tree for G |- p, where the trees for  G |- q_i have replaced the leaves of the form D' |- q_i in a proof tree similar in shape to  pi_0.  (F3)*)

let rec add_tree s t= match s with 
                       Ass((g,r))-> (match t with 
                                                  []->  (Ass(g,r))
                                                 | x::xs-> match x with
                                                              Ass((g1,r1))-> (if (r1=r) then Ass((g1, r1)) else add_tree s xs )
                                                             |TI((g1,r1)) -> (if (r1=r) then TI((g1,r1)) else add_tree s xs )
                                                             |FE((g1,r1)) -> (if (r1=r) then FE((g1,r1)) else add_tree s xs )
                                                             |ImpI(p1,(g1,r1))-> (if (r1=r) then ImpI(p1,(g1,r1)) else add_tree s xs )
                                                             |ImpE(p1,p2,(g1,r1))-> (if (r1=r) then ImpE(p1,p2,(g1,r1)) else add_tree s xs ) 
                                                             |AndI(p1,p2,(g1,r1))-> (if (r1=r) then AndI(p1,p2,(g1,r1)) else add_tree s xs )
                                                             |AndEleft(p1,(g1,r1))->(if (r1=r) then AndEleft(p1,(g1,r1)) else add_tree s xs )
                                                             |AndEright(p1,(g1,r1))->(if (r1=r) then AndEright(p1,(g1,r1)) else add_tree s xs )
                                                             |OrIleft(p1,(g1,r1))->(if (r1=r) then OrIleft(p1,(g1,r1)) else add_tree s xs )
                                                             |OrIright(p1,(g1,r1))->(if (r1=r) then OrIright(p1,(g1,r1)) else add_tree s xs )
                                                             |OrE(p1,p2,p3,(g1,r1))->(if (r1=r) then OrE(p1,p2,p3,(g1,r1)) else add_tree s xs )
                                                             |NotClass(p1,(g1,r1))-> (if (r1=r) then NotClass(p1,(g1,r1)) else add_tree s xs )
                                                             |NotIntu(p1,(g1,r1))-> (if (r1=r) then NotIntu(p1,(g1,r1)) else add_tree s xs )
                                      
                                               )
                       |TI((g,r)) ->(match t with 
                                                  []->  (TI((g,r)))
                                                 |x::xs-> match x with
                                                              Ass((g1,r1))-> (if (r1=r) then Ass((g1, r1)) else add_tree s xs )
                                                             |TI((g1,r1)) -> (if (r1=r) then TI((g1,r1)) else add_tree s xs )
                                                             |FE((g1,r1)) -> (if (r1=r) then FE((g1,r1)) else add_tree s xs )
                                                             |ImpI(p1,(g1,r1))-> (if (r1=r) then ImpI(p1,(g1,r1)) else add_tree s xs )
                                                             |ImpE(p1,p2,(g1,r1))-> (if (r1=r) then ImpE(p1,p2,(g1,r1)) else add_tree s xs ) 
                                                             |AndI(p1,p2,(g1,r1))-> (if (r1=r) then AndI(p1,p2,(g1,r1)) else add_tree s xs )
                                                             |AndEleft(p1,(g1,r1))->(if (r1=r) then AndEleft(p1,(g1,r1)) else add_tree s xs )
                                                             |AndEright(p1,(g1,r1))->(if (r1=r) then AndEright(p1,(g1,r1)) else add_tree s xs )
                                                             |OrIleft(p1,(g1,r1))->(if (r1=r) then OrIleft(p1,(g1,r1)) else add_tree s xs )
                                                             |OrIright(p1,(g1,r1))->(if (r1=r) then OrIright(p1,(g1,r1)) else add_tree s xs )
                                                             |OrE(p1,p2,p3,(g1,r1))->(if (r1=r) then OrE(p1,p2,p3,(g1,r1)) else add_tree s xs )
                                                             |NotClass(p1,(g1,r1))-> (if (r1=r) then NotClass(p1,(g1,r1)) else add_tree s xs )
                                                             |NotIntu(p1,(g1,r1))-> (if (r1=r) then NotIntu(p1,(g1,r1)) else add_tree s xs )
                                      
                                               )
                       |FE((g,r)) -> (match t with 
                                                  []->  (FE((g,r)))
                                                 |x::xs-> match x with
                                                              Ass((g1,r1))-> (if (r1=r) then Ass((g1, r1)) else add_tree s xs )
                                                             |TI((g1,r1)) -> (if (r1=r) then TI((g1,r1)) else add_tree s xs )
                                                             |FE((g1,r1)) -> (if (r1=r) then FE((g1,r1)) else add_tree s xs )
                                                             |ImpI(p1,(g1,r1))-> (if (r1=r) then ImpI(p1,(g1,r1)) else add_tree s xs )
                                                             |ImpE(p1,p2,(g1,r1))-> (if (r1=r) then ImpE(p1,p2,(g1,r1)) else add_tree s xs ) 
                                                             |AndI(p1,p2,(g1,r1))-> (if (r1=r) then AndI(p1,p2,(g1,r1)) else add_tree s xs )
                                                             |AndEleft(p1,(g1,r1))->(if (r1=r) then AndEleft(p1,(g1,r1)) else add_tree s xs )
                                                             |AndEright(p1,(g1,r1))->(if (r1=r) then AndEright(p1,(g1,r1)) else add_tree s xs )
                                                             |OrIleft(p1,(g1,r1))->(if (r1=r) then OrIleft(p1,(g1,r1)) else add_tree s xs )
                                                             |OrIright(p1,(g1,r1))->(if (r1=r) then OrIright(p1,(g1,r1)) else add_tree s xs )
                                                             |OrE(p1,p2,p3,(g1,r1))->(if (r1=r) then OrE(p1,p2,p3,(g1,r1)) else add_tree s xs )
                                                             |NotClass(p1,(g1,r1))-> (if (r1=r) then NotClass(p1,(g1,r1)) else add_tree s xs )
                                                             |NotIntu(p1,(g1,r1))-> (if (r1=r) then NotIntu(p1,(g1,r1)) else add_tree s xs )
                                      );;

let find_g x= match x with
                        Ass((g,r))-> g
                        |TI((g,r)) -> g 
                        |FE((g,r))-> g 
                        |ImpI(p,(g,r)) -> g
                        |ImpE(p1,p2,(g,r))-> g
                        |AndI(p1,p2,(g,r))-> g
                        |AndEleft(p,(g,r))-> g
                        |AndEright(p,(g,r))-> g 
                        |OrIleft(p,(g,r))-> g
                        |OrIright(p,(g,r))-> g
                        |OrE(p1,p2,p3,(g,r))-> g
                        |NotClass(p,(g,r))-> g
                        |NotIntu(p,(g,r)) -> g;; 


let rec graft x y= match x with
                        Ass((g,r))-> add_tree x y
                       |TI((g,r)) -> add_tree x y
                       |FE((g,r)) -> add_tree x y
                       |ImpI(p,(g,r))-> ImpI((graft p y), ( find_g (graft p y) , r))
                       |ImpE(p1,p2,(g,r))-> ImpE((graft p1 y),(graft p2 y),(find_g (graft p1 y),r))
                       |AndI(p1,p2,(g,r))-> AndI((graft p1 y),(graft p2 y),(find_g (graft p1 y),r))
                       |AndEleft(p,(g,r))->AndEleft((graft p y),(find_g (graft p y),r))
                       |AndEright(p,(g,r))-> AndEright((graft p y),(find_g (graft p y),r))
                       |OrIleft(p,(g,r))-> OrIleft((graft p y),(find_g (graft p y),r))
                       |OrIright(p,(g,r))-> OrIright((graft p y),(find_g (graft p y),r))
                       |OrE(p1,p2,p3,(g,r))->OrE((graft p1 y),(graft p2 y),(graft p3 y),(find_g (graft p1 y),r))
                       |NotClass(p,(g,r))->NotClass((graft p y),(find_g (graft p y),r))
                       |NotIntu(p,(g,r))-> NotIntu((graft p y),(find_g (graft p y),r));;
(*
    Write a program normalise which removes all occurrences of r-pairs in a given well-formed proof tree (i.e., where an introduction rule is followed only by an  elimination rule of the main connective).*)


(*let rec normalise x= match x with
                    Ass(s)->Ass(s) 
                   |TI(s) ->TI(s) 
                   |FE(s) ->FE(s)
                   |ImpI(p,s)-> ImpI((normalise p),s) 
                   |ImpE(p1,p2,s)-> 
                   |AndI(p1,p2,s)-> AndI((normalise p1),(normalise p2),s)
                   |AndEleft(p,s)-> size(p)+1
                   |AndEright(p,s)-> size(p)+1
                   |OrIleft(p,s)-> OrIleft((normalise p), s)
                   |OrIright(p,s)-> OrIright((normalise p), s)
                   |OrE(p1,p2,p3,s)-> 1+ size(p1)+size(p2)+size(p3)
                   |NotClass(p,s)-> NotClass((normalise p), s) 
                   |NotIntu(p,s)-> NotIntu((normalise p), s) ;; *) 


let gamma = [P "p2";P "p1";P "p3"];;
let gamma2 = [And (P "p",P "q");Or (P "p2",P"q2")];; 
let test_tree1 = Ass (gamma ,P "p1") ;;
let test_tree2 = Ass (gamma ,P"p2") ;; 
let test_tree3 = AndI (test_tree1,test_tree2,(gamma,(And (P "p1",P"p2"))));; 
let test_tree4 = AndEleft (test_tree3,(gamma,P "p2"));; 
let test_fE    = FE (F::gamma,P "p1");; 
let test_tree5 = Ass (gamma2,And (P "p",P "q")) ;; 
let test_tree6 = ImpI (test_tree5,([Or (P "p2",P "q2")],Implies (And (P "p",P "q"),And(P "p",P "q"))));;
let gamma3 = [P "a"; P "b"];; 
let tq1 = Ass (gamma3,P "a");;
let tq2 = Ass (gamma3,P "b");; 
let q1 = AndI (tq1, tq2, (gamma3,(And (P "a",P "b"))));;
let q2 = OrIleft (tq2, (gamma3,(Or(P "b",P "c"))));; 
let delta1 = [And (P "a",P"b")];; 
let tp1 = Ass (delta1,(And (P "a",P "b")));; 
let p = AndEleft (tp1,(delta1,(P "a")));; 
let tree_nor = AndEleft (q1,(gamma,P "a"));;



(*wfprooftree test_tree4;;
- : bool = false


# wfprooftree test_fE;;
- : bool = true*)


pad test_tree4 [P "p3";P "p4"];;
(*- : prooftree =
AndEleft(AndI (Ass ([P "p3"; P "p4"; P "p2"; P "p1"], P "p1"),Ass ([P 
"p3"; P "p4"; P "p2"; P "p1"], P "p2"), ([P "p3"; P "p4"; P "p2"; P 
"p1"], And (P "p1", P "p2"))), ([P "p3"; P "p4"; P "p2"; P "p1"], P "p2"))*)


# pare test_tree6;; - :
(*prooftree = ImpI (Ass ([And (P "p", P "q")], And (P "p", P "q")), ([], Implies (And
(P "p", P "q"), And (P "p", P "q"))))*)

graft p [q1;q2];;
(*- : prooftree = AndEleft (AndI (Ass ([P "a"; P "b"], P "a"),Ass ([P "a"; 
P "b"], P "b"),([P "a"; P "b"], And (P "a", P "b"))),([P "a"; P "b"], P 
"a"))


# normalize tree_nor;;
- : prooftree = Ass ([P "a"; P "b"], P "a")*)
