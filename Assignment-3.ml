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

let rec size x = match x with
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

let rec verify x y z = match x with
                         Ass((g,r))-> (if ((equalsets y g) && (r=z)) then true else false)
                        |TI((g,r)) ->(if ((equalsets y g) && (r=z)) then true else false) 
                        |FE((g,r)) ->(if ((equalsets y g) && (r=z)) then true else false)
                        |ImpI(p,(g,r))->(if ((equalsets y g) && (r=z)) then true else false)
                        |ImpE(p1,p2,(g,r))->(if ((equalsets y g) && (r=z)) then true else false)
                        |AndI(p1,p2,(g,r))-> (if ((equalsets y g) && (r=z)) then true else false)
                        |AndEleft(p,(g,r))-> (if ((equalsets y g) && (r=z)) then true else false)
                        |AndEright(p,(g,r))-> (if ((equalsets y g) && (r=z)) then true else false)
                        |OrIleft(p,(g,r))-> (if ((equalsets y g) && (r=z)) then true else false)
                        |OrIright(p,(g,r))-> (if ((equalsets y g) && (r=z)) then true else false)
                        |OrE(p1,p2,p3,(g,r))-> (if ((equalsets y g) && (r=z)) then true else false)
                        |NotClass(p,(g,r))-> (if ((equalsets y g) && (r=z)) then true else false)
                        |NotIntu(p,(g,r))-> (if ((equalsets y g) && (r=z)) then true else false)
                         ;; 
let rec verify_or a b c d= match a with
                         Ass((g,r))-> if (find_val g b) && (r=c) && (equalsets g (union d [b])) then true else false
                        |TI((g,r)) -> if (find_val g b) && (r=c) && (equalsets g (union d [b])) then true else false
                        |FE((g,r)) -> if (find_val g b) && (r=c) && (equalsets g (union d [b])) then true else false
                        |ImpI(p,(g,r))-> if (find_val g b) && (r=c) && (equalsets g (union d [b])) then true else false
                        |ImpE(p1,p2,(g,r))-> if (find_val g b) && (r=c) && (equalsets g (union d [b])) then true else false
                        |AndI(p1,p2,(g,r))-> if (find_val g b) && (r=c) && (equalsets g (union d [b])) then true else false
                        |AndEleft(p,(g,r))->  if (find_val g b) && (r=c) && (equalsets g (union d [b])) then true else false
                        |AndEright(p,(g,r))->  if (find_val g b) && (r=c) && (equalsets g (union d [b])) then true else false
                        |OrIleft(p,(g,r))->  if (find_val g b) && (r=c) && (equalsets g (union d [b])) then true else false
                        |OrIright(p,(g,r))-> if (find_val g b) && (r=c) && (equalsets g (union d [b])) then true else false
                        |OrE(p1,p2,p3,(g,r))-> if (find_val g b) && (r=c) && (equalsets g (union d [b])) then true else false
                        |NotClass(p,(g,r))-> if (find_val g b) && (r=c) && (equalsets g (union d [b])) then true else false
                        |NotIntu(p,(g,r))-> if (find_val g b) && (r=c) && (equalsets g (union d [b])) then true else false
                        ;;

let rec wfprooftree x = match x with
                         Ass((g,r))->(if (find_val g r) then true else false)
                        |TI((g,r)) -> (if (r=T) then true else false) 
                        |FE(g, r) -> (if ((find_val g r) && (find_val g F)) then true else false)
                        |ImpI(p,(g, Implies(v,w)))-> if (wfprooftree p) then (match p with
                                                                                 Ass((g,r))->( if ((find_val g v) && (w=r)) then true else false)
                                                                                |TI((g,r)) -> (if ((find_val g v) && (w=r)) then true else false)
                                                                                |FE((g,r)) ->(if ((find_val g v) && (w=r)) then true else false)
                                                                                |ImpI(p,(g,r))-> (if ((find_val g v) && (w=r)) then true else false)
                                                                                |ImpE(p1,p2,(g,r))-> (if ((find_val g v) && (w=r)) then true else false)
                                                                                |AndI(p1,p2,(g,r))-> (if ((find_val g v) && (w=r)) then true else false)
                                                                                |AndEleft(p,(g,r))-> (if ((find_val g v) && (w=r)) then true else false)
                                                                                |AndEright(p,(g,r))-> (if ((find_val g v) && (w=r)) then true else false)
                                                                                |OrIleft(p,(g,r))-> (if ((find_val g v) && (w=r)) then true else false)
                                                                                |OrIright(p,(g,r))-> ( if ((find_val g v) && (w=r)) then true else false)
                                                                                |OrE(p1,p2,p3,(g,r))-> (if ((find_val g v) && (w=r)) then true else false)
                                                                                |NotClass(p,(g,r))-> (if ((find_val g v) && (w=r)) then true else false) 
                                                                                |NotIntu(p,(g,r))->(if ((find_val g v) && (w=r)) then true else false) 
                                                                                ) else false
                        |ImpE(p1,p2,(g,r))-> if ((wfprooftree p1) && (wfprooftree p2)) then (match p1 with
                                                                                               Ass((g1,Implies(v,w)))->( if ((equalsets g g1) && (w=r)) then verify p2 g v else false)
                                                                                              |TI((g1,Implies(v,w))) -> (if ((equalsets g g1) && (w=r)) then verify p2 g v else false)
                                                                                              |FE((g1,Implies(v,w))) ->(if ((equalsets g g1) && (w=r)) then verify p2 g v else false)
                                                                                              |ImpI(px,(g1,Implies(v,w)))-> (if ((equalsets g g1) && (w=r)) then verify p2 g v else false)
                                                                                              |ImpE(px1,px2,(g1,Implies(v,w)))-> (if ((equalsets g g1) && (w=r)) then verify p2 g v else false)
                                                                                              |AndI(px1,px2,(g1,Implies(v,w)))-> (if ((equalsets g g1) && (w=r)) then verify p2 g v else false)
                                                                                              |AndEleft(px,(g1,Implies(v,w)))-> (if ((equalsets g g1) && (w=r)) then verify p2 g v else false)
                                                                                              |AndEright(px,(g1,Implies(v,w)))-> (if ((equalsets g g1) && (w=r)) then verify p2 g v else false)
                                                                                              |OrIleft(px,(g1,Implies(v,w)))-> (if ((equalsets g g1) && (w=r)) then verify p2 g v else false)
                                                                                              |OrIright(px,(g1,Implies(v,w)))-> ( if ((equalsets g g1) && (w=r)) then verify p2 g v else false)
                                                                                              |OrE(px1,px2,px3,(g1,Implies(v,w)))-> (if ((equalsets g g1) && (w=r)) then verify p2 g v else false)
                                                                                              |NotClass(px,(g1,Implies(v,w)))-> (if ((equalsets g g1) && (w=r)) then verify p2 g v else false) 
                                                                                              |NotIntu(px,(g1,Implies(v,w)))->(if ((equalsets g g1) && (w=r)) then verify p2 g v else false)
                                                                                              ) else false 
                        |AndI(p1,p2,(g,And(v,w)))-> if ((wfprooftree p1) && (wfprooftree p2)) then ( match p1 with
                                                                                                         Ass((g1,r1))-> (if (equalsets g g1) && (r1 =v) then true else false)
                                                                                                         |TI((g1,r1)) -> (if (equalsets g g1) && (r1 =v) then true else false)
                                                                                                         |FE((g1,r1)) ->(if (equalsets g g1) && (r1 = v) then true else false)
                                                                                                         |ImpI(px,(g1,r1))->(if (equalsets g g1) && (r1 =v) then true else false) 
                                                                                                         |ImpE(px,py,(g1,r1))-> (if (equalsets g g1) && (r1 =v) then true else false)
                                                                                                         |AndI(px,py,(g1,r1))-> (if (equalsets g g1) && (r1 =v) then true else false)
                                                                                                         |AndEleft(px,(g1,r1))-> (if (equalsets g g1) && (r1 =v) then true else false)
                                                                                                         |AndEright(px,(g1,r1))-> (if (equalsets g g1) && (r1 =v) then true else false)
                                                                                                         |OrIleft(px,(g1,r1))-> (if (equalsets g g1) && (r1 =v) then true else false)
                                                                                                         |OrIright(px,(g1,r1))-> (if (equalsets g g1) && (r1 =v) then true else false)
                                                                                                         |OrE(px,py,pz,(g1,r1))->(if (equalsets g g1) && (r1 =v) then true else false)
                                                                                                         |NotClass(px,(g1,r1))-> (if (equalsets g g1) && (r1 =v) then true else false) 
                                                                                                         |NotIntu(px,(g1,r1))->(if (equalsets g g1) && (r1 =v) then true else false)
                                                                                                         ) && (match p2 with
                                                                                                                              Ass((g1,r1))-> (if (equalsets g g1) && (r1 =w) then true else false)
                                                                                                                              |TI((g1,r1)) -> (if (equalsets g g1) && (r1 =w) then true else false)
                                                                                                                              |FE((g1,r1)) ->(if (equalsets g g1) && (r1 = w) then true else false)
                                                                                                                              |ImpI(px,(g1,r1))->(if (equalsets g g1) && (r1 =w) then true else false) 
                                                                                                                              |ImpE(px,py,(g1,r1))-> (if (equalsets g g1) && (r1 =w) then true else false)
                                                                                                                              |AndI(px,py,(g1,r1))-> (if (equalsets g g1) && (r1 =w) then true else false)
                                                                                                                              |AndEleft(px,(g1,r1))-> (if (equalsets g g1) && (r1 =w) then true else false)
                                                                                                                              |AndEright(px,(g1,r1))-> (if (equalsets g g1) && (r1 =w) then true else false)
                                                                                                                              |OrIleft(px,(g1,r1))-> (if (equalsets g g1) && (r1 =w) then true else false)
                                                                                                                              |OrIright(px,(g1,r1))-> (if (equalsets g g1) && (r1 =w) then true else false)
                                                                                                                              |OrE(px,py,pz,(g1,r1))->(if (equalsets g g1) && (r1 =w) then true else false)
                                                                                                                              |NotClass(px,(g1,r1))-> (if (equalsets g g1) && (r1 =w) then true else false) 
                                                                                                                              |NotIntu(px,(g1,r1))->(if (equalsets g g1) && (r1 =w) then true else false)
                                                                                                                              ) else false
                        |AndEleft(p,(g,r))-> if (wfprooftree p) then (match p with 
                                                                           |TI((g1,And(x,y))) -> (if ((r=x) && (equalsets g g1)) then true else false)
                                                                           |FE((g1,And(x,y))) ->(if ((r=x) && (equalsets g g1)) then true else false)
                                                                           |ImpI(px,(g1,r1))->(false)
                                                                           |ImpE(px,py,(g1,And(x,y)))->(if ((r=x) && (equalsets g g1)) then true else false)
                                                                           |AndI(px,py,(g1,And(x,y)))-> (if ((r=x) && (equalsets g g1)) then true else false)
                                                                           |AndEleft(px,(g1,And(x,y)))-> (if ((r=x) && (equalsets g g1)) then true else false)
                                                                           |AndEright(px,(g1,And(x,y)))-> (if ((r=x) && (equalsets g g1)) then true else false)
                                                                           |OrIleft(px,(g1,And(x,y)))-> (false)
                                                                           |OrIright(px,(g1,And(x,y)))-> (false)
                                                                           |OrE(px,py,pz,(g1,And(x,y)))->(if ((r=x) && (equalsets g g1)) then true else false)
                                                                           |NotClass(px,(g1,And(x,y)))-> (if ((r=x) && (equalsets g g1)) then true else false) 
                                                                           |NotIntu(px,(g1,And(x,y)))->(if ((r=x) && (equalsets g g1)) then true else false)
                                                                           ) else false 
                        |AndEright(p,(g,r))-> if (wfprooftree p) then (match p with 
                                                                           |TI((g1,And(x,y))) -> (if ((r=y) && (equalsets g g1)) then true else false)
                                                                           |FE((g1,And(x,y))) ->(if ((r=y) && (equalsets g g1)) then true else false)
                                                                           |ImpI(px,(g1,And(x,y)))->(if ((r=y) && (equalsets g g1)) then true else false)
                                                                           |ImpE(px,py,(g1,And(x,y)))->(if ((r=y) && (equalsets g g1)) then true else false)
                                                                           |AndI(px,py,(g1,And(x,y)))-> (if ((r=y) && (equalsets g g1)) then true else false)
                                                                           |AndEleft(px,(g1,And(x,y)))-> (if ((r=y) && (equalsets g g1)) then true else false)
                                                                           |AndEright(px,(g1,And(x,y)))-> (if ((r=y) && (equalsets g g1)) then true else false)
                                                                           |OrIleft(px,(g1,And(x,y)))-> (if ((r=y) && (equalsets g g1)) then true else false)
                                                                           |OrIright(px,(g1,And(x,y)))-> (if ((r=y) && (equalsets g g1)) then true else false)
                                                                           |OrE(px,py,pz,(g1,And(x,y)))->(if ((r=y) && (equalsets g g1)) then true else false)
                                                                           |NotClass(px,(g1,And(x,y)))-> (if ((r=y) && (equalsets g g1)) then true else false) 
                                                                           |NotIntu(px,(g1,And(x,y)))->(if ((r=y) && (equalsets g g1)) then true else false)
                                                                           ) else false 
                        |OrIleft(p,(g,Or(v,w)))-> if (wfprooftree p) then (  match p with 
                                                                                   Ass((g1,r1))-> (if (( r1=v) && (equalsets g g1)) then true else false)
                                                                                  |TI(g1,r1) -> (if (( r1=v) && (equalsets g g1)) then true else false)
                                                                                  |FE((g1, r1)) ->(if (( r1=v) && (equalsets g g1)) then true else false)
                                                                                  |ImpI(px,(g1,r1))->(if (( r1=v) && (equalsets g g1)) then true else false)
                                                                                  |ImpE(px,py,(g1,r1 ))->(if (( r1=v) && (equalsets g g1)) then true else false)
                                                                                  |AndI(px,py,(g1,r1 ))->(if (( r1=v) && (equalsets g g1)) then true else false)
                                                                                  |AndEleft(px,(g1,r1))->(if (( r1=v) && (equalsets g g1)) then true else false)
                                                                                  |AndEright(px,(g1,r1))->(if (( r1=v) && (equalsets g g1)) then true else false)
                                                                                  |OrIleft(px,(g1,r1))->(if (( r1=v) && (equalsets g g1)) then true else false)
                                                                                  |OrIright(px,(g1,r1 ))->(if (( r1=v) && (equalsets g g1)) then true else false)
                                                                                  |OrE(px,py,pz,(g1,r1))->(if (( r1=v) && (equalsets g g1)) then true else false)
                                                                                  |NotClass(px,(g1,r1 ))->(if (( r1=v) && (equalsets g g1)) then true else false) 
                                                                                  |NotIntu(px,(g1, r1))->(if (( r1=v) && (equalsets g g1)) then true else false)
                                                                                   )  else false
                        |OrIright(p,(g, Or(v,w)))-> if (wfprooftree p) then (  match p with 
                                                                                   Ass((g1,r1))-> (if (( r1=w) && (equalsets g g1)) then true else false)
                                                                                  |TI(g1,r1) -> (if (( r1=w) && (equalsets g g1)) then true else false)
                                                                                  |FE((g1, r1)) ->(if (( r1=w) && (equalsets g g1)) then true else false)
                                                                                  |ImpI(px,(g1,r1))->(if (( r1=w) && (equalsets g g1)) then true else false)
                                                                                  |ImpE(px,py,(g1,r1 ))->(if (( r1=w) && (equalsets g g1)) then true else false)
                                                                                  |AndI(px,py,(g1,r1 ))->(if (( r1=w) && (equalsets g g1)) then true else false)
                                                                                  |AndEleft(px,(g1,r1))->(if (( r1=w) && (equalsets g g1)) then true else false)
                                                                                  |AndEright(px,(g1,r1))->(if (( r1=w) && (equalsets g g1)) then true else false)
                                                                                  |OrIleft(px,(g1,r1))->(if (( r1=w) && (equalsets g g1)) then true else false)
                                                                                  |OrIright(px,(g1,r1 ))->(if (( r1=w) && (equalsets g g1)) then true else false)
                                                                                  |OrE(px,py,pz,(g1,r1))->(if (( r1=w) && (equalsets g g1)) then true else false)
                                                                                  |NotClass(px,(g1,r1 ))->(if (( r1=w) && (equalsets g g1)) then true else false) 
                                                                                  |NotIntu(px,(g1, r1))->(if (( r1=w) && (equalsets g g1)) then true else false)
                                                                                  )  else false
                        |OrE(p1,p2,p3,(g,r))-> if (wfprooftree p1) && (wfprooftree p2) && (wfprooftree p3) then (match p1 with
                                                                                                               Ass((g1,Or(v,w)))-> (if ((equalsets g g1)) then verify_or p2 v r g && verify_or p3 w r g else false)
                                                                                                              |TI(g1,Or(v,w)) -> (if ( (equalsets g g1)) then verify_or p2 v r g && verify_or p3 w r g else false)
                                                                                                              |FE((g1, Or(v,w))) ->(if ( (equalsets g g1)) then verify_or p2 v r g && verify_or p3 w r g else false)
                                                                                                              |ImpI(px,(g1,Or(v,w)))->(if ((equalsets g g1)) then verify_or p2 v r g && verify_or p3 w r g else false)
                                                                                                              |ImpE(px,py,(g1,Or(v,w) ))->(if ((equalsets g g1)) then verify_or p2 v r g && verify_or p3 w r g else false)
                                                                                                              |AndI(px,py,(g1,Or(v,w) ))->(if ((equalsets g g1)) then verify_or p2 v r g && verify_or p3 w r g else false)
                                                                                                              |AndEleft(px,(g1,Or(v,w)))->(if ((equalsets g g1)) then verify_or p2 v r g && verify_or p3 w r g else false)
                                                                                                              |AndEright(px,(g1,Or(v,w)))->(if ( (equalsets g g1)) then verify_or p2 v r g && verify_or p3 w r g else false)
                                                                                                              |OrIleft(px,(g1,Or(v,w)))->(if ( (equalsets g g1)) then verify_or p2 v r g && verify_or p3 w r g else false)
                                                                                                              |OrIright(px,(g1,Or(v,w) ))->(if ((equalsets g g1)) then verify_or p2 v r g && verify_or p3 w r g else false)
                                                                                                              |OrE(px,py,pz,(g1,Or(v,w)))->(if ((equalsets g g1)) then verify_or p2 v r g && verify_or p3 w r g else false)
                                                                                                              |NotClass(px,(g1,Or(v,w)))->(if ((equalsets g g1)) then verify_or p2 v r g && verify_or p3 w r g else false) 
                                                                                                              |NotIntu(px,(g1,Or(v,w)))->(if ((equalsets g g1)) then verify_or p2 v r g && verify_or p3 w r g else false)
                                                                                                              ) else false
                        |NotClass(p,(g,r))-> if (wfprooftree p) then (match p with
                                                                            Ass((g1,r1))-> (if ((find_val g1 (Not(r))) && (equalsets g1 (union g ([Not(r)]))) && (r1=F)) then true else false)
                                                                           |TI(g1,r1) -> (if ((find_val g1 (Not(r))) && (equalsets g1 (union g ([Not(r)]))) && (r1=F)) then true else false)
                                                                           |FE((g1, r1)) ->(if ((find_val g1 (Not(r))) && (equalsets g1 (union g ([Not(r)]))) && (r1=F)) then true else false)
                                                                           |ImpI(px,(g1,r1))->(if ((find_val g1 (Not(r))) && (equalsets g1 (union g ([Not(r)]))) && (r1=F)) then true else false)
                                                                           |ImpE(px,py,(g1,r1 ))->(if ((find_val g1 (Not(r))) && (equalsets g1 (union g ([Not(r)]))) && (r1=F)) then true else false)
                                                                           |AndI(px,py,(g1,r1 ))->(if ((find_val g1 (Not(r))) && (equalsets g1 (union g ([Not(r)]))) && (r1=F)) then true else false)
                                                                           |AndEleft(px,(g1,r1))->(if ((find_val g1 (Not(r))) && (equalsets g1 (union g ([Not(r)]))) && (r1=F)) then true else false)
                                                                           |AndEright(px,(g1,r1))->(if ((find_val g1 (Not(r))) && (equalsets g1 (union g ([Not(r)]))) && (r1=F)) then true else false)
                                                                           |OrIleft(px,(g1,r1))->(if ((find_val g1 (Not(r))) && (equalsets g1 (union g ([Not(r)]))) && (r1=F)) then true else false)
                                                                           |OrIright(px,(g1,r1 ))->(if ((find_val g1 (Not(r))) && (equalsets g1 (union g ([Not(r)]))) && (r1=F)) then true else false)
                                                                           |OrE(px,py,pz,(g1,r1))->(if ((find_val g1 (Not(r))) && (equalsets g1 (union g ([Not(r)]))) && (r1=F)) then true else false)
                                                                           |NotClass(px,(g1,r1 ))->(if ((find_val g1 (Not(r))) && (equalsets g1 (union g ([Not(r)]))) && (r1=F)) then true else false) 
                                                                           |NotIntu(px,(g1, r1))->(if ((find_val g1 (Not(r))) && (equalsets g1 (union g ([Not(r)]))) && (r1=F)) then true else false)
                                                                           ) else false 
                        |NotIntu(p,(g,r))-> if (wfprooftree p) then ( match p with 
                                                                            Ass((g1,r1))-> (if ((equalsets g1 g) && (r1=F)) then true else false)
                                                                           |TI(g1,r1) -> (if ((equalsets g1 g) && (r1=F)) then true else false)
                                                                           |FE((g1, r1)) ->(if ((equalsets g1 g) && (r1=F)) then true else false)
                                                                           |ImpI(px,(g1,r1))->(if ((equalsets g1 g) && (r1=F)) then true else false)
                                                                           |ImpE(px,py,(g1,r1 ))->(if ((equalsets g1 g) && (r1=F)) then true else false)
                                                                           |AndI(px,py,(g1,r1 ))->(if ((equalsets g1 g) && (r1=F)) then true else false)
                                                                           |AndEleft(px,(g1,r1))->(if ((equalsets g1 g) && (r1=F)) then true else false)
                                                                           |AndEright(px,(g1,r1))->(if ((equalsets g1 g) && (r1=F)) then true else false)
                                                                           |OrIleft(px,(g1,r1))->(if ((equalsets g1 g) && (r1=F)) then true else false)
                                                                           |OrIright(px,(g1,r1 ))->(if ((equalsets g1 g) && (r1=F)) then true else false)
                                                                           |OrE(px,py,pz,(g1,r1))->(if ((equalsets g1 g) && (r1=F)) then true else false)
                                                                           |NotClass(px,(g1,r1 ))->(if ((equalsets g1 g) && (r1=F)) then true else false) 
                                                                           |NotIntu(px,(g1, r1))->(if ((equalsets g1 g) && (r1=F)) then true else false)
                                                                           ) else false
                 ;; 
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
                   |ImpI(p,(g,r))->ImpI((change_tree p x), ((intersect g x), r))
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

let rec add x y= match x with
                         Ass((g,r))->Ass ( union g [y], r)
                        |TI((g,r)) -> TI(union g [y], r) 
                        |FE((g,r))-> FE(union g [y], r) 
                        |ImpI(p,(g,r)) -> ImpI(p,(union g [y],r))
                        |ImpE(p1,p2,(g,r))-> ImpE(p1,p2,(union g [y],r))
                        |AndI(p1,p2,(g,r))-> AndI(p1,p2,(union g [y],r))
                        |AndEleft(p,(g,r))-> AndEleft(p,(union g [y],r))
                        |AndEright(p,(g,r))-> AndEright(p,(union g [y],r))
                        |OrIleft(p,(g,r))-> OrIleft(p,(union g [y],r))
                        |OrIright(p,(g,r))-> OrIright(p,(union g [y],r))
                        |OrE(p1,p2,p3,(g,r))->OrE(p1,p2,p3,(union g [y],r))
                        |NotClass(p,(g,r))->NotClass(p,(union g [y],r))
                        |NotIntu(p,(g,r)) ->NotIntu(p,(union g [y],r))
                      ;;


let rec graft x y= match x with
                        Ass((g,r))-> add_tree x y
                       |TI((g,r)) -> add_tree x y
                       |FE((g,r)) -> add_tree x y
                       |ImpI(p,(g,Implies(r,s)))-> ImpI(add (graft p y) r, (find_g (graft p y) , Implies(r,s)))
                       |ImpE(p1,p2,(g,r))-> ImpE((graft p1 y),(graft p2 y),(find_g (graft p1 y),r))
                       |AndI(p1,p2,(g,r))-> AndI((graft p1 y),(graft p2 y),(find_g (graft p1 y),r))
                       |AndEleft(p,(g,r))->AndEleft((graft p y),(find_g (graft p y),r))
                       |AndEright(p,(g,r))-> AndEright((graft p y),(find_g (graft p y),r))
                       |OrIleft(p,(g,r))-> OrIleft((graft p y),(find_g (graft p y),r))
                       |OrIright(p,(g,r))-> OrIright((graft p y),(find_g (graft p y),r))
                       |OrE(p1,p2,p3,(g,r))->(match p1 with
                                                   Ass((g,And(v,w)))-> OrE((graft p1 y),add (graft p2 y) v, add (graft p3 y) w,(find_g (graft p1 y),r))
                                                  |TI((g,And(v,w))) -> OrE((graft p1 y),add (graft p2 y) v, add (graft p3 y) w,(find_g (graft p1 y),r))
                                                  |FE((g,And(v,w)))-> OrE((graft p1 y),add (graft p2 y) v, add (graft p3 y) w,(find_g (graft p1 y),r))
                                                  |ImpI(p,(g,And(v,w))) ->OrE((graft p1 y),add (graft p2 y) v, add (graft p3 y) w,(find_g (graft p1 y),r))
                                                  |ImpE(p1,p2,(g,And(v,w)))->OrE((graft p1 y),add (graft p2 y) v, add (graft p3 y) w,(find_g (graft p1 y),r))
                                                  |AndI(p1,p2,(g,And(v,w)))->OrE((graft p1 y),add (graft p2 y) v, add (graft p3 y) w,(find_g (graft p1 y),r)) 
                                                  |AndEleft(p,(g,And(v,w)))->OrE((graft p1 y),add (graft p2 y) v, add (graft p3 y) w,(find_g (graft p1 y),r))
                                                  |AndEright(p,(g,And(v,w)))->OrE((graft p1 y),add (graft p2 y) v, add (graft p3 y) w,(find_g (graft p1 y),r)) 
                                                  |OrIleft(p,(g,And(v,w)))-> OrE((graft p1 y),add (graft p2 y) v, add (graft p3 y) w,(find_g (graft p1 y),r))
                                                  |OrIright(p,(g,And(v,w)))-> OrE((graft p1 y),add (graft p2 y) v, add (graft p3 y) w,(find_g (graft p1 y),r))
                                                  |OrE(p1,p2,p3,(g,And(v,w)))->OrE((graft p1 y),add (graft p2 y) v, add (graft p3 y) w,(find_g (graft p1 y),r))
                                                  |NotClass(p,(g,And(v,w)))-> OrE((graft p1 y),add (graft p2 y) v, add (graft p3 y) w,(find_g (graft p1 y),r))
                                                  |NotIntu(p,(g,And(v,w))) -> OrE((graft p1 y),add (graft p2 y) v, add (graft p3 y) w,(find_g (graft p1 y),r))) 
                       |NotClass(p,(g,r))->NotClass((graft p y),(find_g (graft p y),r))
                       |NotIntu(p,(g,r))-> NotIntu((graft p y),(find_g (graft p y),r));;

(*
    Write a program normalise which removes all occurrences of r-pairs in a given well-formed proof tree (i.e., where an introduction rule is followed only by an  elimination rule of the main connective).*)
let add_norm x y = match x with
                        Ass((g,r))-> (match y with
                                        Ass((g1,r1))-> graft (Ass((difference g [r1], r))) [y]
                                        |TI((g1,r1)) ->   graft (Ass((difference g [r1], r))) [y]
                                        |FE((g1,r1))->  graft (Ass((difference g [r1], r))) [y]
                                        |ImpI(px,(g1,r1)) ->  graft (Ass((difference g [r1], r))) [y]
                                        |ImpE(px,py,(g1,r1))->  graft (Ass((difference g [r1], r))) [y]
                                        |AndI(px,py,(g1,r1))->   graft (Ass((difference g [r1], r))) [y]
                                        |AndEleft(px,(g1,r1))->  graft (Ass((difference g [r1], r))) [y]
                                        |AndEright(px,(g1,r1))->  graft (Ass((difference g [r1], r))) [y] 
                                        |OrIleft(px,(g1,r1))->   graft (Ass((difference g [r1], r))) [y]
                                        |OrIright(px,(g1,r1))->   graft (Ass((difference g [r1], r))) [y]
                                        |OrE(px,py,pz,(g1,r1))->   graft (Ass((difference g [r1], r))) [y] 
                                        |NotClass(px,(g1,r1))->   graft (Ass((difference g [r1], r))) [y]
                                        |NotIntu(px,(g1,r1)) ->  graft (Ass((difference g [r1], r))) [y]
                                      )

                        |TI((g,r)) -> (match y with
                                        Ass((g1,r1))-> graft (TI((difference g [r1], r))) [y]
                                        |TI((g1,r1)) ->   graft (TI((difference g [r1], r))) [y]
                                        |FE((g1,r1))->  graft (TI((difference g [r1], r))) [y]
                                        |ImpI(px,(g1,r1)) ->  graft (TI((difference g [r1], r))) [y]
                                        |ImpE(px,py,(g1,r1))->graft (TI((difference g [r1], r))) [y]
                                        |AndI(px,py,(g1,r1))-> graft (TI((difference g [r1], r))) [y]
                                        |AndEleft(px,(g1,r1))->graft (TI((difference g [r1], r))) [y]
                                        |AndEright(px,(g1,r1))-> graft (TI((difference g [r1], r))) [y]
                                        |OrIleft(px,(g1,r1))-> graft (TI((difference g [r1], r))) [y]
                                        |OrIright(px,(g1,r1))->graft (TI((difference g [r1], r))) [y]
                                        |OrE(px,py,pz,(g1,r1))->graft (TI((difference g [r1], r))) [y]
                                        |NotClass(px,(g1,r1))->graft (TI((difference g [r1], r))) [y]
                                        |NotIntu(px,(g1,r1)) ->graft (TI((difference g [r1], r))) [y]
                                      ) 
                        |FE((g,r))-> (match y with
                                        Ass((g1,r1))-> graft (FE((difference g [r1], r))) [y]
                                        |TI((g1,r1)) -> graft (FE((difference g [r1], r))) [y]
                                        |FE((g1,r1))-> graft (FE((difference g [r1], r))) [y]
                                        |ImpI(px,(g1,r1)) -> graft (FE((difference g [r1], r))) [y]
                                        |ImpE(px,py,(g1,r1))->graft (FE((difference g [r1], r))) [y]
                                        |AndI(px,py,(g1,r1))->graft (FE((difference g [r1], r))) [y]
                                        |AndEleft(px,(g1,r1))->graft (FE((difference g [r1], r))) [y]
                                        |AndEright(px,(g1,r1))->graft (FE((difference g [r1], r))) [y] 
                                        |OrIleft(px,(g1,r1))->graft (FE((difference g [r1], r))) [y]
                                        |OrIright(px,(g1,r1))-> graft (FE((difference g [r1], r))) [y]
                                        |OrE(px,py,pz,(g1,r1))-> graft (FE((difference g [r1], r))) [y]
                                        |NotClass(px,(g1,r1))->graft (FE((difference g [r1], r))) [y]
                                        |NotIntu(px,(g1,r1)) ->graft (FE((difference g [r1], r))) [y]
                                      )  
                        |ImpI(p,(g,r)) -> (match y with
                                        Ass((g1,r1))-> graft (ImpI(p,(difference g [r1], r))) [y]
                                        |TI((g1,r1)) -> graft (ImpI(p,(difference g [r1], r))) [y]
                                        |FE((g1,r1))-> graft (ImpI(p,(difference g [r1], r))) [y]
                                        |ImpI(px,(g1,r1)) ->graft (ImpI(p,(difference g [r1], r))) [y]
                                        |ImpE(px,py,(g1,r1))->graft (ImpI(p,(difference g [r1], r))) [y]
                                        |AndI(px,py,(g1,r1))-> graft (ImpI(p,(difference g [r1], r))) [y]
                                        |AndEleft(px,(g1,r1))->graft (ImpI(p,(difference g [r1], r))) [y]
                                        |AndEright(px,(g1,r1))->graft (ImpI(p,(difference g [r1], r))) [y]
                                        |OrIleft(px,(g1,r1))->graft (ImpI(p,(difference g [r1], r))) [y]
                                        |OrIright(px,(g1,r1))->graft (ImpI(p,(difference g [r1], r))) [y]
                                        |OrE(px,py,pz,(g1,r1))->graft (ImpI(p,(difference g [r1], r))) [y]
                                        |NotClass(px,(g1,r1))->graft (ImpI(p,(difference g [r1], r))) [y]
                                        |NotIntu(px,(g1,r1)) -> graft (ImpI(p,(difference g [r1], r))) [y]
                                      )
                        |ImpE(p1,p2,(g,r))-> (match y with
                                        Ass((g1,r1))-> graft (ImpE(p1,p2,(difference g [r1], r))) [y]
                                        |TI((g1,r1)) -> graft (ImpE(p1,p2,(difference g [r1], r))) [y]
                                        |FE((g1,r1))->  graft (ImpE(p1,p2,(difference g [r1], r))) [y]
                                        |ImpI(px,(g1,r1)) ->graft (ImpE(p1,p2,(difference g [r1], r))) [y]
                                        |ImpE(px,py,(g1,r1))->graft (ImpE(p1,p2,(difference g [r1], r))) [y]
                                        |AndI(px,py,(g1,r1))->graft (ImpE(p1,p2,(difference g [r1], r))) [y]
                                        |AndEleft(px,(g1,r1))->graft (ImpE(p1,p2,(difference g [r1], r))) [y]
                                        |AndEright(px,(g1,r1))->graft (ImpE(p1,p2,(difference g [r1], r))) [y]
                                        |OrIleft(px,(g1,r1))->graft (ImpE(p1,p2,(difference g [r1], r))) [y]
                                        |OrIright(px,(g1,r1))->graft (ImpE(p1,p2,(difference g [r1], r))) [y]
                                        |OrE(px,py,pz,(g1,r1))->graft (ImpE(p1,p2,(difference g [r1], r))) [y]
                                        |NotClass(px,(g1,r1))->graft (ImpE(p1,p2,(difference g [r1], r))) [y]
                                        |NotIntu(px,(g1,r1)) ->graft (ImpE(p1,p2,(difference g [r1], r))) [y]
                                      )
                        |AndI(p1,p2,(g,r))-> (match y with
                                        Ass((g1,r1))-> graft (AndI(p1,p2,(difference g [r1], r))) [y]
                                        |TI((g1,r1)) -> graft (AndI(p1,p2,(difference g [r1], r))) [y]
                                        |FE((g1,r1))-> graft (AndI(p1,p2,(difference g [r1], r))) [y]
                                        |ImpI(px,(g1,r1)) -> graft (AndI(p1,p2,(difference g [r1], r))) [y]
                                        |ImpE(px,py,(g1,r1))->  graft (AndI(p1,p2,(difference g [r1], r))) [y]
                                        |AndI(px,py,(g1,r1))->  graft (AndI(p1,p2,(difference g [r1], r))) [y]
                                        |AndEleft(px,(g1,r1))-> graft (AndI(p1,p2,(difference g [r1], r))) [y]
                                        |AndEright(px,(g1,r1))-> graft (AndI(p1,p2,(difference g [r1], r))) [y]
                                        |OrIleft(px,(g1,r1))-> graft (AndI(p1,p2,(difference g [r1], r))) [y]
                                        |OrIright(px,(g1,r1))-> graft (AndI(p1,p2,(difference g [r1], r))) [y]
                                        |OrE(px,py,pz,(g1,r1))-> graft (AndI(p1,p2,(difference g [r1], r))) [y] 
                                        |NotClass(px,(g1,r1))-> graft (AndI(p1,p2,(difference g [r1], r))) [y]
                                        |NotIntu(px,(g1,r1)) -> graft (AndI(p1,p2,(difference g [r1], r))) [y]
                                      )
                        |AndEleft(p,(g,r))->(match y with
                                        Ass((g1,r1))-> graft (AndEleft(p,(difference g [r1], r))) [y]
                                        |TI((g1,r1)) ->  graft (AndEleft(p,(difference g [r1], r))) [y]
                                        |FE((g1,r1))->  graft (AndEleft(p,(difference g [r1], r))) [y]
                                        |ImpI(px,(g1,r1)) -> graft (AndEleft(p,(difference g [r1], r))) [y]
                                        |ImpE(px,py,(g1,r1))->  graft (AndEleft(p,(difference g [r1], r))) [y]
                                        |AndI(px,py,(g1,r1))->  graft (AndEleft(p,(difference g [r1], r))) [y]
                                        |AndEleft(px,(g1,r1))-> graft (AndEleft(p,(difference g [r1], r))) [y]
                                        |AndEright(px,(g1,r1))-> graft (AndEleft(p,(difference g [r1], r))) [y]
                                        |OrIleft(px,(g1,r1))-> graft (AndEleft(p,(difference g [r1], r))) [y]
                                        |OrIright(px,(g1,r1))-> graft (AndEleft(p,(difference g [r1], r))) [y]
                                        |OrE(px,py,pz,(g1,r1))-> graft (AndEleft(p,(difference g [r1], r))) [y] 
                                        |NotClass(px,(g1,r1))-> graft (AndEleft(p,(difference g [r1], r))) [y]
                                        |NotIntu(px,(g1,r1)) ->  graft (AndEleft(p,(difference g [r1], r))) [y]
                                      )
                        |AndEright(p,(g,r))-> (match y with
                                        Ass((g1,r1))-> graft (AndEright(p,(difference g [r1], r))) [y]
                                        |TI((g1,r1)) ->graft (AndEright(p,(difference g [r1], r))) [y]
                                        |FE((g1,r1))->graft (AndEright(p,(difference g [r1], r))) [y]
                                        |ImpI(px,(g1,r1)) ->graft (AndEright(p,(difference g [r1], r))) [y]
                                        |ImpE(px,py,(g1,r1))->graft (AndEright(p,(difference g [r1], r))) [y]
                                        |AndI(px,py,(g1,r1))-> graft (AndEright(p,(difference g [r1], r))) [y]
                                        |AndEleft(px,(g1,r1))->graft (AndEright(p,(difference g [r1], r))) [y]
                                        |AndEright(px,(g1,r1))->graft (AndEright(p,(difference g [r1], r))) [y]
                                        |OrIleft(px,(g1,r1))->graft (AndEright(p,(difference g [r1], r))) [y]
                                        |OrIright(px,(g1,r1))->graft (AndEright(p,(difference g [r1], r))) [y]
                                        |OrE(px,py,pz,(g1,r1))-> graft (AndEright(p,(difference g [r1], r))) [y]
                                        |NotClass(px,(g1,r1))->graft (AndEright(p,(difference g [r1], r))) [y]
                                        |NotIntu(px,(g1,r1)) ->graft (AndEright(p,(difference g [r1], r))) [y]
                                      )
                        |OrIleft(p,(g,r))-> (match y with
                                        Ass((g1,r1))-> graft (OrIleft(p,(difference g [r1], r))) [y]
                                        |TI((g1,r1)) ->graft (OrIleft(p,(difference g [r1], r))) [y]
                                        |FE((g1,r1))-> graft (OrIleft(p,(difference g [r1], r))) [y]
                                        |ImpI(px,(g1,r1)) ->graft (OrIleft(p,(difference g [r1], r))) [y]
                                        |ImpE(px,py,(g1,r1))-> graft (OrIleft(p,(difference g [r1], r))) [y]
                                        |AndI(px,py,(g1,r1))-> graft (OrIleft(p,(difference g [r1], r))) [y]
                                        |AndEleft(px,(g1,r1))->graft (OrIleft(p,(difference g [r1], r))) [y]
                                        |AndEright(px,(g1,r1))->graft (OrIleft(p,(difference g [r1], r))) [y]
                                        |OrIleft(px,(g1,r1))->graft (OrIleft(p,(difference g [r1], r))) [y]
                                        |OrIright(px,(g1,r1))->graft (OrIleft(p,(difference g [r1], r))) [y]
                                        |OrE(px,py,pz,(g1,r1))-> graft (OrIleft(p,(difference g [r1], r))) [y]
                                        |NotClass(px,(g1,r1))->graft (OrIleft(p,(difference g [r1], r))) [y]
                                        |NotIntu(px,(g1,r1)) ->graft (OrIleft(p,(difference g [r1], r))) [y]
                                      )
                        |OrIright(p,(g,r))-> (match y with
                                        Ass((g1,r1))-> graft (OrIright(p,(difference g [r1], r))) [y]
                                        |TI((g1,r1)) ->  graft (OrIright(p,(difference g [r1], r))) [y]
                                        |FE((g1,r1))-> graft (OrIright(p,(difference g [r1], r))) [y]
                                        |ImpI(px,(g1,r1)) -> graft (OrIright(p,(difference g [r1], r))) [y]
                                        |ImpE(px,py,(g1,r1))-> graft (OrIright(p,(difference g [r1], r))) [y]
                                        |AndI(px,py,(g1,r1))-> graft (OrIright(p,(difference g [r1], r))) [y]
                                        |AndEleft(px,(g1,r1))-> graft (OrIright(p,(difference g [r1], r))) [y]
                                        |AndEright(px,(g1,r1))-> graft (OrIright(p,(difference g [r1], r))) [y]
                                        |OrIleft(px,(g1,r1))-> graft (OrIright(p,(difference g [r1], r))) [y]
                                        |OrIright(px,(g1,r1))-> graft (OrIright(p,(difference g [r1], r))) [y]
                                        |OrE(px,py,pz,(g1,r1))-> graft (OrIright(p,(difference g [r1], r))) [y] 
                                        |NotClass(px,(g1,r1))-> graft (OrIright(p,(difference g [r1], r))) [y]
                                        |NotIntu(px,(g1,r1)) -> graft (OrIright(p,(difference g [r1], r))) [y]
                                      )
                        |OrE(p1,p2,p3,(g,r))-> (match y with
                                        Ass((g1,r1))-> graft (OrE(p1,p2,p3,(difference g [r1], r))) [y]
                                        |TI((g1,r1)) -> graft (OrE(p1,p2,p3,(difference g [r1], r))) [y]
                                        |FE((g1,r1))-> graft (OrE(p1,p2,p3,(difference g [r1], r))) [y]
                                        |ImpI(px,(g1,r1)) -> graft (OrE(p1,p2,p3,(difference g [r1], r))) [y]
                                        |ImpE(px,py,(g1,r1))-> graft (OrE(p1,p2,p3,(difference g [r1], r))) [y]
                                        |AndI(px,py,(g1,r1))-> graft (OrE(p1,p2,p3,(difference g [r1], r))) [y]
                                        |AndEleft(px,(g1,r1))-> graft (OrE(p1,p2,p3,(difference g [r1], r))) [y]
                                        |AndEright(px,(g1,r1))-> graft (OrE(p1,p2,p3,(difference g [r1], r))) [y]
                                        |OrIleft(px,(g1,r1))-> graft (OrE(p1,p2,p3,(difference g [r1], r))) [y]
                                        |OrIright(px,(g1,r1))-> graft (OrE(p1,p2,p3,(difference g [r1], r))) [y]
                                        |OrE(px,py,pz,(g1,r1))-> graft (OrE(p1,p2,p3,(difference g [r1], r))) [y]
                                        |NotClass(px,(g1,r1))-> graft (OrE(p1,p2,p3,(difference g [r1], r))) [y]
                                        |NotIntu(px,(g1,r1)) ->  graft (OrE(p1,p2,p3,(difference g [r1], r))) [y]
                                      )
                        |NotClass(p,(g,r))-> (match y with
                                        Ass((g1,r1))-> graft (NotClass(p,(difference g [r1], r))) [y]
                                        |TI((g1,r1)) ->  graft (NotClass(p,(difference g [r1], r))) [y]
                                        |FE((g1,r1))-> graft (NotClass(p,(difference g [r1], r))) [y]
                                        |ImpI(px,(g1,r1)) ->graft (NotClass(p,(difference g [r1], r))) [y]
                                        |ImpE(px,py,(g1,r1))-> graft (NotClass(p,(difference g [r1], r))) [y]
                                        |AndI(px,py,(g1,r1))-> graft (NotClass(p,(difference g [r1], r))) [y]
                                        |AndEleft(px,(g1,r1))->graft (NotClass(p,(difference g [r1], r))) [y]
                                        |AndEright(px,(g1,r1))->graft (NotClass(p,(difference g [r1], r))) [y]
                                        |OrIleft(px,(g1,r1))->graft (NotClass(p,(difference g [r1], r))) [y]
                                        |OrIright(px,(g1,r1))->graft (NotClass(p,(difference g [r1], r))) [y]
                                        |OrE(px,py,pz,(g1,r1))-> graft (NotClass(p,(difference g [r1], r))) [y]
                                        |NotClass(px,(g1,r1))->graft (NotClass(p,(difference g [r1], r))) [y]
                                        |NotIntu(px,(g1,r1)) ->graft (NotClass(p,(difference g [r1], r))) [y]
                                      )
                        |NotIntu(p,(g,r)) -> (match y with
                                        Ass((g1,r1))-> graft (NotIntu(p,(difference g [r1], r))) [y]
                                        |TI((g1,r1)) ->graft (NotIntu(p,(difference g [r1], r))) [y]
                                        |FE((g1,r1))-> graft (NotIntu(p,(difference g [r1], r))) [y]
                                        |ImpI(px,(g1,r1)) ->graft (NotIntu(p,(difference g [r1], r))) [y]
                                        |ImpE(px,py,(g1,r1))-> graft (NotIntu(p,(difference g [r1], r))) [y]
                                        |AndI(px,py,(g1,r1))->graft (NotIntu(p,(difference g [r1], r))) [y]
                                        |AndEleft(px,(g1,r1))->graft (NotIntu(p,(difference g [r1], r))) [y]
                                        |AndEright(px,(g1,r1))->graft (NotIntu(p,(difference g [r1], r))) [y]
                                        |OrIleft(px,(g1,r1))->graft (NotIntu(p,(difference g [r1], r))) [y]
                                        |OrIright(px,(g1,r1))->graft (NotIntu(p,(difference g [r1], r))) [y]
                                        |OrE(px,py,pz,(g1,r1))-> graft (NotIntu(p,(difference g [r1], r))) [y] 
                                        |NotClass(px,(g1,r1))->graft (NotIntu(p,(difference g [r1], r))) [y]
                                        |NotIntu(px,(g1,r1)) ->graft (NotIntu(p,(difference g [r1], r))) [y]
                                      );;



let rec normalise x= match x with
                    Ass(s)->Ass(s) 
                   |TI(s) ->TI(s) 
                   |FE(s) ->FE(s)
                   |ImpI(p,s)-> ImpI((normalise p),s) 
                   |ImpE(p1,p2,s)-> (match p1 with
                                         Ass((g,r))->ImpE(normalise p1, normalise p2,s)
                                        |TI((g,r)) ->ImpE(normalise p1, normalise p2,s)
                                        |FE((g,r))->ImpE(normalise p1, normalise p2,s) 
                                        |ImpI(px,(g,r)) -> normalise (add_norm px p2)
                                        |ImpE(px,py,(g,r))-> ImpE(normalise p1, normalise p2,s)
                                        |AndI(px,py,(g,r))-> ImpE(normalise p1, normalise p2,s)
                                        |AndEleft(px,(g,r))-> ImpE(normalise p1, normalise p2,s)
                                        |AndEright(px,(g,r))->ImpE(normalise p1, normalise p2,s)
                                        |OrIleft(px,(g,r))-> ImpE(normalise p1, normalise p2,s)
                                        |OrIright(px,(g,r))-> ImpE(normalise p1, normalise p2,s)
                                        |OrE(px,py,pz,(g,r))->ImpE(normalise p1, normalise p2,s)
                                        |NotClass(px,(g,r))->ImpE(normalise p1, normalise p2,s)
                                        |NotIntu(px,(g,r)) ->ImpE(normalise p1, normalise p2,s))
                   |AndI(p1,p2,s)-> AndI((normalise p1),(normalise p2),s)
                   |AndEleft(p,s)-> (match p with
                                        Ass((g,r))->AndEleft((normalise p),s) 
                                        |TI((g,r)) ->AndEleft((normalise p),s)
                                        |FE((g,r))->AndEleft((normalise p),s) 
                                        |ImpI(px,(g,r)) -> AndEleft((normalise p),s)
                                        |ImpE(px,py,(g,r))-> AndEleft((normalise p),s)
                                        |AndI(px,py,(g,r))-> normalise py
                                        |AndEleft(px,(g,r))-> AndEleft((normalise p),s)
                                        |AndEright(px,(g,r))->AndEleft((normalise p),s)
                                        |OrIleft(px,(g,r))-> AndEleft((normalise p),s)
                                        |OrIright(px,(g,r))->AndEleft((normalise p),s)
                                        |OrE(px,py,pz,(g,r))->AndEleft((normalise p),s)
                                        |NotClass(px,(g,r))->AndEleft((normalise p),s)
                                        |NotIntu(px,(g,r)) ->AndEleft((normalise p),s))
                   |AndEright(p,s)-> (match p with
                                        Ass((g,r))->AndEleft((normalise p),s) 
                                        |TI((g,r)) ->AndEleft((normalise p),s)
                                        |FE((g,r))->AndEleft((normalise p),s) 
                                        |ImpI(px,(g,r)) -> AndEleft((normalise p),s)
                                        |ImpE(px,py,(g,r))-> AndEleft((normalise p),s)
                                        |AndI(px,py,(g,r))-> normalise px
                                        |AndEleft(px,(g,r))-> AndEleft((normalise p),s)
                                        |AndEright(px,(g,r))->AndEleft((normalise p),s)
                                        |OrIleft(px,(g,r))-> AndEleft((normalise p),s)
                                        |OrIright(px,(g,r))->AndEleft((normalise p),s)
                                        |OrE(px,py,pz,(g,r))->AndEleft((normalise p),s)
                                        |NotClass(px,(g,r))->AndEleft((normalise p),s)
                                        |NotIntu(px,(g,r)) ->AndEleft((normalise p),s))
                   |OrIleft(p,s)-> OrIleft((normalise p), s)
                   |OrIright(p,s)-> OrIright((normalise p), s)
                   |OrE(p1,p2,p3,s)-> (match p1 with
                                        Ass((g,r))->OrE((normalise p1),(normalise p2),(normalise p3),s) 
                                        |TI((g,r)) ->OrE((normalise p1),(normalise p2),(normalise p3),s)
                                        |FE((g,r))->OrE((normalise p1),(normalise p2),(normalise p3),s) 
                                        |ImpI(px,(g,r)) -> OrE((normalise p1),(normalise p2),(normalise p3),s)
                                        |ImpE(px,py,(g,r))->OrE((normalise p1),(normalise p2),(normalise p3),s)
                                        |AndI(px,py,(g,r))-> OrE((normalise p1),(normalise p2),(normalise p3),s)
                                        |AndEleft(px,(g,r))-> OrE((normalise p1),(normalise p2),(normalise p3),s)
                                        |AndEright(px,(g,r))->OrE((normalise p1),(normalise p2),(normalise p3),s)
                                        |OrIleft(px,(g,r))-> normalise (add_norm p3 px)
                                        |OrIright(px,(g,r))-> normalise (add_norm p2 px)
                                        |OrE(px,py,pz,(g,r))->OrE((normalise p1),(normalise p2),(normalise p3),s)
                                        |NotClass(px,(g,r))->OrE((normalise p1),(normalise p2),(normalise p3),s)
                                        |NotIntu(px,(g,r)) ->OrE((normalise p1),(normalise p2),(normalise p3),s))
                   |NotClass(p,s)-> NotClass((normalise p), s) 
                   |NotIntu(p,s)-> NotIntu((normalise p), s)
    ;; 


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



wfprooftree test_tree4;;
(*- : bool = false*)


wfprooftree test_fE;;
(*- : bool = true*)


pad test_tree4 [P "p3";P "p4"];;
(*- : prooftree =
AndEleft(AndI (Ass ([P "p3"; P "p4"; P "p2"; P "p1"], P "p1"),Ass ([P 
"p3"; P "p4"; P "p2"; P "p1"], P "p2"), ([P "p3"; P "p4"; P "p2"; P 
"p1"], And (P "p1", P "p2"))), ([P "p3"; P "p4"; P "p2"; P "p1"], P "p2"))*)


pare test_tree6;;
(*prooftree = ImpI (Ass ([And (P "p", P "q")], And (P "p", P "q")), ([], Implies (And
(P "p", P "q"), And (P "p", P "q"))))*)

graft p [q1;q2];;
(*- : prooftree = AndEleft (AndI (Ass ([P "a"; P "b"], P "a"),Ass ([P "a"; 
P "b"], P "b"),([P "a"; P "b"], And (P "a", P "b"))),([P "a"; P "b"], P 
"a"))*)

normalise tree_nor;;
(*- : prooftree = Ass ([P "a"; P "b"], P "a")*)
let p12=Ass([(Implies(P"p", (Implies(P"q", P"r")))); (Implies(P"p", P"q")); P"p"], (P"p"));;
let p11=Ass([(Implies(P"p", (Implies(P"q", P"r")))); (Implies(P"p", P"q")); P"p"], (Implies(P"p", P"q")));;
let p10=Ass([(Implies(P"p", (Implies(P"q", P"r")))); (Implies(P"p", P"q")); P"p"], (P"p"));;
let p9=Ass([(Implies(P"p", (Implies(P"q", P"r")))); (Implies(P"p", P"q")); P"p"], (Implies(P"p", (Implies(P"q", P"r")))));;
let p8=ImpE(p11,p12, ([(Implies(P"p", (Implies(P"q", P"r")))); (Implies(P"p", P"q")); P"p"], (P"q")));;
let p7=ImpE(p9,p10, ([(Implies(P"p", (Implies(P"q", P"r")))); (Implies(P"p", P"q")); P"p"], (Implies(P"q", P"r"))));;
let p6=ImpE(p7, p8,  ([(Implies(P"p", (Implies(P"q", P"r")))); (Implies(P"p", P"q")); P"p"], (P"r")));;
let p5=ImpI(p6, ([(Implies(P"p", (Implies(P"q", P"r")))); (Implies(P"p", P"q"))], (Implies(P"p", P"r"))));;
let p4=ImpI(p5, ([(Implies(P"p", (Implies(P"q", P"r"))))], (Implies((Implies(P"p", P"q")),(Implies(P"p", P"r"))))));;
let p3=ImpI(p4, ([], (Implies((Implies(P"p", (Implies(P"q", P"r")))),(Implies((Implies(P"p", P"q")),(Implies(P"p", P"r")))) ))));;

let p2=Ass([P"p"; P"q"], P"p");;                          
let p1=ImpI(p2, ([P"p"],Implies(P"q", P"p") ));;                          
let p0=ImpI(p1, ([], (Implies(P"p", Implies(P"q",P"p")))) );;

wfprooftree p3;;
wfprooftree p0;
