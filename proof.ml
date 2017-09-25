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


let rec find_val s r= match s with
                  []->false
                 |x::xs-> if (x=r) then true
                                   else find_val xs r;;s

let rec append l1 l2 = match l1 with
                        []->l2
                        |x::xs -> if (find_val l2 x) then (append xs l2) else x::(append xs l2);;



let rec intersect s1 s2 = match s1 with 
                          []->[]
                          |x::xs -> match s2 with 
                                     []->[]
                                     | y::ys-> if (member s2 x) then x::intersect xs s2
                                                              else intersect xs s2;;


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


(*Define the function wfprooftree that check tat a given candidate proof tree is indeed a well-formed proof tree (i.e., the main formula is of the form expected by the rule, the side formulas are consistent with the main formula, and the extra formulas agree as specified in each rule).*)
   
let rec wfprooftree x = match x with
                          Ass((g,r))-> if (find_val g r) then true else false 
		         |TI((g,r)) -> if(r==T) then true else false 
		         |FE((g,r)) ->1
		         |ImpI(p,(g,r))-> if
		         |ImpE(p1,p2,(g,r))-> 1 + size(p1)+size(p2)
		         |AndI(p1,p2,(g,r))-> 1 + size(p1)+size(p2)
		         |AndEleft(p,(g,r))-> size(p)+1
		         |AndEright(p,(g,r))-> size(p)+1
		         |OrIleft(p,(g,r))-> size(p)+1
		         |OrIright(p,(g,r))-> size(p)+1
		         |OrE(p1,p2,p3,(g,r))-> 1+ size(p1)+size(p2)+size(p3)
		         |NotClass(p,(g,r))-> size(p)+1 
		         |NotIntu(p,(g,r))-> size(p)+1 ;;  



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

let rec pare x = match x with
                  Ass((g,r))->Ass((intersect g r), r) 
                 |TI(s) ->1 
                 |FE(s) ->1
                 |ImpI(p,(g,r))-> (match (pare p) with 
			                  Ass((g1,r1))->ImpI((pare p),(g1 ,r)) 
					 |TI((g1,r1)) ->ImpI((pare p),(g1 ,r)) 
					 |FE((g1,r1)) ->ImpI((pare p),(g1 ,r))
					 |ImpI(p,(g1,r))->ImpI((pare p),(g1 ,r))
					 |ImpE(p1,p2,(g1,r))->ImpI((pare p),(g1 ,r))
					 |AndI(p1,p2,(g1,r))->ImpI((pare p),(g1 ,r))
					 |AndEleft(p,(g1,r))->ImpI((pare p),(g1 ,r))
					 |AndEright(p,(g1,r))->ImpI((pare p),(g1 ,r))
					 |OrIleft(p,(g1,r))->ImpI((pare p),(g1 ,r))
					 |OrIright(p,(g1,r))->ImpI((pare p),(g1 ,r))
					 |OrE(p1,p2,p3,(g1,r))->ImpI((pare p),(g1 ,r))
					 |NotClass(p,(g1,r))->ImpI((pare p),(g1 ,r)) 
					 |NotIntu(p,(g1,r))->ImpI((pare p),(g1 ,r)))
                 |ImpE(p1,p2,(g,r))->(match (pare p) with 
			                  Ass((g1,r1))->ImpE((pare p),(g1 ,r)) 
					 |TI((g1,r1)) ->ImpE((pare p),(g1 ,r)) 
					 |FE((g1,r1)) ->ImpE((pare p),(g1 ,r))
					 |ImpI(p,(g1,r))->ImpE((pare p),(g1 ,r))
					 |ImpE(p1,p2,(g1,r))->ImpE((pare p),(g1 ,r))
					 |AndI(p1,p2,(g1,r))->ImpE((pare p),(g1 ,r))
					 |AndEleft(p,(g1,r))->ImpE((pare p),(g1 ,r))
					 |AndEright(p,(g1,r))->ImpE((pare p),(g1 ,r))
					 |OrIleft(p,(g1,r))->ImpE((pare p),(g1 ,r))
					 |OrIright(p,(g1,r))->ImpE((pare p),(g1 ,r))
					 |OrE(p1,p2,p3,(g1,r))->ImpE((pare p),(g1 ,r))
					 |NotClass(p,(g1,r))->ImpE((pare p),(g1 ,r)) 
					 |NotIntu(p,(g1,r))->ImpE((pare p),(g1 ,r)))
                 |AndI(p1,p2,(g,r))->(match (pare p1) with 
			                  Ass((g1,r1))->ImpI((pare p),(g1 ,r)) 
					 |TI((g1,r1)) ->ImpI((pare p),(g1 ,r)) 
					 |FE((g1,r1)) ->ImpI((pare p),(g1 ,r))
					 |ImpI(p,(g1,r))->ImpI((pare p),(g1 ,r))
					 |ImpE(p1,p2,(g1,r))->ImpI((pare p),(g1 ,r))
					 |AndI(p1,p2,(g1,r))->ImpI((pare p),(g1 ,r))
					 |AndEleft(p,(g1,r))->ImpI((pare p),(g1 ,r))
					 |AndEright(p,(g1,r))->>ImpI((pare p),(g1 ,r))
					 |OrIleft(p,(g1,r))->ImpI((pare p),(g1 ,r))
					 |OrIright(p,(g1,r))->ImpI((pare p),(g1 ,r))
					 |OrE(p1,p2,p3,(g1,r))->ImpI((pare p),(g1 ,r))
					 |NotClass(p,(g1,r))->ImpI((pare p),(g1 ,r)) 
					 |NotIntu(p,(g1,r))->ImpI((pare p),(g1 ,r)))
                 |AndEleft(p,(g,r))->(match (pare p) with 
			                  Ass((g1,r1))->AndEleft((pare p),(g1 ,r)) 
					 |TI((g1,r1)) ->AndEleft((pare p),(g1 ,r)) 
					 |FE((g1,r1)) ->AndEleft((pare p),(g1 ,r))
					 |ImpI(p,(g1,r))->AndEleft((pare p),(g1 ,r))
					 |ImpE(p1,p2,(g1,r))->AndEleft((pare p),(g1 ,r))
					 |AndI(p1,p2,(g1,r))->AndEleft((pare p),(g1 ,r))
					 |AndEleft(p,(g1,r))->AndEleft((pare p),(g1 ,r))
					 |AndEright(p,(g1,r))->>AndEleft((pare p),(g1 ,r))
					 |OrIleft(p,(g1,r))->AndEleft((pare p),(g1 ,r))
					 |OrIright(p,(g1,r))->AndEleft((pare p),(g1 ,r))
					 |OrE(p1,p2,p3,(g1,r))->AndEleft((pare p),(g1 ,r))
					 |NotClass(p,(g1,r))->AndEleft((pare p),(g1 ,r)) 
					 |NotIntu(p,(g1,r))->AndEleft((pare p),(g1 ,r)))
                 |AndEright(p,(g,r))->(match (pare p) with 
			                  Ass((g1,r1))->AndEright((pare p),(g1 ,r)) 
					 |TI((g1,r1)) ->AndEright((pare p),(g1 ,r)) 
					 |FE((g1,r1)) ->AndEright((pare p),(g1 ,r))
					 |ImpI(p,(g1,r))->AndEright((pare p),(g1 ,r))
					 |ImpE(p1,p2,(g1,r))->AndEright((pare p),(g1 ,r))
					 |AndI(p1,p2,(g1,r))->AndEright((pare p),(g1 ,r))
					 |AndEleft(p,(g1,r))->AndEright((pare p),(g1 ,r))
					 |AndEright(p,(g1,r))->>AndEright((pare p),(g1 ,r))
					 |OrIleft(p,(g1,r))->AndEright((pare p),(g1 ,r))
					 |OrIright(p,(g1,r))->AndEright((pare p),(g1 ,r))
					 |OrE(p1,p2,p3,(g1,r))->AndEright((pare p),(g1 ,r))
					 |NotClass(p,(g1,r))->AndEright((pare p),(g1 ,r)) 
					 |NotIntu(p,(g1,r))->AndEright((pare p),(g1 ,r)))
                 |OrIleft(p,(g,r))->(match (pare p) with 
			                  Ass((g1,r1))->OrIleft((pare p),(g1 ,r)) 
					 |TI((g1,r1)) ->OrIleft((pare p),(g1 ,r)) 
					 |FE((g1,r1)) ->OrIleft((pare p),(g1 ,r))
					 |ImpI(p,(g1,r))->OrIleft((pare p),(g1 ,r))
					 |ImpE(p1,p2,(g1,r))->OrIleft((pare p),(g1 ,r))
					 |AndI(p1,p2,(g1,r))->OrIleft((pare p),(g1 ,r))
					 |AndEleft(p,(g1,r))->OrIleft((pare p),(g1 ,r))
					 |AndEright(p,(g1,r))->>OrIleft((pare p),(g1 ,r))
					 |OrIleft(p,(g1,r))->OrIleft((pare p),(g1 ,r))
					 |OrIright(p,(g1,r))->OrIleft((pare p),(g1 ,r))
					 |OrE(p1,p2,p3,(g1,r))->OrIleft((pare p),(g1 ,r))
					 |NotClass(p,(g1,r))->OrIleft((pare p),(g1 ,r)) 
					 |NotIntu(p,(g1,r))->OrIleft((pare p),(g1 ,r)))
                 |OrIright(p,(g,r))->(match (pare p) with 
			                  Ass((g1,r1))->OrIright((pare p),(g1 ,r)) 
					 |TI((g1,r1)) ->OrIright((pare p),(g1 ,r)) 
					 |FE((g1,r1)) ->OrIright((pare p),(g1 ,r))
					 |ImpI(p,(g1,r))->OrIright((pare p),(g1 ,r))
					 |ImpE(p1,p2,(g1,r))->OrIright((pare p),(g1 ,r))
					 |AndI(p1,p2,(g1,r))->OrIright((pare p),(g1 ,r))
					 |AndEleft(p,(g1,r))->OrIright((pare p),(g1 ,r))
					 |AndEright(p,(g1,r))->OrIright((pare p),(g1 ,r))
					 |OrIleft(p,(g1,r))->OrIright((pare p),(g1 ,r))
					 |OrIright(p,(g1,r))->OrIright((pare p),(g1 ,r))
					 |OrE(p1,p2,p3,(g1,r))->OrIright((pare p),(g1 ,r))
					 |NotClass(p,(g1,r))->OrIright((pare p),(g1 ,r)) 
					 |NotIntu(p,(g1,r))->OrIright((pare p),(g1 ,r)))
                 |OrE(p1,p2,p3,(g,r))->(match (pare p1) with 
			                  (Ass((g1,r1))|TI((g1,r1))|FE((g1,r1))|ImpI(p,(g1,r))|ImpE(p1,p2,(g1,r))|AndI(p1,p2,(g1,r))
					 |AndEleft(p,(g1,r))|AndEright(p,(g1,r))|OrIleft(p,(g1,r))|OrIright(p,(g1,r))|OrE(p1,p2,p3,(g1,r))
					 |NotClass(p,(g1,r)) |NotIntu(p,(g1,r)))->match (pare p2) with
                                                                                        (Ass((g1,r1))|TI((g1,r1))|FE((g1,r1))|ImpI(p,(g1,r))|ImpE(p1,p2,(g1,r))|AndI(p1,p2,(g1,r))
					 |AndEleft(p,(g1,r))|AndEright(p,(g1,r))|OrIleft(p,(g1,r))|OrIright(p,(g1,r))|OrE(p1,p2,p3,(g1,r))
					 |NotClass(p,(g1,r)) |NotIntu(p,(g1,r))
                                        )
                                        )
                 |NotClass(p,(g,r))->(match (pare p) with 
			                  Ass((g1,r1))->NotClass((pare p),(g1 ,r)) 
					 |TI((g1,r1)) ->NotClass((pare p),(g1 ,r)) 
					 |FE((g1,r1)) ->NotClass((pare p),(g1 ,r))
					 |ImpI(p,(g1,r))->NotClass((pare p),(g1 ,r))
					 |ImpE(p1,p2,(g1,r))->NotClass((pare p),(g1 ,r))
					 |AndI(p1,p2,(g1,r))->NotClass((pare p),(g1 ,r))
					 |AndEleft(p,(g1,r))->NotClass((pare p),(g1 ,r))
					 |AndEright(p,(g1,r))->NotClass((pare p),(g1 ,r))
					 |OrIleft(p,(g1,r))->NotClass((pare p),(g1 ,r))
					 |OrIright(p,(g1,r))->NotClass((pare p),(g1 ,r))
					 |OrE(p1,p2,p3,(g1,r))->NotClass((pare p),(g1 ,r))
					 |NotClass(p,(g1,r))->NotClass((pare p),(g1 ,r)) 
					 |NotIntu(p,(g1,r))->NotClass((pare p),(g1 ,r))) 
                 |NotIntu(p,(g,r))->(match (pare p) with 
			                  Ass((g1,r1))->NotIntu((pare p),(g1 ,r)) 
					 |TI((g1,r1)) ->NotIntu((pare p),(g1 ,r)) 
					 |FE((g1,r1)) ->NotIntu((pare p),(g1 ,r))
					 |ImpI(p,(g1,r))->NotIntu((pare p),(g1 ,r))
					 |ImpE(p1,p2,(g1,r))->NotIntu((pare p),(g1 ,r))
					 |AndI(p1,p2,(g1,r))->NotIntu((pare p),(g1 ,r))
					 |AndEleft(p,(g1,r))->NotIntu((pare p),(g1 ,r))
					 |AndEright(p,(g1,r))->NotIntu((pare p),(g1 ,r))
					 |OrIleft(p,(g1,r))->NotIntu((pare p),(g1 ,r))
					 |OrIright(p,(g1,r))->NotIntu((pare p),(g1 ,r))
					 |OrE(p1,p2,p3,(g1,r))->NotIntu((pare p),(g1 ,r))
					 |NotClass(p,(g1,r))->NotIntu((pare p),(g1 ,r)) 
					 |NotIntu(p,(g1,r))->NotIntu((pare p),(g1 ,r))) ;;





  
 (* Write a function graft that given a proof tree pi_0 of D |- p and a list of i proof trees pi_i for G |- q_i for each q_i   in D, returns a proof tree for G |- p, where the trees for  G |- q_i have replaced the leaves of the form D' |- q_i in a proof tree similar in shape to  pi_0.  (F3)*)

let rec graft 



(*
    Write a program normalise which removes all occurrences of r-pairs in a given well-formed proof tree (i.e., where an introduction rule is followed only by an  elimination rule of the main connective).*)
