(*In this programming assignment, you will take the data type of propositions defined in class and write simple programs to manipulate them.*)
   

type prop = P of string
            | T 
            | F
            | Not of prop 
            | And of prop * prop
            | Or of prop * prop 
            | Implies of prop * prop

;;

let max l1 l2 = if (l1 >l2) then l1 else l2;;


let rec append l1 l2 = match l1 with
                        []->l2
                        |x::xs -> x::(append xs l2);;

let rho s = match s with
            "playing"->true|"raining"->true|"studying"->true| x->false;;


let rec prop_ret p= match p with 
                     P(n)->(P(n))
		    | T ->T
		    | F ->F
		    | Not(p) -> Not (p)
                    ;;

let rec find_val s r= match s with
                  []->false
                 |x::xs-> if (x=r) then true
                                   else find_val xs r;;

let rec find_prop p = match p with
                      [x]->false
                     |x::xs-> if (find_val xs (Not(x))) then true else find_prop xs;;

(*1. height: prop -> int, which returns the height of a proposition (height of the operator tree, counting from 0).*)
let rec height p = match p with
                  T->0 
                 |F-> 0
                 |P(n)->0
                 |Not(p)-> 1+ height(p)
                 |And(p1, p2)-> 1+ (max (height(p1)) (height(p2)))
                 |Or(p1, p2)-> 1+ (max (height(p1)) (height(p2)))
                 |Implies (p1, p2)-> 1+ (max (height(p1)) (height(p2)))
               ;;






(*2. size: prop ->, which returns the number of nodes in a proposition (number of nodes in the operator tree).*)
let rec size p = match p with
                  T->1 
                 |F->1
                 |P(n)->1
                 |Not(p)-> 1+ size(p)
                 |And(p1, p2)-> 1+ ((size(p1))+ (size(p2)))
                 |Or(p1, p2)-> 1+ ((size(p1))+ (size(p2)))
                 |Implies (p1, p2)-> 1+ ((size(p1)) +(size(p2)))
               ;;






(* 3. letters: prop -> string set, which returns the set of propositional variables that appear in a proposition.*)
let rec letter p = match p with
                  T->[] 
                 |F->[]
                 |P(n)->[n]
                 |Not(p)->letter p
                 |And(p1, p2)-> (append (letter p1) (letter p2))
                 |Or(p1, p2)-> (append (letter p1) (letter p2))
                 |Implies (p1, p2)-> (append (letter p1) (letter p2))
               ;;




(*4. truth: prop -> (string -> bool) -> bool, which evaluates a proposition with respect to a given truth assignment to the propositional letters.*)
let rec truth p rho  = match p with
                  T->true
                 |F->false
                 |P(n)->rho n
                 |Not(p)->not(truth p rho)
                 |And(p1, p2)-> (truth p1 rho) && (truth p1 rho)
                 |Or(p1, p2)-> (truth p1 rho) || (truth p1 rho)
                 |Implies (p1, p2)-> not((truth p1 rho) ) || (truth p1 rho)
               ;;



(*5. nnf: prop -> prop, which converts a proposition into negation normal form, where all Not's appear just above only propositional letters, and strictly below And's and Or's, and all Implies have been replaced by logically equivalent forms.*)
let rec nnf p = match p with
                  T->T
                 |F->F
                 |P(n)-> p
		 |And(p1,p2)->And(nnf p1,nnf p2)
                 |Or(p1,p2)-> Or(nnf p1, nnf p2)
                 |Implies (p1,p2)-> Or( Not(nnf p1), (nnf p2))
                 |Not(p)-> match p with 
                           T->F
                          |F->T
                          |P(n)-> Not (p)
                          |Not(p)-> nnf p 
		          |And(p1, p2)->Or ((nnf (Not p1)),(nnf (Not p2)))
		          |Or(p1, p2)-> And ( (nnf (Not p1)),(nnf (Not p2)))
		          |Implies (p1, p2)-> And((nnf (Not p1)),(nnf (p2)))
                  
               ;;


(*6. cnf: prop -> (prop list list), which converts a proposition into conjunctive normal form (POS) as a (conjunctive) list of clauses, where each clause is considered as a (disjunctive) list of literals (which are either propositional letters or their negation).  Note: Literals are a subset of prop.*) 
let rec convert_c p  =match p with
                    Or (p1, p2) -> (convert_c p1) @ (convert_c p2)
		    | _ -> [prop_ret p]

;;

let rec cnf_set p= match p with 
                    And (p1, p2) -> (cnf_set p1)@(cnf_set p2)
                   | _-> [convert_c p]
;;

let rec distributive_or p1 p2= match p2 with 
                            And(px, py)-> And ( (distributive_or p1 px), (distributive_or p1 py))
                            | px ->( match p1 with
                                    And(pr, ps)-> And ((distributive_or pr p2),( distributive_or ps p2))
                                    | pr -> Or(p1, p2) )
;;

let rec cnf_s p =match p with
               P(n)->p
              | T->T
              | F->F
              | Not(p)-> Not (cnf_s p)
              | And(p1, p2) -> And(cnf_s p1, cnf_s p2)
              | Or (p1, p2) -> distributive_or (cnf_s p1) (cnf_s p2)
              | Implies (p1, p2) -> distributive_or (nnf (Not (cnf_s p1))) (cnf_s p2)
;;
let cnf_prop s = cnf_s (nnf s);; 

let cnf s= cnf_set (cnf_prop s);;





(*7. dnf: prop -> (prop list list),  which converts a proposition into disjunctive normal form (SOP) as a (disjunctive) list of terms, where each term is a list of literals (which are either propositional letters or their negation).  Literals are a subset of prop. *)
let rec convert_d p  =match p with
                    And (p1, p2) -> (convert_d p1) @ (convert_d p2)
		    | _ -> [prop_ret p]

;;
let rec dnf_set p  =match p with
                     Or (p1, p2) -> (dnf_set p1) @ (dnf_set p2)
		    | _ -> [convert_d p]

;;

let rec distributive_and p1 p2= match p2 with 
                            Or(px, py)-> Or ( (distributive_and p1 px), (distributive_and p1 py))
                            | px ->( match p1 with
                                    Or(pr, ps)-> Or ((distributive_and pr p2),( distributive_and ps p2))
                                    | pr -> And(p1, p2) )
;; 

let rec dnf_s p =match p with
                P(n)->p
              | T-> T
              | F-> F
              | Not(p)-> Not (dnf_s p)
              | And(p1, p2) -> distributive_and (dnf_s p1) (dnf_s p2)
              | Or (p1, p2) -> Or ((dnf_s p1),( dnf_s p2))
              | Implies (p1, p2) -> Or ((nnf(Not (dnf_s p1))),(dnf_s p2))
;;



let dnf_prop s = dnf_s (nnf s);;

let dnf s= dnf_set (dnf_prop s);;

    
(*8. isTautology: prop -> bool, which checks if a proposition is a tautology.*)    
(*let rec tautology p =match p with
                          T->true
                         |F->false
                         |P(n)-> if (truth p rho) then true else false
                         |Not (p) -> if (truth p rho) then false else true
                         |And(p1, p2)-> if ((tautology p1) && (tautology p2)) then true else false
                         |Or (p1, p2)-> if ((tautology p1) || (tautology p2)) then true else false
                         |Implies (p1, p2)-> if ((not (tautology p1)) || (tautology p2)) then true else false
                    ;;*)

let rec tautology   p = match p with
                            []->false
                           |x::xs->if (find_prop x) then true else (tautology xs);;

let isTautology p = tautology (dnf_set p);;



(*9. isContradiction: prop -> bool, which checks if a proposition is a contradiction.*)
(*let rec contradiction p = match p with
                          T->false
                         |F->true
                         |P(n)-> if (truth p rho) then false else true
                         |Not (p) -> if (truth p rho) then true else false
                         |And(p1, p2)-> if ((contradiction p1) || (contradiction p2)) then true else false
                         |Or (p1, p2)-> if ((contradiction p1) && (contradiction p2)) then true else false
                         |Implies (p1, p2)-> if ((not (contradiction p1)) && (contradiction p2)) then true else false
                    ;;
*)




let rec contradiction p = match p with
                            []->false
                           |x::xs->if (find_prop x) then true else (contradiction xs);;

let isContradiction p = contradiction (cnf_set p);;



(*10. isSatisfiable: prop -> bool, which checks if a proposition is satisfiable.*)
let isSatisfiable p = if (not(isContradiction p)) then true else false;;



(*11. isEquivalent: prop -> prop -> bool, which checks if two propositions are logically equivalent.*)
let isEquivalent p1 p2 = if (((isTautology p1)=(isTautology p2))|| ((isContradiction p1)=(isContradiction p2))) then true else false;;




(*12. entails: prop -> prop -> bool, which checks if the second proposition is a logical consequence of the first proposition.*) 
let entails p1 p2 = if (isTautology p1)  then (if (isTautology p2) then true else false)
                                       else false;;



(*These are some functions to convert DNF list of list form into propositional form*)
let rec con_d p= match p with
                 [x]-> x
                 |x::xs-> And(x, con_d xs);;

let rec convert_prop_d p = match p with
                           [x]-> con_d x
                           |x::xs -> Or (con_d x, convert_prop_d xs);;


(*These are some functions to convert CNF list of list form into propositional form*)
let rec con_c p= match p with
                 [x]-> x
                 |x::xs-> Or(x, con_c xs);;

let rec convert_prop_c p = match p with
                           [x]-> con_c x
                           |x::xs -> And (con_c x, convert_prop_c xs);;

let a = And(Not (Or (And ( (P("raining")),(P("studying"))), P("learning") )), Or((P("eat")),(P("dance"))));;
