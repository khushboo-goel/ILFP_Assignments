type prop = P of string
            | T 
            | F
            | Not of prop 
            | And of prop * prop
            | Or of prop * prop 
            | Implies of prop * prop

;;

let max l1 l2 = if (l1 >l2) then l1 else l2;;

let rec height p = match p with
                  T->0 
                 |F-> 0
                 |P(n)->0
                 |Not(p)-> 1+ height(p)
                 |And(p1, p2)-> 1+ (max (height(p1)) (height(p2)))
                 |Or(p1, p2)-> 1+ (max (height(p1)) (height(p2)))
                 |Implies (p1, p2)-> 1+ (max (height(p1)) (height(p2)))
               ;;

let rec size p = match p with
                  T->1 
                 |F->1
                 |P(n)->1
                 |Not(p)-> 1+ size(p)
                 |And(p1, p2)-> 1+ ((size(p1))+ (size(p2)))
                 |Or(p1, p2)-> 1+ ((size(p1))+ (size(p2)))
                 |Implies (p1, p2)-> 1+ ((size(p1)) +(size(p2)))
               ;;

let rec append l1 l2 = match l1 with
                        []->l2
                        |x::xs -> x::(append xs l2);;

let rec letter p = match p with
                  T->[] 
                 |F->[]
                 |P(n)->[n]
                 |Not(p)->letter p
                 |And(p1, p2)-> (append (letter p1) (letter p2))
                 |Or(p1, p2)-> (append (letter p1) (letter p2))
                 |Implies (p1, p2)-> (append (letter p1) (letter p2))
               ;;

let rho s = match s with
            |"playing"->true|"raining"->true|"studying"->true| x->false;;


let rec truth p rho  = match p with
                  T->true
                 |F->false
                 |P(n)->rho n
                 |Not(p)->not(truth p rho)
                 |And(p1, p2)-> (truth p1 rho) && (truth p1 rho)
                 |Or(p1, p2)-> (truth p1 rho) || (truth p1 rho)
                 |Implies (p1, p2)-> not((truth p1 rho) ) || (truth p1 rho)
               ;;


let rec nnf p = match p with
                  T->T
                 |F->F
                 |P(n)->nnf p
                 |Not(p)-> (match p with 
                           T->F
                          |F->T
                          |P(n)-> Not (p)
                          |Not(p)-> nnf p 
		          |And(p1, p2)->Or ((nnf (Not p1)),(nnf (Not p2)))
		          |Or(p1, p2)-> And ( (nnf (Not p1)),(nnf (Not p2)))
		          |Implies (p1, p2)-> And((nnf (Not p1)),(nnf (p2)))
                          )
		 |And(p1, p2)->And( (nnf p1),(nnf p2))
                 |Or(p1, p2)-> Or( (nnf p1), (nnf p2))
                 |Implies (p1, p2)-> And( (Not(nnf p1)), (nnf p2))
               ;;


let rec distributive_or p1 p2= match p2 with 
                            And(px, py)-> And ( (distributive_or p1 px), (distributive_or p1 py))
                            | px ->( match p1 with
                                    And(pr, ps)-> And ((distributive_or pr p2),( distributive_or ps p2))
                                    | pr -> Or(p1, p2) )
;;

let rec distributive_and p1 p2= match p2 with 
                            Or(px, py)-> Or ( (distributive_and p1 px), (distributive_and p1 py))
                            | px ->( match p1 with
                                    Or(pr, ps)-> Or ((distributive_and pr p2),( distributive_and ps p2))
                                    | pr -> And(p1, p2) )
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

let cnf s = cnf_s (nnf s);; 

let rec dnf_s p =match p with
                P(n)->p
              | T-> T
              | F-> F
              | Not(p)-> Not (dnf_s p)
              | And(p1, p2) -> distributive_and (dnf_s p1) (dnf_s p2)
              | Or (p1, p2) -> Or ((dnf_s p1),( dnf_s p2))
              | Implies (p1, p2) -> Or ((nnf(Not (dnf_s p1))),(dnf_s p2))
;;

let dnf s = dnf_s (nnf s);;

let a = Not (Or (And ( (P("raining")),(P("studying"))), P("learning") ));;

let rec tautology p =match p with
                          T->true
                         |F->false
                         |P(n)-> if (truth p rho) then true else false
                         |Not (p) -> if (truth p rho) then false else true
                         |And(p1, p2)-> if ((tautology p1) && (tautology p2)) then true else false
                         |Or (p1, p2)-> if ((tautology p1) || (tautology p2)) then true else false
                         |Implies (p1, p2)-> if ((not (tautology p1)) || (tautology p2)) then true else false
                    ;;

let isTautology p = tautology (dnf p);;

let isContradiction p = if (not(isTautology p)) then true else false;;


let isSatisfiable
let isEquivalent
let entails
