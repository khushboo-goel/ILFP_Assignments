type prop = P of string | T | F

    | Not of prop | And of prop * prop

    | Or of prop * prop | Implies of prop * prop

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


let rec nnf p    = match p with
                  T->T
                 |F->F
                 |P(n)->nnf p
                 |Not(p)-> (match p with 
                           T->F
                          |F->T
                          |P(n)->nnf p
                          |Not(p)-> nnf p 
		          |And(p1, p2)->Or ((nnf (Not p1)),(nnf (Not p2)))
		          |Or(p1, p2)-> And ( (nnf (Not p1)),(nnf (Not p2)))
		          |Implies (p1, p2)-> And((nnf (Not p1)),(nnf (p2)))
                          )
		 |And(p1, p2)->And( (nnf p1),(nnf p2))
                 |Or(p1, p2)-> Or( (nnf p1), (nnf p2))
                 |Implies (p1, p2)-> And( (Not(nnf p1)), (nnf p2))
               ;;

let rec cnf p = match p with
                  T->T
                 |F->F
                 |P(n)->p
                 |Not(p)-> nnf p
		 |And(p1, p2)-> And((cnf p1),(cnf p2))
                 |Or(p1, p2)-> nnf (Not(And ((Not p1), (Not p2))))
                 |Implies (p1, p2)-> nnf (Not(And ((Not (Not p1)), (Not p2))))
               ;;



let rec distr_or p1 p2 = match (p1, p2) with
| (p, And (p21, p22)) -> And (distr_or p p21 , distr_or p p22)
| (And (p11, p12), p) -> And (distr_or p11 p, distr_or p12 p)
| (p1, p2) -> Or (p1, p2);;

let rec cnf_prop p = match p with
|P s -> p
| T -> p
| F -> p
| Not p1 -> p
| And (p1, p2) -> And (cnf_prop p1, cnf_prop p2)
| Or (p1, p2) -> distr_or (cnf_prop p1) (cnf_prop p2);;


let rec flatten_or_cnf p = match p with 
 Or (p1, p2) -> (flatten_or_cnf p1) @ (flatten_or_cnf p2)
| l -> [l];;

let rec flatten_and_cnf = function
| And (p1, p2) -> (flatten_and_cnf p1) @ (flatten_and_cnf p2)
| l -> [flatten_or_cnf l];;

(*cnf function: prop -> prop set set returns cnf of a given propositions as a list of list containing unique elements*)
let cnf p = (flatten_and_cnf (cnf_prop (nnf p)));;

