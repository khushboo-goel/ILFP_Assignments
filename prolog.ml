(*ASSIGNMENT -6 First-order Horn Prolog interpreter
                SUNMITTED TO: Prof. Sanjiva Prasad
                SUBMITTED BY: Khushboo Goel (2017MCS2084)


In this assignment, you will write a simplified version of a Prolog interpreter in OCaml by combining the implementations of Assignment 4 (terms, substitutions and unification) and Assignment 5 (Resolution and Backtracking)

You will first (re)define an ML data type to represent the structure of a legitimate Prolog program.

A program is a set (list) of clauses. 
 A clause can either be a fact or a rule. A fact has a head but no body.  A rule has a head and a body.  
The head is a single atomic formula.  A body is a sequence of atomic formulas.
An atomic formula is a k-ary predicate symbol followed by k terms.
A term is either a variable, a constant, or a k-ary function symbol with k subterms.
A goal is a set (list) of atomic formulas.
You need to take your implementation of unification to use as the parameter-passing mechanism. (Note: by pretending the predicate symbol is a function symbol, you can perform resolution of goals and program clauses).

You also need to choose a back-tracking strategy to explore the resolution search space.   You need to be able to replace a goal by subgoals, as found by applying a unifier to the body of a program clause whose head unified with the chosen subgoal.



Now provide examples of Prolog programs and queries, and test the execution of your interpreter*)


type variable = string;;
type constant = string;;
type predicate = string;;
type term = V of variable | C of constant | Node of predicate * (term list)
type atomic_formula = predicate * (term list);;
type clause = Fact of atomic_formula | Rule of  atomic_formula * atomic_formula list;;
type goal = atomic_formula list;;
type program = clause list;;

exception NOT_UNIFIABLE;;
exception NOT_RESOLVED;;

let rec find_val r s= match s with
                     []->false
                     |x::xs-> match r with
                               []->false
                               |y::ys->if (x=y) then true
                                             else find_val r xs;;


let rec length x= match x with
                  []->0
                  |x::xs-> 1 + (length xs);;

let rec maps f l t= match l with
                     []->[]
                     |x::xs-> (f x t)::(maps f xs t);;

let rec find x= match x with
					[]->true
					|x::xs -> if (x) then find xs else false;;

let rec substi x y= match x with
                     C(n)->C(n)
                    |V(n)->(match y with
                                    (p,q)-> if (V(n)=p) then q else x)
                    |Node(m,n)->(match y with
                                         (p,q)-> if (Node(m,n)=p) then q else x);;

let rec substitute x y = match x with 
                         (q,n)-> (q , (maps substi n y));;

let rec subst x y = match y with
                    []-> x
                   | r::xs->subst (substitute x r) xs
               ;;

let rec map_uni f l t = match (l,t) with
                        ([],[])->[]
                      |([],y::ys)->raise NOT_UNIFIABLE
                      |(x::xs,[])->raise NOT_UNIFIABLE
                      |(x::xs , y::ys)-> (f x y)@(map_uni f xs ys);;

let rec find_uni y x= match y with
                      C(a)->false
                     |V(a)-> if(x=y) then true else false
                     |Node(p,[])->false
                     |Node(p,q)-> if (find (maps find_uni q x)) then true else false;;

let rec sub_uni x y= match x with
                     []->[]
                     |p::xs-> (subst p y)::(sub_uni xs y);;

let rec mgu x y = match (x,y) with
                   |(V(a),V(b))-> [(V(a), V(b))]
                   |(V(a),C(b))-> [(V(a), C(b))]
                   |(V(a),Node(b,c))-> [(V(a), Node(b,c))]
                   |(C(a),V(b))-> [(V(b),C(a))]
                   |(C(a),C(b))-> if (a=b) then [C(a),C(b)] else raise NOT_UNIFIABLE
                   |(C(a),Node(b,c))-> raise NOT_UNIFIABLE
                   |(Node(a,d),V(b))-> [(V(b),Node(a,d))]
                   |(Node(a,d),C(b))-> raise NOT_UNIFIABLE
                   |(Node(a,[]),Node(b,[]))-> if (a = b) then [Node(a,[]),Node(b,[])] else raise NOT_UNIFIABLE
                   |(Node(a,d::dx),Node(b,c::cx))-> if (a = b) then (map_uni mgu dx cx) else raise NOT_UNIFIABLE;;

let rec check_mgu a b = match a with
                        []->[]
                        |x::xs-> match b with
                                 []->[]
                                 |y::ys-> (mgu x y)@(check_mgu xs ys);;
let rec find_r x y = match (x,y) with
                     ((p,t),Fact(q,tt))->if (p=q) then (if ((length t) = (length tt)) then (if ((try check_mgu t tt with NOT_UNIFIABLE->[])!=[]) then true else false ) else false )else false
			         |((p,t),Rule((q,tt),b))->if (p=q) then (if ((length t) = (length tt)) then (if ((try check_mgu t tt with NOT_UNIFIABLE->[])!=[]) then true else false ) else false )else false;;

let rec find_resol x y= match y with
                          []-> ([],[],[])
                          |y::ys-> if ((find_r x y)=false) then find_resol x ys else (match (x,y) with 
                                                                                 ((p,t),Fact(q,tt))->([],check_mgu t tt,ys)
			                                                 			        |((p,t),Rule((q,tt),b))->(b,check_mgu t tt,ys));;

let rec resolve goal program mgu = match goal with
			                         []-> mgu
			                         |x::xs-> match program with
			                                 []-> []
			                                 |y::ys->match (find_resol x program) with
			                                  				(k,l,m)-> if (k=[] && l=[]) then [] else (if ((resolve (maps subst (k@xs) l) program (mgu@l))=[])
			                                  					                                      then ( match (find_resol x m) with (e,f,g)->  if ((resolve (maps subst (e@xs) f) program (mgu@f))=[])
			                                  					                                      	                                           then ( match (find_resol x g) with (i,r,t)-> if ((resolve (maps subst (i@xs) r) program (mgu@r))=[])
			                                  					                                      	                                           	                                           then (match (find_resol x t) with (z,zz,zzz)-> 
			                                  					                                      	                                           	                                           	                        (resolve (maps subst (z@xs) zz) program (mgu@zz))) 
			                                  					                                      	                                           	                                           else resolve (maps subst (i@xs) r) program (mgu@r))
			                                  					                                                                                    else resolve (maps subst (e@xs) f) program (mgu@f))    
			                                  					                                      else resolve (maps subst (k@xs) l) program (mgu@l) );;


let rec final_resol t = match t with
                        []->[]
                       |x::xs-> match x with
                                (a,b)-> if (a = b) then final_resol xs else x::final_resol xs;;

let resolution x y= if ((resolve x y [])=[]) then raise NOT_RESOLVED else final_resol( resolve x y []);; 

let rec find_v term term_list = match term_list with
                               []-> false
                              | x::xs -> if (term = x) then true else find_v term xs;;

let rec find_var term goal = match goal with
                            []->false
                            |x::xs-> match x with 
                                     (q,r)-> if (find_v term r) then true else find_var term xs;; 

let rec find_variable goal mgu = match mgu with
                                 []->[]
                                 |x::xs-> match x with
                                          (a,b)-> if (find_var a goal) then x::find_variable goal xs else find_variable goal xs;;

let resolve_x goal program = find_variable goal (resolution goal program);;

let resolve_all goal program =  if ((resolve goal program [])=[]) then (false, []) else (true,(resolve_x goal program));; 

let rec find_occurences subgoal program = match subgoal with
                                          (p,r) -> match program with
                                                       []->[]
                                                        |x::xs-> match x with 
                                                            (Fact(q,t))->if (p=q) then (if ((length t) = (length (r))) then (if ((try check_mgu t r with NOT_UNIFIABLE->[])!=[]) then x::find_occurences subgoal xs else find_occurences subgoal xs ) else find_occurences subgoal xs )else find_occurences subgoal xs
			                                                |(Rule((q,t),b))->if (p=q) then (if ((length t) = (length (r))) then (if ((try check_mgu t r with NOT_UNIFIABLE->[])!=[]) then x::find_occurences subgoal xs else find_occurences subgoal xs ) else find_occurences subgoal xs )else find_occurences subgoal xs;;


let rec find_rec goal program mgu occur= match goal with
                                         []->[mgu]
                                        |x::xs -> match (find_occurences x occur) with
                                                    []->[]
                                                    |y::ys -> match (find_resol x [y]) with (k,l,m)-> if (k=[] && l=[]) then [] else (find_rec (maps subst (k@xs) l) program (mgu@l) program)@(find_rec goal program mgu ys);;


let rec final_resol_new t = match t with
                             []->[]
                             |x::xs-> (final_resol x)::final_resol_new xs;;

let rec find_variable_new goal mgu_list = match mgu_list with
                                          []->[]
                                          |x::xs-> (find_variable goal x)::(find_variable_new goal xs);; 

let resolution_new x y= if ((find_rec x y [] y)=[]) then raise NOT_RESOLVED else final_resol_new(find_rec x y [] y);;

let resolve_x_new goal program = find_variable_new goal (resolution_new goal program);;

let interpret goal program =  if ((find_rec goal program [] program)=[]) then (false, []) else (true,(resolve_x_new goal program));;


let g =[("loves",[C("Ram");C("Shyam")]);("hates",[V("x");C("Ram")])];;
let p= [Fact("loves",[C("Ram");C("Shyam")]);Fact("hates",[C("Ravan");C("Ram")]);Fact("hates",[C("Radha");C("Ram")])];;
let q= [Fact("loves",[C("Ram");C("Shyam")]);Rule(("hates",[V("x");V("y")]),[("loves",[V("y");V("x")])]);Fact("hates",[C("Radha");C("Ram")])];;
let r= [Fact("loves",[C("Ram");C("Shyam")]);Rule(("hates",[V("x");V("y")]),[("loves",[V("x");V("y")])]);Fact("hates",[C("Radha");C("Ram")])];;

(*let rec print b = match b with
                  []->print_string " "
                 | x::xs -> match x with
                            |(V(a),V(b))-> print_string (a ^","^ b), print xs 
                            |(V(a),C(b))-> print_string (a^","^ b), print xs
                            |(V(a),Node(b,c))-> print_string (a ^","^ b), print xs
                            |(C(a),V(b))-> print_string (a ^ "," ^ b), print xs
                            |(C(a),C(b))-> print_string (a ^ "," ^ b), print xs
                            |(C(a),Node(b,c))-> print_string (a ^ "," ^ b), print xs
                            |(Node(a,d),V(b))-> print_string (a ^ "," ^ b), print xs
                            |(Node(a,d),C(b))-> print_string (a^","^ b), print xs
                            |(Node(a,[]),Node(b,[]))-> print_string (a ^"," ^b), print xs
                            |(Node(a,d::dx),Node(b,c::cx))-> print_string (a ^"," ^ b), print xs;;

let print_all goal program = match (resolve_all goal program) with
                             (a,b)-> match a with
                                     false-> print_string "false"
                                     |true -> match b with
                                              []-> print_string "true"
                                             | x::xs -> print b;;
*)
interpret g p;;
interpret g q;;
interpret g r;;