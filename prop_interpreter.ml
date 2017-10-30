type atom = P of string;;
type head= atom;;
type body= atom list;;
type fact= head;;
type rule= head * body;;
type clause = C of fact| L of rule;;
type program = clause list;;

exception NOT_POSSIBLE;;
let rec replace a b = match b with
                      []-> [P("false")]
                      |x::xs-> match (a,x) with
                               (P(p), C(P(q)))->if (p=q) then [] else replace a xs
                               |(P(p), L(P(q),r))-> if (p=q) then r else replace a xs ;;

let rec resolve a b c d = match a with
	                       []->[]
	                       |x::xs-> match b with
	                                 []->[P("false")]
	                                 |y::ys-> match (x,y) with
	                                           (P(p), C(P(q)))-> if (p=q) then resolve xs b c ys else (if ((replace x ys)= [P("false")]) then (match c with 
	                                                                                                                                             []-> [P("false")]
	                                                                                                                                             |q::qs -> (match d with
	                                                                                                                                                        []->[P("false")]
	                                                                                                                                                        |yy::yys-> resolve ((replace q d)@qs) b c yys )) else if ((replace x ys)= []) then resolve ((replace x ys)@xs) b c ys else resolve ((replace x ys)@xs) b a ys)
	                                           |(P(p), L(P(q),r))-> if (p=q) then resolve (r@xs) b a ys else (if ((replace x ys)=[P("false")]) then (match c with 
	                                                                                                                                             []-> [P("false")]
	                                                                                                                                             |q::qs -> (match d with
	                                                                                                                                                        []->[P("false")]
	                                                                                                                                                        |yy::yys-> resolve ((replace q d)@qs) b c yys )) else if ((replace x ys)= []) then resolve ((replace x ys)@xs) b c ys else resolve ((replace x ys)@xs) b a ys);;

let resolve_dfs a b = if(resolve a b [] [] =[]) then true else false;;

let a = [P("a");P("b");P("c");P("d")];;
let b = [C(P("b"));C(P("d"));L(P("a"),[P("e")]);L(P("c"),[P("e")]);L(P("c"),[P("d")])];;

let rec resolve_c a b c d = match a with
	                       []->[]
	                       |x::xs-> match b with
	                                 []->[P("false")]
	                                 |y::ys-> match (x,y) with
	                                           (P(p), C(P(q)))-> if (p=q) then resolve xs b c ys else (if ((replace x ys)= [P("false")]) then (match c with 
	                                                                                                                                             []-> [P("false")]
	                                                                                                                                             |q::qs -> (match d with
	                                                                                                                                                        []->[P("false")]
	                                                                                                                                                        |yy::yys-> resolve (qs@(replace q d)) b c yys )) else if ((replace x ys)= []) then resolve (xs@(replace x ys)) b c ys else resolve (xs@(replace x ys)) b a ys)
	                                           |(P(p), L(P(q),r))-> if (p=q) then resolve (xs@r) b a ys else (if ((replace x ys)=[P("false")]) then (match c with 
	                                                                                                                                             []-> [P("false")]
	                                                                                                                                             |q::qs -> (match d with
	                                                                                                                                                        []->[P("false")]
	                                                                                                                                                        |yy::yys-> resolve (qs@(replace q d)) b c yys )) else if ((replace x ys)= []) then resolve (xs@(replace x ys)) b c ys else resolve (xs@(replace x ys)) b a ys);;
	                                                                                                                                                        

let resolve_bfs a b = if(resolve_c a b [] [] =[]) then true else false;;

