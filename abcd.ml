type atom = P of string;;
type head= atom;;
type body= atom list;;
type fact= head;;
type rule= head * body;;
type clause = C of fact| L of rule;;
type program = clause list;;

exception NOT_POSSIBLE;;
let rec replace a b c = match b with
                      []-> []
                      |x::xs-> match (a,x) with
                               (P(p), C(P(q)))->if (p=q) then [] else replace a xs
                               |(P(p), L(P(q),r))-> if (p=q) then r else replace a xs ;;

let rec resolve a b = match a with
                       []->[]
                       |x::xs-> match b with
                                 []->[]
                                 |y::ys-> match (x,y) with
                                           (P(p), C(P(q)))-> if (p=q) then resolve xs b else resolve ((replace x ys)@xs) b
                                           |(P(p), L(P(q),r))-> if (p=q) then resolve (r@xs) b else resolve ((replace x ys)@xs) b;;

let resolve_dfs a b = if(resolve a b =[]) then true else false;;

let a = [P("a");P("b");P("c");P("d")];;
let b = [L(P("a"),[P("b");P("c")]);C(P("b"));L(P("c"),[P("d")]);C(P("d"))];;

resolve_dfs a b;;

