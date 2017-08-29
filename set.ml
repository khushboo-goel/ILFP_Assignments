type set = int list;;

let a=[1;2;3];;
let emptyset=[];;

let rec member s r= match s with
                  []->false
                 |x::xs-> if (x=r) then true
                                   else member xs r;;

let empty s= match s with
             []->true
            |x->false;;

let rec card s = match s with
                  []->0
                 | x::xs-> 1 + (card xs);;


let rec append l1 l2= match l1 with
                      []->l2
                     | x::xs-> x::(append xs l2);;


let rec union s1 s2 = match s1 with 
                      []->s2
                     |x::xs -> match s2 with 
                                []->s1
                               | y::ys-> if (member s2 x) then (union xs s2)
                                                        else x ::(union xs s2 );;


let rec intersect s1 s2 = match s1 with 
                          []->[]
                          |x::xs -> match s2 with 
                                     []->[]
                                     | y::ys-> if (member s2 x) then x::intersect xs s2
                                                              else intersect xs s2;;

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


let rec product s1 s2 = match s1 with 
                        []->[]
                        |x::xs-> match s2 with 
                                 []->[]
                                 |y::ys-> (product_r [x] s2) @ (product xs s2);;






(*let rec power s= match s with
                 []-> []
                |x::xs->*) 



