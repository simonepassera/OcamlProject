(* DYNAMIC EVAL *)

type exp =
| CstInt of int
| CstString of string
| CstTrue
| CstFalse
| Den of ide
| Sum of exp * exp
| Sub of exp * exp
| Times of exp * exp
| Ifthenelse of exp * exp * exp
| Eq of exp * exp
| Let of ide * exp * exp
| Fun of ide * exp
| Letrec of ide * ide * exp * exp
| Apply of exp * exp
| List of exp list
| SetEmpty of type_elts
| SetSingleton of type_elts * exp
| SetOf of type_elts * exp
| Union of exp * exp
| Inter of exp * exp
| Diff of exp * exp
| Add of exp * exp
| Remove of exp * exp
| IsEmpty of exp
| Contains of exp * exp
| Subset of exp * exp
| MinElt of exp
| MaxElt of exp
| For_all of exp * exp
| Exists of exp * exp
| Filter of exp * exp
| Map of exp * exp
and ide = string
and type_elts = string ;;

type 'v env = (string * 'v) list ;;

type evT =
| Int of int
| String of string
| Bool of bool
| Closure of ide * exp * evT env
| RecClosure of ide * ide * exp * evT env
| List_val of evT list
| Set of type_elts * evT
| Unbound ;;

let emptyEnv = [("", Unbound)] ;;

let rec lookup (s:evT env) (i:string) =
  match s with
  | [("", Unbound)] -> Unbound
  | (x, v) :: s2 -> if x = i
                     then v
                        else lookup s2 i
  | [] -> failwith "Wrong env" ;; 

let bind (e:evT env) (s:string) (v:evT) = (s, v) :: e ;;

type tval =
| Tint
| Tstring
| Tbool
| Tfun of tval * tval
| Trecfun of tval * tval
| Tfunval of ide * exp
| Trecfunval of ide * ide * exp
| Tlist of tval
| Temptylist
| Tset of tval ;;

type tenv = ide -> tval ;;

let emptyTenv = fun (x:ide) -> failwith "Empty type env" ;;

let lookupTenv (e:tenv) (i:ide) = e i ;;

let bindTenv (e:tenv) (i:ide) (v:tval) = fun x -> if x = i then v else lookupTenv e x ;;

let type_string v =
  match v with
  | Int i -> "int"
  | String s -> "string"
  | Bool b -> "bool"
  | Closure (arg, fbody, fDecEnv) -> "fun"
  | RecClosure (f, arg, fbody, fDecEnv) -> "recfun"
  | List_val l -> "list"
  | Set (t, List_val l) -> "set"
  | _ -> failwith "Run-time error" ;;

let parentheses str =
  let rec loop np nc l =
    if nc = l
     then -1
        else match str.[nc] with
             | '(' -> loop (np + 1) (nc + 1) l
             | ')' -> if (np - 1) = 0
                       then nc
                          else loop (np - 1) (nc + 1) l
             | _ -> loop np (nc + 1) l
    in loop 0 0 (String.length str) ;;

let type_param s =
  let nc1 = parentheses s in
    if nc1 = -1
     then failwith "Run-time error"
        else let arg = Str.string_after (Str.string_before s nc1) 1 in
               let str = Str.string_after s (nc1 + 5) in
                 let nc2 = parentheses str in
                   if nc2 = -1
                    then failwith "Run-time error"
                       else (arg, Str.string_after (Str.string_before str nc2) 1) ;;

let rec type_return t =
  match t with
  | "int" -> Tint
  | "string" -> Tstring
  | "bool" -> Tbool
  | "emptylist" -> Temptylist
  | _ -> let r1 = Str.regexp "\\([a-z]+\\) (\\([a-z>() -]+\\))" in
           if (Str.string_match r1 t 0)
            then (match (Str.matched_group 1 t) with
                  | "list" -> Tlist (type_return (Str.matched_group 2 t))
                  | "set" -> Tset (type_return (Str.matched_group 2 t))
                  | "fun" -> (match (type_param (Str.matched_group 2 t)) with
                              | (arg, res) -> Tfun (type_return arg, type_return res))
                  | "recfun" -> (match (type_param (Str.matched_group 2 t)) with
                                 | (arg, res) -> Trecfun (type_return arg, type_return res))
                  | _ -> failwith "Run-time error")
               else failwith "Run-time error"

let rec teval (e:exp) (s:tenv) =
  match e with
  | CstInt n -> Tint
  | CstString s -> Tstring
  | CstTrue -> Tbool
  | CstFalse -> Tbool
  | Eq (e1, e2) -> Tbool
  | Times (e1, e2) -> Tint                         
  | Sum (e1, e2) -> Tint
  | Sub (e1, e2) -> Tint
  | Ifthenelse (e1, e2, e3) -> teval e2 s
  | Den i -> lookupTenv s i
  | Let (i, e, ebody) -> teval ebody (bindTenv s i (teval e s))
  | Fun (arg, ebody) -> Tfunval (arg, ebody)
  | Letrec (f, arg, fBody, letBody) -> teval letBody (bindTenv s f (Trecfunval (f, arg, fBody)))
  | Apply (eF, eArg) -> (match (teval eF s) with
                         | Tfunval (arg, ebody) -> let targ = teval eArg s in
                                                     let env = bindTenv s arg targ in
                                                       teval ebody env
                         | Trecfunval (f, arg, fbody) -> let renv = bindTenv s f (Trecfunval (f, arg, fbody)) in
                                                           let targ = teval eArg s in
                                                             let env = bindTenv renv arg targ in
                                                               teval fbody env
                         | Tfun (targ, tres) -> tres
                         | Trecfun (targ, tres) -> tres                                                          
                         | _ -> failwith "Run-time error")
  | List l -> if l = []
               then Temptylist
                  else Tlist (teval (List.nth l 0) s)
  | SetEmpty t -> Tset (type_return t)
  | SetSingleton (t, elt) -> Tset (type_return t)
  | SetOf (t, l) -> Tset (type_return t)
  | Union (s1, s2) -> teval s1 s
  | Inter (s1, s2) -> teval s1 s
  | Diff (s1, s2) -> teval s1 s
  | Add (s0, elt) -> teval s0 s
  | Remove (s0, elt) -> teval s0 s
  | IsEmpty s0 -> Tbool
  | Contains (s0, elt) -> Tbool
  | Subset (s1, s2) -> Tbool
  | MinElt s0 -> (match (teval s0 s) with
                  | Tset t -> t
                  | _ -> failwith "Run-time error")
  | MaxElt s0 -> (match (teval s0 s) with
                  | Tset t -> t
                  | _ -> failwith "Run-time error")
  | For_all (p, s0) -> Tbool
  | Exists (p, s0) -> Tbool
  | Filter (p, s0) -> teval s0 s
  | Map (f, s0) -> (match (teval f s, teval s0 s) with
                    | (Tfunval (arg, ebody), Tset t0) -> let env = bindTenv s arg t0 in
                                                           Tlist (teval ebody env)
                    | (_, _) -> failwith "Run-time error") ;;

let rec typecheck (x, y) =
  match x with
  | "int" -> (match y with
              | Int u -> true
              | _ -> false)
  | "string" -> (match y with
                 | String u -> true
                 | _ -> false)
  | "bool" -> (match y with
               | Bool u -> true
               | _ -> false)
  | "list" -> (match y with
               | List_val l -> true
               | _ -> false)
  | "set" -> (match y with
              | Set (t, List_val l) -> true
              | _ -> false)
  | "fun" -> (match y with
              | Closure (arg, fbody, fDecEnv) -> true
              | _ -> false)
  | "recfun" -> (match y with 
                 | RecClosure (f, arg, fbody, fDecEnv) -> true
                 | _ -> false)
  | _ -> let r = Str.regexp "\\([a-z]+\\) (\\([a-z>() -]+\\))" in
           if (Str.string_match r x 0)
            then (match (Str.matched_group 1 x) with
                  | "fun" -> (match y with
                              | Closure (carg, fbody, fDecEnv) -> (match (type_param (Str.matched_group 2 x)) with
                                                                   | (arg, res) -> let env = bindTenv emptyTenv carg (type_return arg) in
                                                                                     let tval_res = type_return res in
                                                                                       (match tval_res with
                                                                                        | Tfun (targ, tres) -> (match (teval fbody env) with
                                                                                                                | Tfun (targ2, tres2)-> if (targ, tres) = (targ2, tres2)
                                                                                                                                         then true
                                                                                                                                            else false
                                                                                                                | Tfunval (i, e) -> true
                                                                                                                | _ -> false)
                                                                                        | Trecfun (targ, tres) -> (match (teval fbody env) with
                                                                                                                   | Trecfun (targ2, tres2)-> if (targ, tres) = (targ2, tres2)
                                                                                                                                               then true
                                                                                                                                                  else false
                                                                                                                   | Trecfunval (i1, i2, e) -> true
                                                                                                                   | _ -> false)
                                                                                        | Temptylist -> (match (teval fbody env) with
                                                                                                         | Temptylist -> true
                                                                                                         | Tlist tl -> true
                                                                                                         | _ -> false)
                                                                                        | Tlist tl -> (match (teval fbody env) with
                                                                                                       | Temptylist -> true
                                                                                                       | Tlist tl -> true
                                                                                                       | _ -> false)                                                                                            
                                                                                        | _ -> if tval_res = (teval fbody env)
                                                                                                then true
                                                                                                   else false))
                              | _ -> false)
                  | "recfun" -> (match y with
                                 | RecClosure (f, carg, fbody, fDecEnv) -> (match (type_param (Str.matched_group 2 x)) with
                                                                           | (arg, res) -> let renv = bindTenv emptyTenv f (Trecfunval (f, carg, fbody)) in
                                                                                             let env = bindTenv renv arg (type_return arg) in
                                                                                               let tval_res = type_return res in
                                                                                                 (match tval_res with
                                                                                                  | Tfun (targ, tres) -> (match (teval fbody env) with
                                                                                                                          | Tfun (targ2, tres2)-> if (targ, tres) = (targ2, tres2)
                                                                                                                                                   then true
                                                                                                                                                      else false
                                                                                                                          | Tfunval (i, e) -> true
                                                                                                                          | _ -> false)
                                                                                                  | Trecfun (targ, tres) -> (match (teval fbody env) with
                                                                                                                             | Trecfun (targ2, tres2)-> if (targ, tres) = (targ2, tres2)
                                                                                                                                                         then true
                                                                                                                                                            else false
                                                                                                                             | Trecfunval (i1, i2, e) -> true
                                                                                                                             | _ -> false)
                                                                                                  | Temptylist -> (match (teval fbody env) with
                                                                                                                   | Temptylist -> true
                                                                                                                   | Tlist tl -> true
                                                                                                                   | _ -> false)    
                                                                                                  | Tlist tl -> (match (teval fbody env) with
                                                                                                                 | Temptylist -> true
                                                                                                                 | Tlist tl -> true
                                                                                                                 | _ -> false)                                                                                                     
                                                                                                  | _ -> if tval_res = (teval fbody env)
                                                                                                          then true
                                                                                                             else false))
                                 | _ -> false)
                  | _ -> failwith "Run-time error")
               else failwith "Run-time error" ;;
                       
let rec type_elts_check str =
  let rec type_res t =
    match t with
    | "int" -> true
    | "string" -> true
    | "bool" -> true
    | "emptylist" -> true
    | _ -> let r1 = Str.regexp "\\([a-z]+\\) (\\([a-z>() -]+\\))" in
             if (Str.string_match r1 t 0)
              then (match (Str.matched_group 1 t) with
                   | "list" -> type_res (Str.matched_group 2 t)
                   | "set" -> type_elts_check (Str.matched_group 2 t)
                   | "fun" -> (match (type_param (Str.matched_group 2 t)) with
                               | (arg, res) -> (type_res arg) &&  (type_res res))
                   | "recfun" -> (match (type_param (Str.matched_group 2 t)) with
                                  | (arg, res) -> (type_res arg) && (type_res res))
                   | _ -> failwith "Not a valid type for elements of set")
                 else failwith "Not a valid type for elements of set"
    in let r0 = Str.regexp "\\([a-z]+\\) (\\([a-z>() -]+\\))" in
         if (Str.string_match r0 str 0)
          then match (Str.matched_group 1 str) with
               | "list" -> failwith "Not a valid type for elements of set"
               | "emptylist" -> failwith "Not a valid type for elements of set"
               | "set" -> failwith "Not a valid type for elements of set"
               | _ -> type_res str
             else type_res str ;;
                                                                                                                             
let int_sum (x, y) =
  match(typecheck ("int", x), typecheck ("int", y), x, y) with
  | (true, true, Int v, Int w) -> Int (v + w)
  | (_, _, _, _) -> failwith "Run-time error" ;;

let int_sub (x, y) =
  match(typecheck ("int", x), typecheck ("int", y), x, y) with
  | (true, true, Int v, Int w) -> Int (v - w)
  | (_, _, _, _) -> failwith "Run-time error" ;;

let int_times (x, y) =
  match(typecheck ("int", x), typecheck ("int", y), x, y) with
  | (true, true, Int v, Int w) -> Int (v * w)
  | (_, _, _, _) -> failwith "Run-time error" ;;

let contains (s, elt) =
  match (typecheck ("set", s), s) with
  | (true, Set (t, List_val l)) -> (match (typecheck (t, elt)) with
                                    | true -> let rec f (ls, e) =
                                                match ls with
                                                | [] -> false
                                                | x :: xs -> if x = elt
                                                              then true
                                                                 else f (xs, e)
                                                in Bool (f (l, elt))
                                    | _ -> failwith "Run-time error")
  | (_, _) -> failwith "Run-time error" ;;

let add (s, elt) =
  match (typecheck ("set", s), s) with
  | (true, Set (t, List_val l)) -> (match (typecheck (t, elt)) with
                                    | true -> if contains (s, elt) = Bool true
                                               then Set (t, List_val l)
                                                  else Set (t, List_val (elt :: l))
                                    | _ -> failwith "Run-time error")
  | (_, _) -> failwith "Run-time error" ;;

let set_empty t =
  match (type_elts_check t) with
  | true -> Set (t, List_val [])
  | _ -> failwith "Run-time error" ;;

let set_singleton (t, elt) = add (set_empty t, elt) ;;

let set_of (t, l) =
  match (type_elts_check t, l) with
  | (true, List_val lv) -> if lv = []
                            then failwith "Run-time error"
                               else let rec create_set ls =
                                      match ls with
                                      | [] -> set_empty t
                                      | x :: xs -> add (create_set xs, x)
                                      in create_set lv    
  | (_, _) -> failwith "Run-time error" ;;

let remove (s, elt) =
  match (typecheck ("set", s), s) with
  | (true, Set (t, List_val l)) -> (match (typecheck (t, elt)) with
                                    | true -> let rec f ls =
                                                match ls with
                                                | [] -> []
                                                | x :: xs -> if x = elt
                                                              then xs
                                                                 else x :: f xs
                                                in Set (t, List_val (f l)) 
                                    | _ -> failwith "Run-time error")
  | (_, _) -> failwith "Run-time error" ;;

let is_empty s =
  match (typecheck ("set", s), s) with
  | (true, Set (t, List_val l)) -> Bool (l = [])
  | (_, _) -> failwith "Run-time error" ;;

let min_elt s =
  match (typecheck ("set", s), s) with
  | (true, Set (t, List_val l)) -> (match t with
                                    | "int" -> let rec int_min ls =
                                                 match ls with
                                                 | Int x :: [] -> Int x
                                                 | Int x :: xs -> (match (int_min xs) with 
                                                                   | Int r -> if x < r 
                                                                               then Int x
                                                                                  else Int r
                                                                   | _ -> failwith "Run-time error")
                                                 | _ -> failwith "Run-time error" 
                                                 in int_min l     
                                    | "string" -> let rec string_min ls =
                                                    match ls with
                                                    | String x :: [] -> String x
                                                    | String x :: xs -> (match (string_min xs) with 
                                                                         | String r -> if x < r 
                                                                                        then String x
                                                                                           else String  r
                                                                         | _ -> failwith "Run-time error")
                                                    | _ -> failwith "Run-time error"
                                                    in string_min l
                                    | _ -> failwith "Run-time error")
  | (_, _) -> failwith "Run-time error" ;;

let max_elt s =
  match (typecheck ("set", s), s) with
  | (true, Set (t, List_val l)) -> (match t with
                                    | "int" -> let rec int_max ls =
                                                 match ls with
                                                 | Int x :: [] -> Int x
                                                 | Int x :: xs -> (match (int_max xs) with 
                                                                   | Int r -> if x > r 
                                                                               then Int x
                                                                                  else Int r
                                                                   | _ -> failwith "Run-time error")
                                                 | _ -> failwith "Run-time error" 
                                                 in int_max l     
                                    | "string" -> let rec string_max ls =
                                                    match ls with
                                                    | String x :: [] -> String x
                                                    | String x :: xs -> (match (string_max xs) with 
                                                                         | String r -> if x > r 
                                                                                        then String x
                                                                                           else String  r
                                                                         | _ -> failwith "Run-time error")
                                                    | _ -> failwith "Run-time error"
                                            in string_max l
                                    | _ -> failwith "Run-time error")
  | (_, _) -> failwith "Run-time error" ;;

let union (s1, s2) =
  match (typecheck ("set", s1), typecheck ("set", s2), s1, s2) with
  | (true, true, Set (t1, List_val l1), Set (t2, List_val l2)) -> if t1 <> t2
                                                                   then failwith "Run-time error"
                                                                      else let rec create_set ls =
                                                                             match ls with
                                                                             | [] -> s1
                                                                             | x :: xs -> add (create_set xs, x)
                                                                             in create_set l2
  | (_, _, _, _) -> failwith "Run-time error" ;;

let inter (s1, s2) =
  match (typecheck ("set", s1), typecheck ("set", s2), s1, s2) with
  | (true, true, Set (t1, List_val l1), Set (t2, List_val l2)) -> if t1 <> t2
                                                                   then failwith "Run-time error"
                                                                      else let rec create_set ls =
                                                                             match ls with
                                                                             | [] -> set_empty t1
                                                                             | x :: xs -> if contains (s2, x) = Bool true
                                                                                           then add (create_set xs, x)
                                                                                              else create_set xs
                                                                             in create_set l1
  | (_, _, _, _) -> failwith "Run-time error" ;;

let diff (s1, s2) =
  match (typecheck ("set", s1), typecheck ("set", s2), s1, s2) with
  | (true, true, Set (t1, List_val l1), Set (t2, List_val l2)) -> if t1 <> t2
                                                                   then failwith "Run-time error"
                                                                      else let rec create_set ls =
                                                                             match ls with
                                                                             | [] -> set_empty t1
                                                                             | x :: xs -> if contains (s2, x) = Bool false
                                                                                           then add (create_set xs, x)
                                                                                              else create_set xs
                                                                             in create_set l1
  | (_, _, _, _) -> failwith "Run-time error" ;;

let eq (x, y) =
  match (typecheck ("int", x), typecheck ("int", y), x, y) with
  | (true, true, Int v, Int w) -> Bool (v = w)
  | (_, _, _, _) -> (match (typecheck ("string", x), typecheck ("sring", y), x, y) with
                     | (true, true, String v, String w) -> Bool (v = w)
                     | (_, _, _, _) -> (match (typecheck ("bool", x), typecheck ("bool", y), x, y) with
                                        | (true, true, Bool v, Bool w) -> Bool (v = w)
                                        | (_, _, _, _) -> (match (typecheck ("list", x), typecheck ("list", y), x, y) with
                                                           | (true, true, List_val v, List_val w) -> Bool (v = w)
                                                           | (_, _, _, _) -> (match (typecheck ("fun", x), typecheck ("fun", y), x, y) with
                                                                              | (true, true, Closure (arg1, fbody1, fDecEnv1), Closure (arg2, fbody2, fDecEnv2)) -> Bool (x = y)
                                                                              | (_, _, _, _) -> (match (typecheck ("recfun", x), typecheck ("recfun", y), x, y) with
                                                                                                 | (true, true, RecClosure (f1, arg1, fbody1, fDecEnv1), RecClosure (f2, arg2, fbody2, fDecEnv2)) -> Bool (x = y)
                                                                                                 | (_, _, _, _) -> (match (typecheck ("set", x), typecheck ("set", y), x, y) with
                                                                                                                    | (true, true, Set (t1, List_val l1), Set (t2, List_val l2)) -> if (is_empty (diff (x, y))) = Bool true
                                                                                                                                                                                     then is_empty (diff (y, x))
                                                                                                                                                                                        else Bool false
                                                                                                                    | (_, _, _, _) -> failwith "Run-time error")))))) ;;

let subset (s1, s2) =
  match (typecheck ("set", s1), typecheck ("set", s2), s1, s2) with
  | (true, true, Set (t1, List_val l1), Set (t2, List_val l2)) -> if t1 <> t2
                                                                   then failwith "Run-time error"
                                                                      else let rec check ls =
                                                                             match ls with
                                                                             | [] -> Bool true
                                                                             | x :: xs -> if contains (s2, x) = Bool true
                                                                                           then check xs
                                                                                              else Bool false
                                                                             in check l1
  | (_, _, _, _) -> failwith "Run-time error" ;;

let rec eval (e:exp) (s:evT env) =
  match e with
  | CstInt n -> Int n
  | CstString s -> String s
  | CstTrue -> Bool true
  | CstFalse -> Bool false
  | Eq (e1, e2) -> eq ((eval e1 s), (eval e2 s))
  | Times (e1, e2) -> int_times ((eval e1 s), (eval e2 s))
  | Sum (e1, e2) -> int_sum ((eval e1 s), (eval e2 s))
  | Sub (e1, e2) -> int_sub ((eval e1 s), (eval e2 s))
  | Ifthenelse (e1, e2, e3) -> let g = eval e1 s in
                                 (match (typecheck ("bool", g), g) with
                                  | (true, Bool b) -> let rt = eval e2 s
                                                        in let rf = eval e3 s
                                                             in (match (typecheck ("int", rt), typecheck ("int", rf)) with
                                                                 | (true, true) -> if b then rt else rf
                                                                 | (_, _) -> (match (typecheck ("string", rt), typecheck ("string", rf)) with
                                                                              | (true, true) -> if b then rt else rf
                                                                              | (_, _) -> (match (typecheck ("bool", rt), typecheck ("bool", rf)) with
                                                                                           | (true, true) -> if b then rt else rf
                                                                                           | (_, _) -> (match (typecheck ("list", rt), typecheck ("list", rf)) with
                                                                                                        | (true, true) -> if b then rt else rf
                                                                                                        | (_, _)-> (match (typecheck ("fun", rt), typecheck ("fun", rf)) with
                                                                                                                    | (true, true) -> if b then rt else rf
                                                                                                                    | (_, _)-> (match (typecheck ("recfun", rt), typecheck ("recfun", rf)) with
                                                                                                                                | (true, true) -> if b then rt else rf
                                                                                                                                | (_, _) -> (match (typecheck ("set", rt), typecheck ("set", rf)) with
                                                                                                                                             | (true, true) -> if b then rt else rf
                                                                                                                                             | (_, _) -> failwith "Run-time error")))))))
                                  | (_, _) -> failwith "Run-time error")
  | Den i -> lookup s i
  | Let (i, e, ebody) -> eval ebody (bind s i (eval e s))
  | Fun (arg, ebody) -> Closure (arg, ebody, s)
  | Letrec (f, arg, fBody, letBody) -> let benv = bind s f (RecClosure (f, arg, fBody, s)) in
                                         eval letBody benv
  | Apply (eF, eArg) -> let fclosure = eval eF s in
                          (match fclosure with
                           | Closure (arg, fbody, fDecEnv) -> let aVal = eval eArg s in
                                                                let aenv = bind fDecEnv arg aVal in
                                                                  eval fbody aenv
                           | RecClosure (f, arg, fbody, fDecEnv) -> let aVal = eval eArg s in
                                                                      let rEnv = bind fDecEnv f fclosure in
                                                                        let aenv = bind rEnv arg aVal in
                                                                          eval fbody aenv
                           | _ -> failwith "Run-time error")
  | List l -> if l = []
               then List_val []
                  else let t = type_string (eval (List.nth l 0) s) in
                         let rec f ls = 
                           match ls with
                           | [] -> []
                           | x :: xs -> let ex = eval x s in
                                          if typecheck (t, ex)
                                           then ex :: f xs
                                              else failwith "Run-time error"
                           in List_val (f l)
  | SetEmpty t -> set_empty t
  | SetSingleton (t, elt) -> set_singleton (t, (eval elt s))
  | SetOf (t, l) -> set_of (t, (eval l s))
  | Union (s1, s2) -> union ((eval s1 s), (eval s2 s))
  | Inter (s1, s2) -> inter ((eval s1 s), (eval s2 s))
  | Diff (s1, s2) -> diff ((eval s1 s), (eval s2 s))
  | Add (s0, elt) -> add ((eval s0 s), (eval elt s))
  | Remove (s0, elt) -> remove ((eval s0 s), (eval elt s))
  | IsEmpty s0 -> is_empty (eval s0 s)
  | Contains (s0, elt) -> contains ((eval s0 s), (eval elt s))
  | Subset (s1, s2) -> subset ((eval s1 s), (eval s2 s))
  | MinElt s0 -> min_elt (eval s0 s)         
  | MaxElt s0 -> max_elt (eval s0 s)
  | For_all (p, s0) -> let es = eval s0 s in
                         let ep = eval p s in
                           (match (typecheck ("set", es), es) with
                            | (true, Set (t, List_val l)) -> (match (typecheck ("fun ((" ^ t ^ ") -> (bool))", ep), ep) with
                                                              | (true, Closure (arg, fbody, fDecEnv)) -> let rec check ls =
                                                                                                   match ls with
                                                                                                   | [] -> Bool true
                                                                                                   | x :: xs -> let aenv = bind fDecEnv arg x in
                                                                                                                  match (eval fbody aenv) with
                                                                                                                  | Bool b -> if b
                                                                                                                               then check xs
                                                                                                                                  else Bool false
                                                                                                                  | _ -> failwith "Run-time error"
                                                                                                   in check l           
                                                              | (_, _) -> failwith "Run-time error")
                            | (_, _) -> failwith "Run-time error")
  | Exists (p, s0) -> let es = eval s0 s in
                        let ep = eval p s in
                          (match (typecheck ("set", es), es) with
                           | (true, Set (t, List_val l)) -> (match (typecheck ("fun ((" ^ t ^ ") -> (bool))", ep), ep) with
                                                             | (true, Closure (arg, fbody, fDecEnv)) -> let rec check ls =
                                                                                                          match ls with
                                                                                                          | [] -> Bool false
                                                                                                          | x :: xs -> let aenv = bind fDecEnv arg x in
                                                                                                                         match (eval fbody aenv) with
                                                                                                                         | Bool b -> if b
                                                                                                                                      then Bool true 
                                                                                                                                         else check xs
                                                                                                                         | _ -> failwith "Run-time error"
                                                                                                          in check l           
                                                             | (_, _) -> failwith "Run-time error")
                           | (_, _) -> failwith "Run-time error")
  | Filter (p, s0) -> let es = eval s0 s in
                        let ep = eval p s in
                          (match (typecheck ("set", es), es) with
                           | (true, Set (t, List_val l)) -> (match (typecheck ("fun ((" ^ t ^ ") -> (bool))", ep), ep) with
                                                             | (true, Closure (arg, fbody, fDecEnv)) -> let rec create_set ls =
                                                                                                          match ls with
                                                                                                          | [] -> set_empty t
                                                                                                          | x :: xs -> let aenv = bind fDecEnv arg x in
                                                                                                                         match (eval fbody aenv) with
                                                                                                                         | Bool b -> if b
                                                                                                                                      then add (create_set xs, x)
                                                                                                                                         else create_set xs
                                                                                                                         | _ -> failwith "Run-time error"
                                                                                                          in create_set l           
                                                             | (_, _) -> failwith "Run-time error")
                           | (_, _) -> failwith "Run-time error")
  | Map (f, s0) -> let es = eval s0 s in
                     let ef = eval f s in
                       (match (typecheck ("set", es), es) with
                        | (true, Set (t, List_val l)) -> (match (typecheck ("fun", ef), ef) with
                                                          | (true, Closure (arg, fbody, fDecEnv)) -> let rec create_list ls =
                                                                                                      match ls with
                                                                                                      | [] -> []
                                                                                                      | x :: xs -> let aenv = bind fDecEnv arg x in
                                                                                                                     (eval fbody aenv) :: (create_list xs)
                                                                                                      in List_val (create_list l)
                                                          | (_, _) -> failwith "Run-time error")
                        | (_, _) -> failwith "Run-time error")
