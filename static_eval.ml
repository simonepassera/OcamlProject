(* STATIC EVAL *)

#load "str.cma" ;;

type tval =
| Tint
| Tstring
| Tbool
| Tfun of tval * tval
| Trecfun of tval * tval
| Tlist of tval
| Temptylist
| Tset of tval
| Terror
and ide = string ;;

type tenv = ide -> tval ;;

let emptyTenv = fun (x:ide) -> failwith "Empty type env" ;;

let lookupTenv (e:tenv) (i:ide) = e i ;;

let bindTenv (e:tenv) (i:ide) (v:tval) = fun x -> if x = i then v else lookupTenv e x ;;

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
     then failwith "Not a valid type for elements of set"
        else let arg = Str.string_after (Str.string_before s nc1) 1 in
               let str = Str.string_after s (nc1 + 5) in
                 let nc2 = parentheses str in
                   if nc2 = -1
                    then failwith "Not a valid type for elements of set"
                       else (arg, Str.string_after (Str.string_before str nc2) 1) ;;
                       
let rec type_elts_check str =
  let rec type_res t =
    match t with
    | "int" -> Tint
    | "string" -> Tstring
    | "bool" -> Tbool
    | "emptylist" -> Temptylist
    | _ -> let r1 = Str.regexp "\\([a-z]+\\) (\\([a-z>() -]+\\))" in
             if (Str.string_match r1 t 0)
              then (match (Str.matched_group 1 t) with
                   | "list" -> Tlist (type_res (Str.matched_group 2 t))
                   | "set" -> Tset (type_elts_check (Str.matched_group 2 t))
                   | "fun" -> (match (type_param (Str.matched_group 2 t)) with
                               | (arg, res) -> Tfun (type_res arg, type_res res))
                   | "recfun" -> (match (type_param (Str.matched_group 2 t)) with
                                  | (arg, res) -> Trecfun (type_res arg, type_res res))
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
               
type texp =
| CstInt of int
| CstString of string
| CstTrue
| CstFalse
| Den of ide
| Sum of texp * texp
| Sub of texp * texp
| Times of texp * texp
| Ifthenelse of texp * texp * texp
| Eq of texp * texp
| Let of ide * texp * texp
| Fun of ide * tval * texp
| Letrec of ide * ide * tval * texp * tval * texp
| Apply of texp * texp
| List of texp list
| SetEmpty of type_elts
| SetSingleton of type_elts * texp
| SetOf of type_elts * texp
| Union of texp * texp
| Inter of texp * texp
| Diff of texp * texp
| Add of texp * texp
| Remove of texp * texp
| IsEmpty of texp
| Contains of texp * texp
| Subset of texp * texp
| MinElt of texp
| MaxElt of texp
| For_all of texp * texp
| Exists of texp * texp
| Filter of texp * texp
| Map of texp * texp
and type_elts = string ;;

let int_op (t1, t2) =
  match (t1, t2) with
  | (Tint, Tint) -> Tint
  | (_, _) -> failwith "Wrong type" ;;

let set_op0 (s1, s2) =
  match (s1, s2) with
  | (Tset t1, Tset t2) -> if t1 <> t2
                           then failwith "Wrong type"
                              else Tset t1
  | (_, _) -> failwith "Wrong type" ;;

let set_op1 (s, elt) =
  match (s, elt) with
  | (Tset t0, telt) -> if t0 <> telt
                        then failwith "Wrong type"
                           else Tset t0
  | (_, _) -> failwith "Wrong type" ;;

let set_op2 s =
  match s with
  | Tset t -> if (t = Tint) || (t = Tstring)
               then t
                  else failwith "Wrong type"
  | _ -> failwith "Wrong type" ;;

let set_op3 (p, s) =
  match (p, s) with
  | (Tfun (targ, tres), Tset t) -> if (targ <> t) || (tres <> Tbool)
                                    then failwith "Wrong type"
                                       else Tbool
  | (_, _) -> failwith "Wrong type" ;;

let rec teval (e:texp) (s:tenv) =
  match e with
  | CstInt n -> Tint
  | CstString s -> Tstring
  | CstTrue -> Tbool
  | CstFalse -> Tbool
  | Eq (e1, e2) -> if (teval e1 s) = (teval e2 s)
                    then Tbool 
                       else failwith "Wrong type"
  | Times (e1, e2) -> int_op (teval e1 s, teval e2 s)                          
  | Sum (e1, e2) -> int_op (teval e1 s, teval e2 s)
  | Sub (e1, e2) -> int_op (teval e1 s, teval e2 s)
  | Ifthenelse (e1, e2, e3) -> let g = teval e1 s in
                                 (match g with
                                  | Tbool -> let t1 = teval e2 s in
                                               let t2 = teval e3 s in
                                                 if t1 <> t2
                                                  then failwith "Wrong type"
                                                     else t1
                                  | _ -> failwith "Wrong type")
  | Den i -> lookupTenv s i
  | Let (i, e, ebody) -> teval ebody (bindTenv s i (teval e s))
  | Fun (arg, targ, ebody) -> let env = bindTenv s arg targ in
                                let tres = teval ebody env in
                                  Tfun (targ, tres)
  | Letrec (f, arg, targ, fBody, tres, letBody) -> let renv = bindTenv s f (Trecfun (targ, tres)) in
                                                     let env = bindTenv renv arg targ in
                                                       if (teval fBody env) = tres
                                                        then teval letBody renv
                                                           else failwith "Wrong type"
  | Apply (eF, eArg) -> let f = teval eF s in
                          (match f with
                           | Tfun (targ, tres) -> if (teval eArg s) = targ
                                                   then tres
                                                      else failwith "Wrong type"
                           | Trecfun (targ, tres) -> if (teval eArg s) = targ
                                                      then tres
                                                         else failwith "Wrong type"
                           | _ -> failwith "Wrong type")
  | List l -> if l = []
               then Temptylist
                  else let t1 = teval (List.nth l 0) s in
                         let rec check ls = 
                           match ls with
                           | [] -> Tlist t1
                           | x :: xs -> let tx = teval x s in
                                          if tx = t1
                                           then check xs
                                              else failwith "Wrong type"
                           in check l
  | SetEmpty t -> Tset (type_elts_check t)
  | SetSingleton (t, elt) -> let t1 = type_elts_check t in
                               if t1 = (teval elt s)
                                then Tset t1
                                   else failwith "Wrong type"
  | SetOf (t, l) -> let t1 = type_elts_check t in 
                      (match (teval l s) with
                       | Tlist tl -> if tl = t1
                                      then Tset t1
                                         else failwith "Wrong type"
                       | _ -> failwith "Wrong type")
  | Union (s1, s2) -> set_op0 (teval s1 s, teval s2 s)
  | Inter (s1, s2) -> set_op0 (teval s1 s, teval s2 s)
  | Diff (s1, s2) -> set_op0 (teval s1 s, teval s2 s)
  | Add (s0, elt) -> set_op1 (teval s0 s, teval elt s)
  | Remove (s0, elt) -> set_op1 (teval s0 s, teval elt s)
  | IsEmpty s0 -> (match (teval s0 s) with
                   | Tset t -> Tbool
                   | _ -> failwith "Wrong type")
  | Contains (s0, elt) -> (match (teval s0 s, teval elt s) with
                           | (Tset t0, telt) ->  if t0 <> telt
                                                  then failwith "Wrong type"
                                                     else Tbool
                           | (_, _) -> failwith "Wrong type")
  | Subset (s1, s2) -> (match (teval s1 s, teval s2 s) with
                        | (Tset t1, Tset t2) ->  if t1 <> t2
                                                  then failwith "Wrong type"
                                                     else Tbool
                        | (_, _) -> failwith "Wrong type")
  | MinElt s0 -> set_op2 (teval s0 s)
  | MaxElt s0 -> set_op2 (teval s0 s)
  | For_all (p, s0) -> set_op3 (teval p s, teval s0 s)
  | Exists (p, s0) -> set_op3 (teval p s, teval s0 s)
  | Filter (p, s0) -> (match (teval p s, teval s0 s) with
                       | (Tfun (targ, tres), Tset t) -> if (targ <> t) || (tres <> Tbool)
                                                         then failwith "Wrong type"
                                                            else Tset t
                       | (_, _) -> failwith "Wrong type")

  | Map (f, s0) -> (match (teval f s, teval s0 s) with
                    | (Tfun (targ, tres), Tset t0) -> if targ <> t0
                                                       then failwith "Wrong type"
                                                          else Tlist tres
                    | (_, _) -> failwith "Wrong type")

type 'v env = (string * 'v) list ;;

type valT =
| Int of int
| String of string
| Bool of bool
| Closure of ide * texp * valT env
| RecClosure of ide * ide * texp * valT env
| List_val of valT list
| Set of type_elts * valT
| Unbound
| Error ;;

let emptyEnv = [("", Unbound)] ;;

let rec lookup (s:valT env) (i:string) =
  match s with
  | [("", Unbound)] -> Unbound
  | (x, v) :: s2 -> if x = i
                     then v
                        else lookup s2 i
  | [] -> failwith "Wrong env" ;; 

let bind (e:valT env) (s:string) (v:valT) = (s, v) :: e ;;

let int_sum (x, y) =
  match(x, y) with
  | (Int v, Int w) -> Int (v + w)
  | (_, _) -> failwith "Run-time error" ;;

let int_sub (x, y) =
  match(x, y) with
  | (Int v, Int w) -> Int (v - w)
  | (_, _) -> failwith "Run-time error" ;;

let int_times (x, y) =
  match(x, y) with
  | (Int v, Int w) -> Int (v * w)
  | (_, _) -> failwith "Run-time error" ;;

let contains (s, elt) =
  match s with
  | Set (t, List_val l) -> let rec f (ls, e) =
                             match ls with
                             | [] -> false
                             | x :: xs -> if x = elt
                                           then true
                                              else f (xs, e)
                             in Bool (f (l, elt))
  | _ -> failwith "Run-time error" ;;

let add (s, elt) =
  match s with
  | Set (t, List_val l) -> if contains (s, elt) = Bool true
                            then Set (t, List_val l)
                               else Set (t, List_val (elt :: l))
  | _ -> failwith "Run-time error" ;;

let set_empty t = Set (t, List_val []) ;;

let set_singleton (t, elt) = add (set_empty t, elt) ;;

let set_of (t, l) = 
  match l with
  | List_val le -> let rec create_set ls =
                     match ls with
                     | [] -> set_empty t
                     | x :: xs -> add (create_set xs, x)
                     in create_set le
  | _ -> failwith "Run-time error" ;;

let remove (s, elt) =
  match s with
  | Set (t, List_val l) -> let rec f ls =
                             match ls with
                             | [] -> []
                             | x :: xs -> if x = elt
                                           then xs
                                              else x :: f xs
                             in Set (t, List_val (f l))
  | _ -> failwith "Run-time error" ;;

let is_empty s =
  match s with
  | Set (t, List_val l) -> Bool (l = [])
  | _ -> failwith "Run-time error" ;;

let min_elt s =
  match s with
  | Set (t, List_val l) -> (match t with
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
  | _ -> failwith "Run-time error" ;;

let max_elt s =
  match s with
  | Set (t, List_val l) -> (match t with
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
  | _ -> failwith "Run-time error" ;;

let union (s1, s2) =
  match s2 with
  | Set (t2, List_val l2) -> let rec create_set ls =
                               match ls with
                               | [] -> s1
                               | x :: xs -> add (create_set xs, x)
                               in create_set l2
  | _ -> failwith "Run-time error" ;;

let inter (s1, s2) =
  match s1 with
  | Set (t1, List_val l1) -> let rec create_set ls =
                               match ls with
                               | [] -> set_empty t1
                               | x :: xs -> if contains (s2, x) = Bool true
                                             then add (create_set xs, x)
                                                else create_set xs
                               in create_set l1
  | _ -> failwith "Run-time error" ;;

let diff (s1, s2) =
  match s1 with
  | Set (t1, List_val l1) -> let rec create_set ls =
                               match ls with
                               | [] -> set_empty t1
                               | x :: xs -> if contains (s2, x) = Bool false
                                             then add (create_set xs, x)
                                                else create_set xs
                               in create_set l1                                     
  | _ -> failwith "Run-time error" ;;

let eq (x, y) =
  match (x, y) with
  | (Set (t1, List_val l1), Set (t2, List_val l2)) -> if (is_empty (diff (x, y))) = Bool true
                                                       then is_empty (diff (y, x))
                                                          else Bool false
  | (_, _) -> Bool (x = y) ;;

let subset (s1, s2) =
  match s1 with
  | Set (t1, List_val l1) -> let rec check ls =
                               match ls with
                               | [] -> Bool true
                               | x :: xs -> if contains (s2, x) = Bool true
                                             then check xs
                                                else Bool false
                               in check l1
  | _ -> failwith "Run-time error" ;;

let rec eval (e:texp) (s:valT env) =
  match e with
  | CstInt n -> Int n
  | CstString s -> String s
  | CstTrue -> Bool true
  | CstFalse -> Bool false
  | Eq (e1, e2) -> eq ((eval e1 s), (eval e2 s))
  | Times (e1, e2) -> int_times ((eval e1 s), (eval e2 s))
  | Sum (e1, e2) -> int_sum ((eval e1 s), (eval e2 s))
  | Sub (e1, e2) -> int_sub ((eval e1 s), (eval e2 s))
  | Ifthenelse (e1, e2, e3) -> (match (eval e1 s) with
                                | Bool true -> eval e2 s
                                | Bool false -> eval e3 s
                                | _ -> failwith "Run-time error")
  | Den i -> lookup s i
  | Let (i, e, ebody) -> eval ebody (bind s i (eval e s))
  | Fun (arg, targ, ebody) -> Closure (arg, ebody, s)
  | Letrec (f, arg, targ, fBody, tres, letBody) -> let benv = bind s f (RecClosure (f, arg, fBody, s)) in
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
  | List l -> let rec f ls = 
                match ls with
                | [] -> []
                | x :: xs -> (eval x s) :: f xs
                in List_val (f l)
  | SetEmpty t -> set_empty t
  | SetSingleton (t, elt) -> set_singleton (t, (eval elt s))
  | SetOf (t, l) -> set_of (t, (eval l s))
  | Union (s1, s2) -> union ((eval s1 s), (eval s2 s))
  | Inter (s1, s2) -> inter ((eval s1 s),(eval s2 s))
  | Diff (s1, s2) -> diff ((eval s1 s), (eval s2 s))
  | Add (s0, elt) -> add ((eval s0 s), (eval elt s))
  | Remove (s0, elt) -> remove ((eval s0 s), (eval elt s))
  | IsEmpty s0 -> is_empty (eval s0 s)
  | Contains (s0, elt) -> contains ((eval s0 s), (eval elt s))
  | Subset (s1, s2) -> subset ((eval s1 s), (eval s2 s))
  | MinElt s0 -> min_elt (eval s0 s)         
  | MaxElt s0 -> max_elt (eval s0 s)
  | For_all (p, s0) -> (match (eval s0 s) with
                        | Set (t, List_val l) -> (match (eval p s) with
                                                  | Closure (arg, fbody, fDecEnv) -> let rec check ls =
                                                                                       match ls with
                                                                                       | [] -> Bool true
                                                                                       | x :: xs -> let aenv = bind fDecEnv arg x in
                                                                                                      if (eval fbody aenv) = Bool true
                                                                                                       then check xs
                                                                                                          else Bool false
                                                                                       in check l
                                         | _ -> failwith "Run-time error")
                        | _ -> failwith "Run-time error")
  | Exists (p, s0) -> (match (eval s0 s) with
                       | Set (t, List_val l) -> (match (eval p s) with
                                                 | Closure (arg, fbody, fDecEnv) -> let rec check ls =
                                                                                      match ls with
                                                                                      | [] -> Bool false
                                                                                      | x :: xs -> let aenv = bind fDecEnv arg x in
                                                                                                     if (eval fbody aenv) = Bool true
                                                                                                      then Bool true 
                                                                                                         else check xs
                                                                                      in check l           
                                        | _ -> failwith "Run-time error")
                       | _ -> failwith "Run-time error")
  | Filter (p, s0) -> (match (eval s0 s) with
                       | Set (t, List_val l) -> (match (eval p s) with
                                                 | Closure (arg, fbody, fDecEnv) -> let rec create_set ls =
                                                                                      match ls with
                                                                                      | [] -> set_empty t
                                                                                      | x :: xs -> let aenv = bind fDecEnv arg x in
                                                                                                     if (eval fbody aenv) = Bool true
                                                                                                      then add (create_set xs, x)
                                                                                                         else create_set xs
                                                                                      in create_set l           
                                        | _ -> failwith "Run-time error")
                       | _ -> failwith "Run-time error")
  | Map (f, s0) -> (match (eval s0 s) with
                    | Set (t, List_val l) -> (match (eval f s) with
                                              | Closure (arg, fbody, fDecEnv) -> let rec create_list ls =
                                                                                   match ls with
                                                                                   | [] -> []
                                                                                   | x :: xs -> let aenv = bind fDecEnv arg x in
                                                                                                  (eval fbody aenv) :: (create_list xs)
                                                                                   in List_val (create_list l)
                                              | _ -> failwith "Run-time error")
                    | _ -> failwith "Run-time error") ;;

print_endline "\n\nTEST CstInt" ;;
let t = CstInt 5 ;;
teval t emptyTenv ;;
eval t emptyEnv ;;

print_endline "\n\nTEST CstString" ;;
let t = CstString "string-test" ;;
teval t emptyTenv ;;
eval t emptyEnv ;;

print_endline "\n\nTEST CstTrue" ;;
let t = CstTrue ;;
teval t emptyTenv ;;
eval t emptyEnv ;;

print_endline "\n\nTEST CstFalse" ;;
let t = CstFalse ;;
teval t emptyTenv ;;
eval t emptyEnv ;;

print_endline "\n\nTEST Let" ;;
let t = Let ("x", CstInt 3, CstTrue) ;;
teval t emptyTenv ;;
eval t emptyEnv ;;

print_endline "\n\nTEST Den" ;;
let t = Let ("x", CstInt 3, Den "x") ;;
teval t emptyTenv ;;
eval t emptyEnv ;;

print_endline "\n\nTEST Sum" ;;
let t = Let ("x", CstInt 5, Let ("y", CstInt 7, Sum (Den "x", Den "y"))) ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = Let ("x", CstInt 5, Let ("y", CstString "string-test", Sum (Den "x", Den "y"))) ;;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;

print_endline "\n\nTEST Sub" ;;
let t = Let ("x", CstInt 5, Let ("y", CstInt 7, Sub (Den "x", Den "y"))) ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = Let ("x", CstInt 5, Let ("y", CstString "string-test", Sub (Den "x", Den "y"))) ;;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;

print_endline "\n\nTEST Times" ;;
let t = Let ("x", CstInt 5, Let ("y", CstInt 7, Times (Den "x", Den "y"))) ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = Let ("x", CstInt 5, Let ("y", CstString "string-test", Times (Den "x", Den "y"))) ;;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;

print_endline "\n\nTEST Ifthenelse" ;;
let t = Let ("x", CstInt 5, Ifthenelse (CstTrue, CstInt 7, Sum (Den "x", CstInt 3))) ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = Let ("x", CstInt 5, Ifthenelse (CstTrue, CstString "string-test", Sum (Den "x", CstInt 3))) ;;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;

print_endline "\n\nTEST Fun" ;;
let t = Let ("f", Fun ("x", Tint, Sum (Den "x", CstInt 3)), Den "f") ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = Let ("f", Fun ("x", Tstring, Sum (Den "x", CstInt 3)), Den "f") ;;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;

print_endline "\n\nTEST Letrec" ;;
let t = Letrec ("f", "x", Tint, Ifthenelse (Eq (Den "x", CstInt 0), CstTrue, Apply (Den "f", Sub (Den "x", CstInt 1))), Tbool, Den "f") ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = Letrec ("f", "x", Tint, Ifthenelse (Eq (Den "x", CstInt 0), CstTrue, Apply (Den "f", Sub (Den "x", CstInt 1))), Tint, Den "f") ;;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;

print_endline "\n\nTEST Apply" ;;
let t = Letrec ("f", "x", Tint, Ifthenelse (Eq (Den "x", CstInt 0), CstTrue, Apply (Den "f", Sub (Den "x", CstInt 1))), Tbool, Apply (Den "f", CstInt 4)) ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = Letrec ("f", "x", Tint, Ifthenelse (Eq (Den "x", CstInt 0), CstTrue, Apply (Den "f", Sub (Den "x", CstInt 1))), Tint, Apply (Den "f", CstFalse)) ;;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;

print_endline "\n\nTEST List" ;;
let t = List [CstInt 3; CstInt 5];;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = List [];;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = List [CstInt 3; CstTrue];;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;

print_endline "\n\nTEST SetEmpty" ;;
let t = SetEmpty "int" ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = SetEmpty "fun ((fun ((list (int)) -> (set (int)))) -> (bool))" ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = SetEmpty "set (int)" ;;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;

print_endline "\n\nTEST SetSingleton" ;;
let t = SetSingleton ("int", CstInt 3) ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = SetSingleton ("int", CstString "string-test") ;;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;

print_endline "\n\nTEST SetOf" ;;
let t = SetOf ("string", List ([CstString "string1"; CstString "string2"])) ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = SetOf ("string", List ([CstString "string1"; CstInt 3])) ;;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;

print_endline "\n\nTEST Add" ;;
let set = SetSingleton ("int", CstInt 3) ;;
let t = Add (set, CstInt 4) ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = Add (set, CstInt 4) ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = Add (set, CstTrue) ;;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;
let set2 = SetEmpty "fun ((int) -> (bool))" ;;
let t = Add (set2, Fun ("x", Tint, Ifthenelse(Eq (Den "x", CstInt 0), CstTrue, CstFalse))) ;;
teval t emptyTenv ;;
eval t emptyEnv ;;

print_endline "\n\nTEST Remove" ;;
let set = SetSingleton ("int", CstInt 3) ;;
let t = Remove (set, CstInt 4) ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = Remove (set, CstInt 3) ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = Remove (set, CstTrue) ;;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;

print_endline "\n\nTEST Union" ;;
let set1 = SetOf ("int", List [CstInt 3; CstInt 4; CstInt 6]) ;;
let set2 = SetOf ("int", List [CstInt 7; CstInt 9; CstInt 4]) ;;
let t = Union (set1, set2);;
teval t emptyTenv ;;
eval t emptyEnv ;;
let set3 = SetEmpty "string" ;;
let t = Union (set3, set3);;
teval t emptyTenv ;;
eval t emptyEnv ;;

print_endline "\n\nTEST Inter" ;;
let set1 = SetOf ("int", List [CstInt 3; CstInt 4; CstInt 6]) ;;
let set2 = SetOf ("int", List [CstInt 7; CstInt 9; CstInt 4]) ;;
let t = Inter (set1, set2);;
teval t emptyTenv ;;
eval t emptyEnv ;;
let set3 = SetEmpty "string" ;;
let t = Inter (set3, set3);;
teval t emptyTenv ;;
eval t emptyEnv ;;

print_endline "\n\nTEST Diff" ;;
let set1 = SetOf ("int", List [CstInt 3; CstInt 4; CstInt 6]) ;;
let set2 = SetOf ("int", List [CstInt 7; CstInt 9; CstInt 4]) ;;
let t = Diff (set1, set2);;
teval t emptyTenv ;;
eval t emptyEnv ;;
let set3 = SetEmpty "string" ;;
let t = Diff (set3, set3);;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = Diff (set2, set1);;
teval t emptyTenv ;;
eval t emptyEnv ;;

print_endline "\n\nTEST Subset" ;;
let set1 = SetOf ("int", List [CstInt 9; CstInt 4]) ;;
let set2 = SetOf ("int", List [CstInt 7; CstInt 9; CstInt 4]) ;;
let t = Subset (set1, set2);;
teval t emptyTenv ;;
eval t emptyEnv ;;
let set3 = SetEmpty "string" ;;
let t = Subset (set3, set3);;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = Subset (set2, set1);;
teval t emptyTenv ;;
eval t emptyEnv ;;

print_endline "\n\nTEST Eq" ;;
let set1 = SetOf ("int", List [CstInt 9; CstInt 4; CstInt 7]) ;;
let set2 = SetOf ("int", List [CstInt 7; CstInt 9; CstInt 4]) ;;
let t = Eq (set1, set2);;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = Eq (List [CstInt 2; CstInt 5], List [CstInt 5; CstInt 2]) ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = Eq (CstInt 5, CstString "string-test") ;;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;

print_endline "\n\nTEST IsEmpty" ;;
let set1 = SetOf ("int", List [CstInt 9; CstInt 4]) ;;
let t = IsEmpty set1 ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let set2 = SetEmpty "string" ;;
let t = IsEmpty set2 ;;
teval t emptyTenv ;;
eval t emptyEnv ;;

print_endline "\n\nTEST Contains" ;;
let set = SetOf ("int", List [CstInt 9; CstInt 4; CstInt 7]) ;;
let t = Contains (set, CstInt 7);;
teval t emptyTenv ;;
eval t emptyEnv ;;
let t = Contains (set, CstString "string-test");;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;

print_endline "\n\nTEST MinElt" ;;
let set1 = SetOf ("int", List [CstInt 47; CstInt 6; CstInt 17]) ;;
let t = MinElt set ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let set2 =  SetOf ("string", List [CstString "rosso"; CstString "verde"; CstString "blu"]) ;;
let t = MinElt set2 ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let set3 = SetSingleton ("bool", CstFalse) ;;
let t = MinElt set3 ;;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;

print_endline "\n\nTEST MaxElt" ;;
let set1 = SetOf ("int", List [CstInt 47; CstInt 6; CstInt 17]) ;;
let t = MaxElt set ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let set2 =  SetOf ("string", List [CstString "rosso"; CstString "verde"; CstString "blu"]) ;;
let t = MaxElt set2 ;;
teval t emptyTenv ;;
eval t emptyEnv ;;
let set3 = SetEmpty "int" ;;
let t = MaxElt set3 ;;
teval t emptyTenv ;;
try eval t emptyEnv with e -> print_endline (Printexc.to_string e) ; Error ;;

print_endline "\n\nTEST For_all" ;;
let set = SetOf ("int", List [CstInt 3; CstInt 6; CstInt 8])
let f = Fun ("x", Tint, Eq (CstInt 10, Den "x" )) ;;
let t = For_all (f, set);;
teval t emptyTenv ;;
eval t emptyEnv ;;
let f = Fun ("x", Tint, CstString "string-test") ;;
let t = For_all (f, set);;
try teval t emptyTenv with e -> print_endline (Printexc.to_string e) ; Terror ;;

print_endline "\n\nTEST Exists" ;;
let set = SetOf ("int", List [CstInt 3; CstInt 6; CstInt 8])
let f = Fun ("x", Tint, Eq (CstInt 6, Den "x" )) ;;
let t = Exists (f, set);;
teval t emptyTenv ;;
eval t emptyEnv ;;

print_endline "\n\nTEST Filter" ;;
let set = SetOf ("int", List [CstInt 3; CstInt 6; CstInt 8])
let f = Fun ("x", Tint, Eq (CstInt 6, Den "x" )) ;;
let t = Filter (f, set);;
teval t emptyTenv ;;
eval t emptyEnv ;;

print_endline "\n\nTEST Map" ;;
let set = SetOf ("int", List [CstInt 3; CstInt 6; CstInt 8])
let f = Fun ("x", Tint, Sum (CstInt 2, Den "x" )) ;;
let t = Map (f, set);;
teval t emptyTenv ;;
eval t emptyEnv ;;

