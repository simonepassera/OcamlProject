(* STATIC EVAL *)

type tval =
| Tint
| Tstring
| Tbool
| Tfun of tval * tval
| Trecfun of tval * tval
| Tset of tval
and ide = string ;;

type tenv = ide -> tval ;;

let emptyTenv = fun (x:ide) -> failwith "Empty type env" ;;

let lookupTenv (e:tenv) (i:ide) = e i ;;

let bindTenv (e:tenv) (i:ide) (v:tval) = fun x -> if x = i then v else lookupTenv e x ;;
(*
#load "str.cma" ;;
*)
let rec type_elts_check t =
  match t with
  | "int" -> Tint
  | "string" -> Tstring
  | "bool" -> Tbool
  | _ -> let r = Str.regexp "\\([a-z]+\\) (\\([a-z->() ]+\\) -> \\([a-z->() ]+\\))" in
           if (Str.string_match r t 0)
            then (match (Str.matched_group 1 t) with
                  | "fun" -> Tfun (type_elts_check (Str.matched_group 2 t), type_elts_check (Str.matched_group 3 t))
                  | "recfun" -> Trecfun (type_elts_check (Str.matched_group 2 t), type_elts_check (Str.matched_group 3 t))
                  | _ -> failwith "Not a valid type for elements of set")
               else failwith "Not a valid type for elements of set" ;;

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
| SetEmpty of type_elts
| SetSingleton of type_elts * texp
| SetOf of type_elts * elts
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
and type_elts = string
and elts = texp list ;;

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
  | Eq (e1, e2) -> let t1 = teval e1 s in
                     (match t1 with
                      | Tfun (targ, tres) -> failwith "Wrong type"
                      | Trecfun (targ, tres) -> failwith "Wrong type"
                      | Tset t -> (match t with
                                   | Tfun (targ2, tres2) -> failwith "Wrong type"
                                   | Trecfun (targ2, tres2) -> failwith "Wrong type"
                                   | _ -> if t1 = (teval e2 s)
                                           then Tbool 
                                              else failwith "Wrong type")
                      | _ -> if t1 = (teval e2 s)
                              then Tbool 
                                 else failwith "Wrong type")
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
                                                        then teval letBody (bindTenv s f (Trecfun (targ, tres)))
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
  | SetEmpty t -> Tset (type_elts_check t)
  | SetSingleton (t, elt) -> let t1 = type_elts_check t in
                               if t1 = (teval elt s)
                                then Tset t1
                                   else failwith "Wrong type"
  | SetOf (t, l) -> let t1 = type_elts_check t in 
                      if l = []
                       then failwith "Wrong type"
                          else let rec check ls = 
                                 match ls with
                                 | [] -> Tset t1
                                 | x :: xs -> let tx = teval x s in
                                                if tx = t1
                                                 then check xs
                                                    else failwith "Wrong type"
                                 in check l
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
                                                          else (match tres with
                                                                | Tset t1 -> failwith "Wrong type"
                                                                | _ -> Tset tres)
                    | (_, _) -> failwith "Wrong type")

type 'v env = string -> 'v ;;

type valT =
| Int of int
| String of string
| Bool of bool
| Closure of ide * texp * valT env
| RecClosure of ide * ide * texp * valT env
| Set of type_elts * (valT list)
| Unbound ;;

let emptyEnv = fun (x:string) -> Unbound ;;

let lookup (s:valT env) (i:string) = s i ;;

let bind (e:valT env) (s:string) (v:valT) = fun c -> if c = s then v else lookup e c ;;

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
  | Set (t, l) -> let rec f (ls, e) =
                    match ls with
                    | [] -> false
                    | x :: xs -> if x = elt
                                  then true
                                     else f (xs, e)
                    in Bool (f (l, elt))
  | _ -> failwith "Run-time error" ;;

let add (s, elt) =
  match s with
  | Set (t, l) -> if contains (s, elt) = Bool true
                   then Set (t, l)
                      else Set (t, elt :: l)
  | _ -> failwith "Run-time error" ;;

let set_empty t = Set (t, []) ;;

let set_singleton (t, elt) = add (set_empty t, elt) ;;

let set_of (t, l) = let rec create_set ls =
                      match ls with
                      | [] -> set_empty t
                      | x :: xs -> add (create_set xs, x)
                      in create_set l ;;

let remove (s, elt) =
  match s with
  | Set (t, l) -> let rec f ls =
                    match ls with
                    | [] -> []
                    | x :: xs -> if x = elt
                                  then xs
                                     else x :: f xs
                    in Set (t, f l)
  | _ -> failwith "Run-time error" ;;

let is_empty s =
  match s with
  | Set (t, l) -> Bool (l = [])
  | _ -> failwith "Run-time error" ;;

let min_elt s =
  match s with
  | Set (t, l) -> (match t with
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
  | Set (t, l) -> (match t with
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
  | Set (t2, l2) -> let rec create_set ls =
                      match ls with
                      | [] -> s1
                      | x :: xs -> add (create_set xs, x)
                      in create_set l2
  | _ -> failwith "Run-time error" ;;

let inter (s1, s2) =
  match s1 with
  | Set (t1, l1) -> let rec create_set ls =
                      match ls with
                      | [] -> set_empty t1
                      | x :: xs -> if contains (s2, x) = Bool true
                                    then add (create_set xs, x)
                                       else create_set xs
                      in create_set l1
  | _ -> failwith "Run-time error" ;;

let diff (s1, s2) =
  match s1 with
  | Set (t1, l1) -> let rec create_set ls =
                      match ls with
                      | [] -> set_empty t1
                      | x :: xs -> if contains (s2, x) = Bool false
                                    then add (create_set xs, x)
                                       else create_set xs
                      in create_set l1                                     
  | _ -> failwith "Run-time error" ;;

let eq (x, y) =
  match (x, y) with
  | (Int v, Int w) -> Bool (v = w)
  | (String v, String w) -> Bool (v = w)
  | (Bool v, Bool w) -> Bool (v = w)
  | (Set (t1, l1), Set (t2, l2)) -> if (is_empty (diff (x, y))) = Bool true
                                     then is_empty (diff (y, x))
                                        else Bool false
  | (_, _) -> failwith "Run-time error" ;;

let subset (s1, s2) =
  match s1 with
  | Set (t1, l1) -> let rec check ls =
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
  | SetEmpty t -> set_empty t
  | SetSingleton (t, elt) -> set_singleton (t, (eval elt s))
  | SetOf (t, l) -> let rec f ls = 
                      match ls with
                      | [] -> []
                      | x :: xs -> (eval x s) :: f xs
                      in set_of (t, f l)
  | Union (s1, s2) -> union ((eval s1 s), (eval s2 s))
  | Inter (s1, s2) -> inter ((eval s1 s),(eval s2 s))
  | Diff (s1, s2) -> diff ((eval s1 s), (eval s2 s))
  | Add (s0, elt) -> add ((eval s0 s), (eval elt s))
  | Remove (s0, elt) -> remove ((eval s0 s), (eval elt s))
  | IsEmpty s0 -> is_empty (eval s0 s)
  | Contains (s0, elt) ->  contains ((eval s0 s), (eval elt s))
  | Subset (s1, s2) -> subset ((eval s1 s), (eval s2 s))
  | MinElt s0 -> min_elt (eval s0 s)         
  | MaxElt s0 -> max_elt (eval s0 s)
  | For_all (p, s0) -> (match (eval s0 s) with
                        | Set (t, l) -> (match (eval p s) with
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
                       | Set (t, l) -> (match (eval p s) with
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
                       | Set (t, l) -> (match (eval p s) with
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
                    | Set (t, l) -> (match (eval f s) with
                                     | Closure (arg, fbody, fDecEnv) -> let type_res v =
                                                                          match (eval fbody (bind fDecEnv arg v)) with
                                                                          | Int r -> "int"
                                                                          | String r -> "string"
                                                                          | Bool r -> "bool"
                                                                          | _ -> failwith "Run-time error"
                                                                          in let rec create_set ls =
                                                                               match ls with
                                                                               | x :: [] -> set_empty (type_res x)
                                                                               | x :: xs -> let aenv = bind fDecEnv arg x in
                                                                                              add (create_set xs, (eval fbody aenv))
                                                                               | _ -> failwith "Run-time error"
                                                                               in create_set l
                                     | _ -> failwith "Run-time error")
                    | _ -> failwith "Run-time error")
