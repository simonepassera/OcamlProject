(* The language *)

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
| SetEmpty of type_elts
| SetSingleton of type_elts * exp
| SetOf of type_elts * elts
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
and type_elts = string
and elts = exp list ;;

type 'v env = string -> 'v ;;

type evT =
| Int of int
| String of string
| Bool of bool
| Closure of ide * exp * evT env
| RecClosure of ide * ide * exp * evT env
| Set of type_elts * (evT list)
| Unbound ;;

let emptyEnv = fun (x:string) -> Unbound ;;

let lookup (s:evT env) (i:string) = s i ;;

let bind (e:evT env) (s:string) (v:evT) = fun c -> if c = s then v else lookup e c ;;

let typecheck (x, y) =
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
  | "set" -> (match y with
              | Set (t, l) -> true
              | _ -> false)
  | "fun" -> (match y with
              | Closure (arg, fbody, fDecEnv) -> true
              | RecClosure (f, arg, fbody, fDecEnv) -> true
              | _ -> false)
  | _ -> failwith "Not a valid type" ;;

let type_elts_check t =
  match t with
  | "int" -> true
  | "string" -> true
  | "bool" -> true
  | "fun" -> true
  | _ -> false ;;

let int_eq (x, y) =
  match (typecheck ("int", x), typecheck ("int", y), x, y) with
  | (true, true, Int v, Int w) -> Bool (v = w)
  | (_, _, _, _) -> failwith "Run-time error" ;;

let int_plus (x, y) =
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
  | (true, Set (t, l)) -> (match (typecheck (t, elt)) with
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
  | (true, Set (t, l)) -> (match (typecheck (t, elt)) with
                           | true -> if contains (s, elt) = Bool true
                                      then Set (t, l)
                                         else Set (t, elt :: l)
                           | _ -> failwith "Run-time error")
  | (_, _) -> failwith "Run-time error" ;;

let set_empty t =
  match (type_elts_check t) with
  | true -> Set (t, [])
  | _ -> failwith "Not a valid type for elements of set" ;;

let set_singleton (t, elt) = add (set_empty t, elt) ;;

let set_of (t, l) =
  match (type_elts_check t) with
  | true -> if l = []
             then failwith "Run-time error"
                else let rec create_set ls =
                       match ls with
                       | [] -> set_empty t
                       | x :: xs -> add (create_set xs, x)
                       in create_set l    
  | _ -> failwith "Not a valid type for elements of set" ;;

let remove (s, elt) =
  match (typecheck ("set", s), s) with
  | (true, Set (t, l)) -> (match (typecheck (t, elt)) with
                           | true -> let rec f ls =
                                       match ls with
                                       | [] -> []
                                       | x :: xs -> if x = elt
                                                     then xs
                                                        else x :: f xs
                                       in Set (t, f l) 
                           | _ -> failwith "Run-time error")
  | (_, _) -> failwith "Run-time error" ;;

let is_empty s =
  match (typecheck ("set", s), s) with
  | (true, Set (t, l)) -> Bool (l = [])
  | (_, _) -> failwith "Run-time error" ;;

let min_elt s =
  match (typecheck ("set", s), s) with
  | (true, Set (t, l)) -> (match t with
                           | "int" -> let rec int_min ls =
                                        match ls with
                                        | [] -> Unbound
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
                                            | [] -> Unbound
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
  | (true, Set (t, l)) -> (match t with
                           | "int" -> let rec int_max ls =
                                        match ls with
                                        | [] -> Unbound
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
                                            | [] -> Unbound
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
  | (true, true, Set (t1, l1), Set (t2, l2)) -> if t1 <> t2
                                                 then failwith "Run-time error"
                                                    else (match (type_elts_check t1) with
                                                          | true -> let rec create_set ls =
                                                                      match ls with
                                                                      | [] -> s1
                                                                      | x :: xs -> add (create_set xs, x)
                                                                      in create_set l2
                                                          | _ -> failwith "Run-time error")
  | (_, _, _, _) -> failwith "Run-time error" ;;

let inter (s1, s2) =
  match (typecheck ("set", s1), typecheck ("set", s2), s1, s2) with
  | (true, true, Set (t1, l1), Set (t2, l2)) -> if t1 <> t2
                                                 then failwith "Run-time error"
                                                    else (match (type_elts_check t1) with
                                                          | true -> let rec create_set ls =
                                                                      match ls with
                                                                      | [] -> set_empty t1
                                                                      | x :: xs -> if contains (s2, x) = Bool true
                                                                                    then add (create_set xs, x)
                                                                                       else create_set xs
                                                                      in create_set l1
                                                          | _ -> failwith "Run-time error")
  | (_, _, _, _) -> failwith "Run-time error" ;;

let diff (s1, s2) =
  match (typecheck ("set", s1), typecheck ("set", s2), s1, s2) with
  | (true, true, Set (t1, l1), Set (t2, l2)) -> if t1 <> t2
                                                 then failwith "Run-time error"
                                                    else (match (type_elts_check t1) with
                                                          | true -> let rec create_set ls =
                                                                      match ls with
                                                                      | [] -> set_empty t1
                                                                      | x :: xs -> if contains (s2, x) = Bool false
                                                                                    then add (create_set xs, x)
                                                                                       else create_set xs
                                                                      in create_set l1
                                                          | _ -> failwith "Run-time error")
  | (_, _, _, _) -> failwith "Run-time error" ;;

let subset (s1, s2) =
  match (typecheck ("set", s1), typecheck ("set", s2), s1, s2) with
  | (true, true, Set (t1, l1), Set (t2, l2)) -> if t1 <> t2
                                                 then failwith "Run-time error"
                                                    else (match (type_elts_check t1) with
                                                          | true -> let rec check ls =
                                                                      match ls with
                                                                      | [] -> Bool true
                                                                      | x :: xs -> if contains (s2, x) = Bool true
                                                                                    then check xs
                                                                                       else Bool false
                                                                      in check l1
                                                          | _ -> failwith "Run-time error")
  | (_, _, _, _) -> failwith "Run-time error" ;;

let rec eval (e:exp) (s:evT env) =
  match e with
  | CstInt n -> Int n
  | CstString s -> String s
  | CstTrue -> Bool true
  | CstFalse -> Bool false
  | Eq (e1, e2) -> int_eq ((eval e1 s), (eval e2 s))
  | Times (e1, e2) -> int_times ((eval e1 s), (eval e2 s))
  | Sum (e1, e2) -> int_plus ((eval e1 s), (eval e2 s))
  | Sub (e1, e2) -> int_sub ((eval e1 s), (eval e2 s))
  | Ifthenelse (e1, e2, e3) -> let g = eval e1 s in
                                 (match (typecheck ("bool", g), g) with
                                  | (true, Bool true) -> eval e2 s
                                  | (true, Bool false) -> eval e3 s
                                  | (_, _) -> failwith "Not boolean guard")
  | Den i -> lookup s i
  | Let (i, e, ebody) -> eval ebody (bind s i (eval e s))
  | Fun (arg, ebody) -> Closure (arg, ebody, s)
  | Letrec (f, arg, fBody, letBody) -> let benv = bind s f (RecClosure (f, arg, fBody,s)) in
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
                           | _ -> failwith "Not functional value")
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
  | For_all (p, s0) -> let es = eval s0 s in
                         (match (typecheck ("set", es), es) with
                          | (true, Set (t, l)) -> (match (pred_check (eval p s, t), p) with
                                                   | (true, Closure (arg, fbody, fDecEnv)) -> let rec check ls =
                                                                                               match ls with
                                                                                               | [] -> Bool true
                                                                                               | x :: xs -> let aVal = eval x s in
                                                                                                              let aenv = bind fDecEnv arg aVal in
                                                                                                                if (eval fbody aenv) = Bool true
                                                                                                                 then check xs
                                                                                                                    else Bool false
                                                                                               in check l           
                                                   | (_, _) -> failwith "Run-time error")
                          | (_, _) -> failwith "Run-time error")
  | Exists (p, s0) -> let es = eval s0 s in
                        (match (typecheck ("set", es), es) with
                         | (true, Set (t, l)) -> (match (pred_check (eval p s, t), p) with
                                                  | (true, Closure (arg, fbody, fDecEnv)) -> let rec check ls =
                                                                                               match ls with
                                                                                               | [] -> Bool false
                                                                                               | x :: xs -> let aVal = eval x s in
                                                                                                              let aenv = bind fDecEnv arg aVal in
                                                                                                                if (eval fbody aenv) = Bool true
                                                                                                                 then Bool true 
                                                                                                                    else check xs
                                                                                               in check l           
                                                  | (_, _) -> failwith "Run-time error")
                         | (_, _) -> failwith "Run-time error")
  | Filter (p, s0) -> let es = eval s0 s in
                        (match (typecheck ("set", es), es) with
                         | (true, Set (t, l)) -> (match (pred_check (eval p s, t), p) with
                                                  | (true, Closure (arg, fbody, fDecEnv)) -> let rec create_set ls =
                                                                                               match ls with
                                                                                               | [] -> set_empty t
                                                                                               | x :: xs -> let aVal = eval x s in
                                                                                                              let aenv = bind fDecEnv arg aVal in
                                                                                                                if (eval fbody aenv) = Bool true
                                                                                                                 then add (create_set xs, x)
                                                                                                                    else create_set xs
                                                                                               in create_set l           
                                                  | (_, _) -> failwith "Run-time error")
                         | (_, _) -> failwith "Run-time error")
  | Map (f, s0) -> let es = eval s0 s in
                     (match (typecheck ("set", es), es) with
                      | (true, Set (t, l)) -> (match (fun_check (eval f s, t), f) with
                                               | (type_res, Closure (arg, fbody, fDecEnv)) -> let rec create_set ls =
                                                                                                match ls with
                                                                                                | [] -> set_empty type_res
                                                                                                | x :: xs -> let aVal = eval x s in
                                                                                                               let aenv = bind fDecEnv arg aVal in
                                                                                                                 add (create_set xs, (eval fbody aenv))
                                                                                                in create_set l
                                               | (_, _) -> failwith "Run-time error")
                      | (_, _) -> failwith "Run-time error")
