(* The language *)

type ide = string ;;

type type_elts = string ;;

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
| SetOf of type_elts * (exp list)
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
| Map of exp * exp ;;

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
  | _ -> failwith "Not a valid type" ;;

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
  | SetEmpty t -> (match t with
                   | "int" -> Set (t, [])
                   | "string" -> Set (t, [])
                   | _ -> failwith "Not a valid type for elements of set")
  | SetSingleton (t, elt) -> (match t with
                              | "int" -> let r = eval elt s in
                                           (match (typecheck (t, r), r) with
                                            | (true, Int i) -> Set (t, [r])
                                            | (_, _) -> failwith "Run-time error")
                              | "string" -> let r = eval elt s in
                                              (match (typecheck (t, r), r) with
                                               | (true, String s) -> Set (t, [r])
                                               | (_, _) -> failwith "Run-time error")
                              | _ -> failwith "Not a valid type for elements of set")
  | SetOf (t, l) -> (match t with
                     | "int" -> if l = []
                     			 then failwith "Run-time error"
                     			    else let rec f ls = (match ls with
                                                   | [] -> []
                                                   | x :: xs -> let r = eval x s in (match (typecheck (t, r), r) with
                                                                                     | (true, Int i) -> r :: f xs
                                                                                     | (_, _) -> failwith "Run-time error"))
                                         in Set (t, f l)
                     | "string" -> if l = []
                                    then failwith "Run-time error"
                                       else let rec f ls = (match ls with
                                                            | [] -> []
                                                            | x :: xs -> let r = eval x s in (match (typecheck (t, r), r) with
                                                                                              | (true, String s) -> r :: f xs
                                                                                              | (_, _) -> failwith "Run-time error"))
                                                  in Set (t, f l)
                     | _ -> failwith "Not a valid type for elements of set")
  | Union (s1, s2) -> Unbound
  | Inter (s1, s2) -> Unbound
  | Diff (s1, s2) -> Unbound
  | Add (s0, elt) -> Unbound
  | Remove (s0, elt) -> Unbound
  | IsEmpty s0 -> Unbound
  | Contains (s0, elt) -> Unbound
  | Subset (s1, s2) -> Unbound
  | MinElt s0 -> Unbound
  | MaxElt s0 -> Unbound
  | For_all (p, s0) -> Unbound
  | Exists (p, s0) -> Unbound
  | Filter (p, s0) -> Unbound
  | Map (f, s0) -> Unbound
