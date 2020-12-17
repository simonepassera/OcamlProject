(* The language *)

type tval =
| Tint
| Tstring
| Tbool
| Tfun of tval * tval
| Trecfun of ide * tval * tval
| Tset of tval
| Unbound
and ide = string

type tenv = ide -> tval ;;

let emptyTenv = fun (x:ide) -> Unbound ;;

let lookup (e:tenv) (i:ide) = e i ;;

let bind (e:tenv) (i:ide) (v:tval) = fun x -> if x = i then v else lookup e x ;;

let type_elts_check t =
  match t with
  | "int" -> Tint
  | "string" -> Tstring
  | "bool" -> Tbool
  | _ -> failwith "Not a valid type for elements of set" ;;

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
               then Tset t
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
                                                 (match (t1, t2) with
                                                  | (Tint, Tint) -> Tint
                                                  | (Tbool, Tbool) -> Tbool
                                                  | (Tstring, Tstring) -> Tstring
                                                  | (_, _) -> failwith "Wrong type")
                                  | _ -> failwith "Wrong type")
  | Den i -> lookup s i
  | Let (i, e, ebody) -> teval ebody (bind s i (teval e s))
  | Fun (arg, targ, ebody) -> let env = bind s arg targ in
                                let tres = teval ebody env in
                                  Tfun (targ, tres)
  | Letrec (f, arg, targ, fBody, tres, letBody) -> let renv = bind s f (Trecfun (f, targ, tres)) in
                                                     let env = bind renv arg targ in
                                                       if (teval fBody env) = tres
                                                        then teval letBody (bind s f (Trecfun (f, targ, tres)))
                                                           else failwith "Wrong type"
  | Apply (eF, eArg) -> let f = teval eF s in
                          (match f with
                           | Tfun (targ, tres) -> if (teval eArg s) = targ
                                                   then tres
                                                      else failwith "Wrong type"
                           | Trecfun (f, targ, tres) -> if (teval eArg s) = targ
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
                    | (Tfun (targ, tres), Tset t) -> if targ <> t
                                                      then failwith "Wrong type"
                                                         else Tset tres
                    | (_, _) -> failwith "Wrong type")
