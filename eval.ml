(* The language *)

type ide = string ;;

type exp =
| CstInt of int
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
| Apply of exp * exp ;;

type 'v env = string -> 'v ;;

type evT =
| Int of int
| Bool of bool
| Closure of ide * exp * evT env
| RecClosure of ide * ide * exp * evT env
| Unbound ;;

let emptyEnv = fun (x:string) -> Unbound ;;

let lookup (s:evT env) (i:string) = s i ;;

let bind (e:evT env) (s:string) (v:evT) = fun c -> if c = s then v else lookup e c ;;

let typecheck (x, y) =
  match x with
  | "int" -> (match y with
             | Int u -> true
             | _ -> false)
  | "bool" -> (match y with
              | Bool u -> true
              | _ -> false)
  | _ -> failwith "Not a valid type" ;;

let int_eq (x, y) =
  match (typecheck ("int", x), typecheck ("int", y), x, y) with
  | (true, true, Int v, Int w) -> Bool(v = w)
  | (_,_,_,_) -> failwith "Run-time error" ;;

 let int_plus (x, y) =
   match(typecheck ("int", x), typecheck ("int", y), x, y) with
   | (true, true, Int v, Int w) -> Int (v + w)
   | (_,_,_,_) -> failwith "Run-time error" ;;

let int_sub (x, y) =
  match(typecheck ("int", x), typecheck ("int", y), x, y) with
  | (true, true, Int v, Int w) -> Int (v - w)
  | (_,_,_,_) -> failwith "Run-time error" ;;

let int_times (x, y) =
  match(typecheck ("int", x), typecheck ("int", y), x, y) with
  | (true, true, Int v, Int w) -> Int (v * w)
  | (_,_,_,_) -> failwith "Run-time error" ;;

let rec eval (e:exp) (s:evT env) =
  match e with
  | CstInt n -> Int n
  | CstTrue -> Bool true
  | CstFalse -> Bool false
  | Eq (e1, e2) -> int_eq ((eval e1 s), (eval e2 s))
  | Times (e1, e2) -> int_times ((eval e1 s), (eval e2 s))
  | Sum (e1, e2) -> int_plus ((eval e1 s), (eval e2 s))
  | Sub (e1, e2) -> int_sub ((eval e1 s), (eval e2 s))
  | Ifthenelse (e1, e2, e3) -> let g = eval e1 s in
  								 (match (typecheck("bool", g), g) with
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
                    	  | _ -> failwith "Not functional value") ;;
