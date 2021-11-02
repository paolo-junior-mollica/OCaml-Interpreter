(* Sintassi astratta *)
type ide = string;;

type exp = 
        |   CstInt of int
        |   CstTrue
        |   CstFalse
        |   CstStr of ide
        |   Den of ide
        |   Equals of exp * exp
        |   Minor of exp * exp
        |   Greater of exp * exp
        |   Minoreq of exp * exp
        |   Greatereq of exp * exp
        |   Sum of exp * exp
        |   Diff of exp * exp
        |   Times of exp * exp
        |   Div of exp * exp
        |   Mod of exp * exp
        |   And of exp * exp
        |   Or of exp * exp
        |   Not of exp
        |   Minus of exp
        |   Ifthenelse of exp * exp * exp           
        |   Let of ide * exp * exp                  
        |   Letrec of ide * ide * exp * exp         
        |   Fun of ide * exp                        
        |   Apply of exp * exp                      
        |   Dict of dictionary  (* espressione costituita da un dizionario *)
        |   Get of exp * ide    (* dati un dizionario ed una chiave, restituisce il valore associato a quest'ultima *)
        |   Add of exp * ide * exp  (* inserisce la coppia chiave-valore al dizionario *)
        |   Remove of exp * ide (* rimuove la chiave e il valore associato a questa dal dizionario *)
        |   Clear of exp    (* restituisce un dizionario vuoto *)
        |   ApplyOver of exp * exp  (* applica una funzione ad ogni valore nel dizionario *)

and dictionary = Empty | Item of (ide * exp) * dictionary;;  (* tipo dizionario *)


(* Ambiente *)
type 't env = (ide * 't) list;; 


(* Tipi esprimibili *)
type evT = 
        |   Unbound
        |   Int of int
        |   Bool of bool
        |   String of string
        |   Closure of ide * exp * evT env 
        |   RecClosure of ide * ide * exp * evT env 
        |   DynFun of ide * exp
        |   RecDynFun of ide * ide * exp  
        |   Dictionary of (ide * evT) list;; (* tipo esprimibile per un dizionario *)


(* continuiamo con l'ambiente *)
let emptyEnv = [];;
let bind (r : 't env) (i : ide) (v : evT) = (i, v)::r;;

let rec lookup (r : 't env) (i : ide) =
    match r with
    |   [] -> Unbound
    |   (nome, valore)::tail when nome = i -> valore
    |   _::tail -> lookup tail i;;

(* Supporto a RunTime *)

(* Controllo dei tipi *)
let typecheck (s : string) (v : evT) : bool = 
    match s with
    |   "int" -> (match v with
                    Int n -> true
                  | _ -> false )
    |   "bool" -> (match v with
                    Bool p -> true
                  | _ -> false )
    |   "dictionary" -> ( match v with      (* controllo per il tipo dizionario *)
                          Dictionary d -> true
                        | _ -> false )
    |   _ -> failwith ("Type error");;

(* Eccezioni *)
exception GenericError of string;;
exception KeyNotFound;;
exception ExistingKey of string;;

(* Funzioni ausiliarie per eval / rt_eval *)

let et x y = 
    if typecheck "bool" x && typecheck "bool" y
    then (
            match (x, y) with
            |   (Bool n, Bool u) -> Bool(n && u)
            |   (_,_) -> raise (GenericError "et function")
    )
    else failwith("Type error");;

let times x y =
    if typecheck "int" x && typecheck "int" y 
    then (
            match (x, y) with
            |   (Int n, Int u) -> Int(n * u)
            |   (_,_) -> raise (GenericError "prod function")
    )
    else failwith("Type error");;

let div x y =
    if typecheck "int" x && typecheck "int" y 
    then (
            match (x, y) with
            |   (Int n, Int u) -> if u = 0 then failwith ("Division by zero")
                               else Int(n / u)
            |   (_,_) -> raise (GenericError "div function")
    )
    else failwith("Type error");;

let modulo x y =
    if typecheck "int" x && typecheck "int" y 
    then (
            match (x, y) with
            |   (Int n, Int u) -> if u = 0 then failwith ("Division by zero")
                                  else Int(n mod u)
            |   (_,_) -> raise (GenericError "div function")
    )
    else failwith("Type error");;

let sum x y =
    if typecheck "int" x && typecheck "int" y 
    then (
            match (x, y) with
            |   (Int n, Int u) -> Int(n + u)
            |   (_,_) -> raise (GenericError "sum function") 
    )
    else failwith("Type error");;

let diff x y =
    if typecheck "int" x && typecheck "int" y 
    then (
            match (x, y) with
            |   (Int n, Int u) -> if n > u then Int(n - u)
                                  else Int(u - n)
            |   (_,_) -> raise (GenericError "diff function")
    )
    else failwith("Type error");;

let equals x y = 
    if typecheck "int" x && typecheck "int" y
    then (
            match (x, y) with
            |   (Int n, Int u) -> Bool(n = u)
            |   (_,_) -> raise (GenericError "eq function")
    )
    else failwith("Type error");;

let minoreq x y = 
    if typecheck "int" x && typecheck "int" y
    then (
            match (x, y) with
            |   (Int n, Int u) -> Bool(n <= u)
            |   (_,_) -> raise (GenericError "minoreq function")
    )
    else failwith("Type error");;

let minor x y = 
    if typecheck "int" x && typecheck "int" y
    then (
            match (x, y) with
            |   (Int n, Int u) -> Bool(n < u)
            |   (_,_) -> raise (GenericError "minor function")
    )
    else failwith("Type error");;

let greatereq x y = 
    if typecheck "int" x && typecheck "int" y
    then (
            match (x, y) with
            |   (Int n, Int u) -> Bool(n >= u)
            |   (_,_) -> raise (GenericError "majoreq function")
    )
    else failwith("Type error");;

let greater x y = 
    if typecheck "int" x && typecheck "int" y
    then (
            match (x, y) with
            |  (Int n, Int u) -> Bool(n > u)
            |   (_,_) -> raise (GenericError "major function")
    )
    else failwith("Type error");;

let vel x y = 
    if typecheck "bool" x && typecheck "bool" y
    then (
            match (x, y) with
            |   (Bool n, Bool u) -> Bool(n || u)
            |   (_,_) -> raise (GenericError "vel function")
    )
    else failwith("Type error");;

let non x = 
    if typecheck "bool" x = true 
    then (
            match x with
            |  Bool true -> Bool false
            |  Bool false -> Bool true
            |  _ -> raise (GenericError "non function")
    )
    else failwith ("Type error");;

let minus x =
    if typecheck "int" x = true
    then (
            match x with   
            |   Int n -> Int(-n)
            |   _ -> raise (GenericError "minus function")
    )
    else failwith ("Type error");;

(* Conta le occorrenze di una chiave *)
let rec contaOcc dict key = 
    match dict with
    |   Empty -> 0
    |   Item ((k, v), tail) -> if k = key 
                               then 1 + contaOcc tail key
                               else contaOcc tail key;;

(* restituisce il valore associato alla chiave se esiste, altrimenti lancia un'eccezione *)
let rec get dict key =
    match dict with
    |   [] -> raise KeyNotFound
    |   (k, v)::tail -> if k = key
                        then v
                        else get tail key;;

(* aggiunge la coppia key-value al dizionario se key non è già presente, altrimenti lancia un'eccezione *)
let rec add dict key value =
    match dict with
    |   [] -> (key, value)::[]
    |   (k, v)::tail -> if k = key
                        then raise (ExistingKey "Key already in the dictionary")
                        else (k, v)::(add tail key value);;

(* rimuove la chiave e il rispettivo valore se esiste, altrimenti lancia un'eccezione *)
let rec remove dict key =
    match dict with
    |   [] -> raise KeyNotFound
    |   (k, v)::tail -> if k = key
                        then tail
                        else (k, v)::(remove tail key);;
    

(* L'interprete con regola di scoping statico *)
let rec eval (e: exp) (r: 't env) : evT = 
    match e with
    |   CstInt n -> Int n
    |   CstTrue -> Bool true
    |   CstFalse -> Bool false
    |   CstStr s -> String s
    |   Den i -> lookup r i
    |   Minoreq (a, b) -> minoreq (eval a r) (eval b r)
    |   Minor (a, b) -> minor (eval a r) (eval b r)
    |   Greatereq (a, b) -> greatereq (eval a r) (eval b r)
    |   Greater (a, b) -> greater (eval a r) (eval b r)
    |   Times (a, b) -> times (eval a r) (eval b r)
    |   Div (a, b) -> div (eval a r) (eval b r)
    |   Mod (a, b) -> modulo (eval a r) (eval b r)
    |   Sum (a, b) -> sum (eval a r) (eval b r)
    |   Diff (a, b) -> diff (eval a r) (eval b r)
    |   Minus a -> minus (eval a r)
    |   And (a, b) -> et (eval a r) (eval b r) 
    |   Or (a, b) -> vel (eval a r) (eval b r)
    |   Not a -> non (eval a r)
    |   Equals (a, b) -> equals (eval a r) (eval b r)
    |   Ifthenelse (guard, thEn, eLse) ->
            let guardia = eval guard r in 
                if typecheck "bool" guardia = true
                then
                    match guardia with
                    |   Bool true -> eval thEn r
                    |   Bool false -> eval eLse r
                    |   _ -> raise (GenericError "Unexpected") 
                else failwith ("Non boolean guard")
    |   Let (i, e1, e2) -> eval (e2) (bind r i (eval e1 r))
    |   Letrec (f, param, fbody, lbody) -> 
            let bEnv = bind r f (RecClosure (f, param, fbody, r)) in 
                eval lbody bEnv
    |   Fun (param, fbody) -> Closure (param, fbody, r) 
    |   Apply (eF, eArg) -> 
            let fclosure = eval eF r in (
                match fclosure with
                |   Closure (arg, fbody, fDecEnv) -> 
                        let aVal = eval eArg r in 
                            let aEnv = bind fDecEnv arg aVal in 
                                eval fbody aEnv 
                |   RecClosure (f, arg, fbody, fDecEnv) -> 
                        let aVal = eval eArg r in 
                            let rEnv = bind fDecEnv f fclosure in 
                                let aEnv = bind rEnv arg aVal in 
                                    eval fbody aEnv
                |   _ -> failwith ("Non functional value")
            )
    |   Dict dict -> Dictionary (applyEval dict r)  (* il tipo esprimibile Dictionary si ottiene applicando la eval ad ogni 
                                                            valore nel dizionario *)
    |   Get (dict, key) -> (   (* valuta l'espressione Get restituendo il valore esprimibile associato a key *)
            let eD = eval dict r in 
                if typecheck "dictionary" eD then 
                    match eD with
                    |   Dictionary d -> get d key
                    |   _ -> raise (GenericError "eval function")
                else failwith ("Type error")
        )
    |   Add (dict, key, value) -> Dictionary (  (* valuta Add aggiungendo la coppia key-value e restituendo un Dictionary *)
            let eD = eval dict r in 
                if typecheck "dictionary" eD then 
                    match eD with
                    |   Dictionary d -> add d key (eval value r)
                    |   _ -> raise (GenericError "eval function")
                else failwith ("Type error")
        )
    |   Remove (dict, key) -> Dictionary (  (* valuta Remove rimuovendo key e il suo valore associato e restituendo un Dictionary *)
            let eD = eval dict r in 
                if typecheck "dictionary" eD then 
                    match eD with
                    |   Dictionary d -> remove d key 
                    |   _ -> raise (GenericError "eval function")
                else failwith ("Type error")
        )
    |   Clear dict -> ( (* valuta Clear restituendo un Dictionary vuoto *)
            let eD = eval dict r in 
                if typecheck "dictionary" eD then 
                    match eD with
                    |   Dictionary d -> Dictionary ([])
                    |   _ -> raise (GenericError "eval function")
                else failwith ("Type error")
        )
    |   ApplyOver (f, dict) -> Dictionary ( (* valuta ApplyOver restituendo un Dictionary nel quale f è stata applicata ad ogni
                                                valore nel dizionario *)
            let eD = eval dict r in 
                if typecheck "dictionary" eD then 
                    match eD with
                    |   Dictionary d -> (
                            match eval f r with
                            |   Closure (arg, fbody, fDecEnv) -> applyOver f d r
                            |   RecClosure (fn, arg, fbody, fDecEnv) -> applyOver f d r
                            |   _ -> failwith ("Non functional value")
                        )
                    |   _ -> raise (GenericError "eval function")
                else failwith ("Type error")
        )

    and applyEval dict r =  (* funzione utilizzata per applicare la eval ad ogni elemento del dizionario *)
    match dict with
    |   Empty -> []
    |   Item((k, v), tail) -> if contaOcc dict k = 1
                              then (k, eval v r)::(applyEval tail r)
                              else failwith ("Il dizionario non può avere chiavi doppioni")

    and applyOver f d r = (* chiama applica su ogni valore del dizionario *)
        match d with
            |   [] -> []
            |   (k, v)::tail -> (k, applica f v r)::(applyOver f tail r)

    and applica f v r = (* applica la funzione f a v  *)
        match eval f r with
        |   Closure (arg, fbody, fDecEnv) -> (
                let aEnv = bind fDecEnv arg v in 
                        eval fbody aEnv 
            ) 
        |   RecClosure (fn, arg, fbody, fDecEnv) -> (
                let rEnv = bind fDecEnv fn (eval f r) in 
                    let aEnv = bind rEnv arg v in 
                        eval fbody aEnv
            )
        |   _ -> failwith ("Non functional value")

    ;;

(* L'interprete con regola di scoping dinamico *)
let rec rt_eval (e : exp) (r : 't env): evT = 
    match e with
    |   CstInt n -> Int n
    |   CstTrue -> Bool true
    |   CstFalse -> Bool false
    |   CstStr s -> String s
    |   Den i -> lookup r i
    |   Minoreq (a, b) -> minoreq (rt_eval a r) (rt_eval b r)
    |   Minor (a, b) -> minor (rt_eval a r) (rt_eval b r)
    |   Greatereq (a, b) -> greatereq (rt_eval a r) (rt_eval b r)
    |   Greater (a, b) -> greater (rt_eval a r) (rt_eval b r)
    |   Times (a, b) -> times (rt_eval a r) (rt_eval b r)
    |   Div (a, b) -> div (rt_eval a r) (rt_eval b r)
    |   Mod (a, b) -> modulo (rt_eval a r) (rt_eval b r)
    |   Sum (a, b) -> sum (rt_eval a r) (rt_eval b r)
    |   Diff (a, b) -> diff (rt_eval a r) (rt_eval b r)
    |   Minus a -> minus (rt_eval a r)
    |   And (a, b) -> et (rt_eval a r) (rt_eval b r) 
    |   Or (a, b) -> vel (rt_eval a r) (rt_eval b r)
    |   Not a -> non (rt_eval a r)
    |   Equals (a, b) -> equals (rt_eval a r) (rt_eval b r)
    |   Ifthenelse (guard, thEn, eLse) ->
            let guardia = rt_eval guard r in 
                if typecheck "bool" guardia = true
                then
                    match guardia with
                    |   Bool true -> rt_eval thEn r
                    |   Bool false -> rt_eval eLse r
                    |   _ -> raise (GenericError "Unexpected") 
                else failwith ("Non boolean guard")
    |   Let (i, e1, e2) -> rt_eval (e2) (bind r i (rt_eval e1 r))
    |   Letrec (f, param, fbody, lbody) -> 
            let bEnv = bind r f (RecDynFun (f,param,fbody)) in 
                rt_eval lbody bEnv
    |   Fun (param, fbody) -> DynFun (param, fbody) 
    |   Apply (eF, eArg) -> 
            let fval = rt_eval eF r in (
                match fval with
                |   DynFun (arg, fbody) -> (* Con lo scope dinamico, si usa r invece di fDecEnv *)
                        let aVal = rt_eval eArg r in 
                            let aEnv = bind r arg aVal in 
                                rt_eval fbody aEnv 
                |   RecDynFun (f, arg, fbody) -> (* Con lo scope dinamico, si usa r invece di fDecEnv *)
                        let aVal = rt_eval eArg r in 
                            let rEnv = bind r f fval in 
                                let aEnv = bind rEnv arg aVal in 
                                    rt_eval fbody aEnv
                |   _ -> failwith ("Non functional value")
            )
    |   Dict dict -> Dictionary (applyEval dict r)  (* il tipo esprimibile Dictionary si ottiene applicando rt_eval ad ogni 
                                                            valore nel dizionario *)
    |   Get (dict, key) -> (    (* valuta l'espressione Get restituendo il valore esprimibile associato a key *)
            let eD = rt_eval dict r in 
                if typecheck "dictionary" eD then 
                    match eD with
                    |   Dictionary d -> get d key
                    |   _ -> raise (GenericError "rt_eval function")
                else failwith ("Type error")
        )
    |   Add (dict, key, value) -> Dictionary (  (* valuta Add aggiungendo la coppia key-value e restituendo un Dictionary *)
            let eD = rt_eval dict r in 
                if typecheck "dictionary" eD then 
                    match eD with
                    |   Dictionary d -> add d key (rt_eval value r)
                    |   _ -> raise (GenericError "rt_eval function")
                else failwith ("Type error")
        )
    |   Remove (dict, key) -> Dictionary (  (* valuta Remove rimuovendo key e il suo valore associato e restituendo un Dictionary *)
            let eD = rt_eval dict r in 
                if typecheck "dictionary" eD then 
                    match eD with
                    |   Dictionary d -> remove d key 
                    |   _ -> raise (GenericError "rt_eval function")
                else failwith ("Type error")
        )
    |   Clear dict -> (     (* valuta Clear restituendo un Dictionary vuoto *)
            let eD = rt_eval dict r in 
                if typecheck "dictionary" eD then 
                    match eD with
                    |   Dictionary d -> Dictionary ([])
                    |   _ -> raise (GenericError "rt_eval function")
                else failwith ("Type error")
        )
    |   ApplyOver (f, dict) -> Dictionary ( (* valuta ApplyOver restituendo un Dictionary nel quale f è stata applicata ad ogni
                                                valore nel dizionario *)
            let eD = rt_eval dict r in 
                if typecheck "dictionary" eD then 
                    match eD with
                    |   Dictionary d -> (
                            match rt_eval f r with
                            |   DynFun (arg, fbody) -> applyOver f d r
                            |   RecDynFun (fn, arg, fbody) -> applyOver f d r
                            |   _ -> failwith ("Non functional value")
                        )
                    |   _ -> raise (GenericError "rt_eval function")
                else failwith ("Type error")
        )

    and applyEval dict r =  (* funzione utilizzata per applicare la rt_eval ad ogni elemento del dizionario *)
        match dict with
        |   Empty -> []
        |   Item((k, v), tail) -> if contaOcc dict k = 1
                                  then (k, rt_eval v r)::(applyEval tail r)
                                  else failwith ("Il dizionario non può avere chiavi doppioni")

    and applyOver f d r =   (* chiama applica su ogni valore del dizionario *)
        match d with
            |   [] -> []
            |   (k, v)::tail -> (k, applica f v r)::(applyOver f tail r)

    and applica f v r =     (* applica la funzione f a v  *)
        match rt_eval f r with
        |   DynFun (arg, fbody) -> (  (* Con lo scope dinamico, si usa r invece di fDecEnv *)
                let aEnv = bind r arg v in 
                        rt_eval fbody aEnv 
            ) 
        |   RecDynFun (fn, arg, fbody) -> (   (* Con lo scope dinamico, si usa r invece di fDecEnv *)
                let rEnv = bind r fn (rt_eval f r) in 
                    let aEnv = bind rEnv arg v in 
                        rt_eval fbody aEnv
            )
        |   _ -> failwith ("Non functional value")

    ;;

(* ==================================== TEST ==================================== *)

(* crea un dizionario con chiavi doppioni, e quindi lancia un'eccezione *)
let e0 = Dict(Item(("uno", CstInt 1), Item(("due", CstInt 2), Item(("tre", CstInt 3), Item(("due", CstInt 4), Empty)))));;

(* crea un dizionario *)
let e1 = Dict(Item(("uno", CstInt 1), Item(("due", CstInt 2), Item(("tre", CstInt 3), Item(("quattro", CstInt 4), Empty)))));;

(* ritorna il valore associato alla chiave "tre" *)
let e2 = Get(e1, "tre");;

(* aggiunge la coppia ("cinque", 5) al dizionario *)
let e3 = Add(e1, "cinque", CstInt 5);;

(* aggiunge la coppia ("sei", 6) al dizionario. È chiamata su e3 *)
let e4 = Add(e3, "sei", Sum(CstInt 2, CstInt 4));;

(* rimuove la chiave "tre" e il valore associato ad esso. Chiamata su e4 *)
let e5 = Remove(e4, "tre");;

(* restituisce un dizionario vuoto *)
let e6 = Clear(e3);;

(* applica la funzione x -> x + 3 ad ogni elemento del dizionario. Chiamata su e4 *)
let e7 = ApplyOver(Fun("x", Sum(Den "x", CstInt 3)), e4);; 

(* test per la correttezza della eval con regola di scoping dinamico *)
let e8 = Let("x", CstInt 1, Let("f", Fun("y", Den "x"), Let("x", CstInt 2, Apply (Den "f", CstInt 0))));;

(* let e8 = 
    let x = 1 in
        let f = fun y -> x in
            let x = 2 in f 0;; 
se si usa le regole di scoping statico il risultato è 1, altrimenti è 2 *)