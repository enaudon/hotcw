(*
  Simple Hindley-Milner type checker for pure lambda-calculus with let

  Explanation of the efficient generalization -- Remy algorithm

  The sound and efficient generalization with _eagerly_ computed levels
*)

(* The language: lambda-calculus with let *)
type varname = string

type exp = 
  | Var of varname                      (* variable                *)
  | App of exp * exp                    (* application: e1 e2      *)
  | Lam of varname * exp                (* abstraction: fun x -> e *)
  | Let of varname * exp * exp          (* let x = e in e2         *)
;;

(* The types to infer *)
(* Types without QVar (quantified variables) are simple types;
   those containing QVar are type schemas.
   Since quantifiers are always on the outside in the HM system, 
   they are implied and not explicitly represented.
*)
type qname = string
type level = int
type typ = 
  | TVar of tv ref               (* type (schematic) variable *)
  | QVar of qname                (* quantified type variable *)
  | TArrow of typ * typ
and tv = Unbound of string * level | Link of typ
;;

let gensym_counter = ref 0
let reset_gensym : unit -> unit =
  fun () -> gensym_counter := 0
;;

let gensym : unit -> string = fun () ->
  let n = !gensym_counter in
  let () = incr gensym_counter in
  if n < 26 then String.make 1 (Char.chr (Char.code 'a' + n))
            else "t" ^ string_of_int n
;;

(* Determining the |let|-nesting level during the type-checking, 
   or just the _level_.
   Each top-level expression to type-check is implicitly wrapped into a let.
   So, the numbering starts with 1.
*)
let current_level = ref 1
let reset_level () = current_level := 1

let reset_type_variables () =       (* name from OCaml's typing/typetext.ml *)
  reset_gensym ();
  reset_level ()

(* Increase level *)
let enter_level () =
  incr current_level
(* Restore level *)
let leave_level () =
  decr current_level


(* Make a fresh type variable *)
let newvar : unit -> typ =
 fun () -> TVar (ref (Unbound (gensym (),!current_level)))
;;

(* check to see if a TVar (the first argument) occurs in the type
   given as the second argument. Fail if it does.
   At the same time, update the levels of all encountered free
   variables to be the min of variable's current level and
   the level of the given variable tvr.
*)
let rec occurs : tv ref -> typ -> unit = fun tvr -> function
  | TVar tvr' when tvr == tvr' -> failwith "occurs check"
  | TVar ({contents = Unbound (name,l')} as tv) ->
      let min_level = 
        (match !tvr with Unbound (_,l) -> min l l' | _ -> l') in
      tv := Unbound (name,min_level)
  | TVar {contents = Link ty} -> occurs tvr ty
  | TArrow (t1,t2) -> occurs tvr t1; occurs tvr t2
  | _ -> ()
;;

(* Simplistic.  No path compression *)
(* Also, QVar are unexpected: they should've been instantiated *)
let rec unify : typ -> typ -> unit = fun t1 t2 ->
  if t1 == t2 then ()                   (* t1 and t2 are physically the same *)
  else match (t1,t2) with
  | (TVar ({contents = Unbound _} as tv),t')
  | (t',TVar ({contents = Unbound _} as tv)) -> occurs tv t'; tv := Link t'
  | (TVar {contents = Link t1},t2)
  | (t1,TVar {contents = Link t2}) -> unify t1 t2
  | (TArrow (tyl1,tyl2), TArrow (tyr1,tyr2)) ->
      unify tyl1 tyr1;
      unify tyl2 tyr2
  (* everything else is error *)
;;

(* The type environment *)
type env = (varname * typ) list
;;

(* Sound generalization: generalize (convert to QVar) 
   only those free TVar whose level is greater than the current.
   These TVar correspond to dead regions.
*)
let rec gen : typ -> typ = function
  | TVar {contents = Unbound (name,l)} 
      when l > !current_level -> QVar name
  | TVar {contents = Link ty} -> gen ty
  | TArrow (ty1,ty2) -> TArrow (gen ty1, gen ty2)
  | ty -> ty
;;

(* instantiation: replace schematic variables with fresh TVar
*)
let inst : typ -> typ = 
  let rec loop subst = function
    | QVar name -> 
        begin
          try (List.assoc name subst, subst)
          with Not_found ->
            let tv = newvar () in
            (tv, (name,tv)::subst)
        end
    | TVar {contents = Link ty} -> loop subst ty
    | TArrow (ty1,ty2) -> 
        let (ty1,subst) = loop subst ty1 in
        let (ty2,subst) = loop subst ty2 in
        (TArrow (ty1,ty2), subst)
    | ty -> (ty, subst)
  in fun ty -> fst (loop [] ty)
;;


(* Trivial type checker. Type checking errors are delivered
   as exceptions
*)
let rec typeof : env -> exp -> typ = fun env -> function
  | Var x     -> inst (List.assoc x env)
  | Lam (x,e) -> 
      let ty_x = newvar () in
      let ty_e = typeof ((x,ty_x)::env) e in
      TArrow(ty_x,ty_e)
  | App (e1,e2) ->
      let ty_fun = typeof env e1 in
      let ty_arg = typeof env e2 in
      let ty_res = newvar () in
      unify ty_fun (TArrow (ty_arg,ty_res));
      ty_res
  | Let (x,e,e2) -> 
      enter_level ();
      let ty_e = typeof env e in
      leave_level ();
      typeof ((x,gen ty_e)::env) e2
;;

let id = Lam("x",Var"x");;
let c1 = Lam("x",Lam("y",App (Var"x",Var"y")));;

let 
 TArrow (TVar {contents = Unbound ("a", 1)},
         TVar {contents = Unbound ("a", 1)})
   = reset_type_variables ();
     typeof [] id
;;

let 
 TArrow
 (TVar
   {contents =
     Link
      (TArrow (TVar {contents = Unbound ("b", 1)},
        TVar {contents = Unbound ("c", 1)}))},
 TArrow (TVar {contents = Unbound ("b", 1)},
  TVar {contents = Unbound ("c", 1)}))
 =
   reset_type_variables (); 
   typeof [] c1
;;

let 
 TArrow
 (TArrow (TVar {contents = Unbound ("d", 1)},
   TVar {contents = Unbound ("e", 1)}),
 TArrow (TVar {contents = Unbound ("d", 1)},
  TVar {contents = Unbound ("e", 1)}))
 =
 reset_type_variables (); 
 typeof [] (Let ("x",c1,Var"x"));;

let 
TArrow (TVar {contents = Unbound ("b", 1)},
        TVar {contents = Unbound ("b", 1)})
 =
 reset_type_variables (); 
 typeof [] (Let ("y",Lam ("z",Var"z"), Var"y"));;

let
 TArrow (TVar {contents = Unbound ("a", 1)},
  TArrow (TVar {contents = Unbound ("c", 1)},
          TVar {contents = Unbound ("c", 1)}))
 =
 reset_type_variables (); 
 typeof [] (Lam ("x", Let ("y",Lam ("z",Var"z"), Var"y")));;

let
 TArrow (TVar {contents = Unbound ("a", 1)},
  TVar
  {contents =
    Link (TVar {contents = Link (TVar {contents = Unbound ("a", 1)})})})
 =
 reset_type_variables (); 
 typeof [] (Lam ("x", Let ("y",Lam ("z",Var"z"), 
                                    App (Var"y",Var"x"))));;
try 
 reset_type_variables (); 
 typeof [] (Lam ("x",App (Var"x",Var"x")));
 assert false;
 with Failure e -> print_endline e
;;

try 
 reset_type_variables (); 
 typeof [] (Let ("x",Var"x",Var"x"));
 assert false;
 with Not_found -> print_endline "unbound var"
;;

(* id can be `self-applied', on the surface of it *)
let 
 TVar
  {contents =
   Link
    (TVar
      {contents =
        Link
         (TArrow (TVar {contents = Unbound ("c", 1)},
           TVar {contents = Unbound ("c", 1)}))})}
 =
 reset_type_variables (); 
 typeof [] (Let ("id",id, App (Var"id",Var"id")));;

let 
 TArrow (TVar {contents = Unbound ("i", 1)},
         TVar {contents = Unbound ("i", 1)})
 =
 reset_type_variables (); 
 typeof [] (Let ("x",c1,
                    Let ("y",
                          Let ("z",App(Var"x",id), Var "z"),
                         Var"y")));;

(*
fun x -> fun y -> let x = x y in fun x -> y x;;
- : (('a -> 'b) -> 'c) -> ('a -> 'b) -> 'a -> 'b = <fun>
*)
let 
 TArrow
  (TVar
   {contents =
     Link
      (TArrow
        (TVar
          {contents =
            Link
             (TArrow (TVar {contents = Unbound ("d", 1)},
               TVar {contents = Unbound ("e", 1)}))},
        TVar {contents = Unbound ("c", 1)}))},
  TArrow
  (TVar
    {contents =
      Link
       (TArrow (TVar {contents = Unbound ("d", 1)},
         TVar {contents = Unbound ("e", 1)}))},
   TArrow (TVar {contents = Unbound ("d", 1)},
   TVar {contents = Unbound ("e", 1)})))
 =
 reset_type_variables (); 
 typeof [] (Lam ("x", Lam("y",Let ("x",App (Var"x",Var"y"),
                                  Lam ("x",App (Var"y",Var"x"))))));;

(* now sound generalization ! *)
let
TArrow (TVar {contents = Unbound ("a", 1)},
        TVar {contents = Unbound ("a", 1)})
 =
 reset_type_variables (); 
 typeof [] (Lam ("x", Let ("y",Var"x", Var"y")));;

(* now sound generalization ! *)
let 
 TArrow (TVar {contents = Unbound ("a", 1)},
  TArrow (TVar {contents = Unbound ("c", 1)},
          TVar {contents = Unbound ("a", 1)}))
 =
 reset_type_variables (); 
 typeof [] (Lam ("x", Let ("y",Lam ("z",Var"x"), Var"y")));;

(* now sound generalization ! *)
let
 TArrow
  (TVar
   {contents =
     Link
      (TArrow (TVar {contents = Unbound ("b", 1)},
        TVar {contents = Unbound ("c", 1)}))},
  TArrow (TVar {contents = Unbound ("b", 1)},
   TVar {contents = Unbound ("c", 1)}))
 =
 reset_type_variables (); 
 typeof [] (Lam ("x", Let ("y",Lam ("z",App (Var"x",Var"z")), Var"y")));;


(* now sound generalization ! *)
let 
 TArrow
  (TVar
   {contents =
     Link
      (TArrow (TVar {contents = Unbound ("b", 1)},
        TVar
         {contents =
           Link
            (TArrow (TVar {contents = Unbound ("b", 1)},
              TVar {contents = Unbound ("d", 1)}))}))},
  TArrow (TVar {contents = Unbound ("b", 1)},
          TVar {contents = Unbound ("d", 1)}))
 =
 reset_type_variables (); 
 typeof [] (Lam ("x", Lam("y",Let ("x",App (Var"x",Var"y"),
                                    App (Var"x",Var"y")))));;



(* now sound generalization ! *)
try 
 reset_type_variables (); 
 typeof [] (Lam ("x",Let("y",Var"x", App (Var"y",Var"y"))));
 assert false;
 with Failure e -> print_endline e
;;

(* now sound generalization ! *)
(* fun x -> let y = let z = x (fun x -> x) in z in y;;
   - : (('a -> 'a) -> 'b) -> 'b = <fun>
*)
let
 TArrow
 (TVar
   {contents =
     Link
      (TArrow
        (TArrow (TVar {contents = Unbound ("b", 1)},
          TVar {contents = Unbound ("b", 1)}),
        TVar {contents = Unbound ("c", 1)}))},
  TVar {contents = Unbound ("c", 1)})
 =
 reset_gensym (); 
 typeof [] (Lam ("x",
                    Let ("y",
                          Let ("z",App(Var"x",id), Var "z"),
                          Var"y")));;


print_endline "\nAll Done\n";;
