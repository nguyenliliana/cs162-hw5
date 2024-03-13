open Base
open Ast
open Vars
exception Type_error of string

(** Raise a type error with the given message *)
let ty_err msg = raise (Type_error msg)

(* Placeholders *)
let part1 () = failwith "TODO: Part 1"
let part2 () = failwith "TODO: Part 2"
let part3 () = failwith "TODO: Part 3"
let parts2and3 () = failwith "TODO: Parts 2 and 3"
let part4 () = failwith "TODO: Part 4"


(**********************************************
  *         Typing Environment (Gamma)        *
  *********************************************)
type gamma = (string * pty) list [@@deriving eq, ord, show]
(** Gamma is the type environment that maps variables to types *)

let uncurry f (x, y) = f x y

(** Pretty-printer for gamma *)
let pp_gamma : gamma Fmt.t =
  let open Fmt in
  let pp_pair = hbox (pair ~sep:(any " : ") string Pretty.pp_pty) in
  vbox
  @@ iter_bindings ~sep:comma (fun f l -> List.iter ~f:(uncurry f) l) pp_pair

let show_gamma : gamma -> string = Fmt.to_to_string pp_gamma

(** Find the type of a variable in gamma *)
let find : gamma -> string -> pty option = List.Assoc.find ~equal:String.equal

(** Add a (var, type) pair to gamma *)
let add : gamma -> string -> pty -> gamma = List.Assoc.add ~equal:String.equal

(*******************************************
 *         Type Equality Constraints       *
 *******************************************)
type cons = ty * ty [@@deriving eq, ord, show]
(** A constraint is a pair (t1,t2) that asserts t1 = t2 *)

(** Pretty-printer for cons *)
let pp_cons : cons Fmt.t =
 fun ppf (t1, t2) -> Fmt.pf ppf "%a == %a" Pretty.pp_ty t1 Pretty.pp_ty t2

(*******************************************
 *         Type Substitution (Sigma)       *
 *******************************************)
type sigma = (string * ty) list [@@deriving eq, ord, show]
(** The solution to a list of type equations is 
   * a substitution [sigma] from type variables to types *)

(** Pretty-printer for sigma *)
let pp_sigma : sigma Fmt.t =
  let open Fmt in
  let pp_pair = hbox (pair ~sep:(any " |-> ") string Pretty.pp_ty) in
  iter_bindings (fun f l -> List.iter ~f:(uncurry f) l) pp_pair

let show_sigma : sigma -> string = Fmt.to_to_string pp_sigma

(** The empty solution *)
let empty : sigma = []

(** Compose the substitution [x |-> t] to the given [sigma] *)
let compose (x : string) (t : ty) (s : sigma) : sigma = (x, t) :: s

(**********************************************
  *            My Helper Funcs                *
  *********************************************)
let rec equal_ty (t1 : ty) (t2 : ty) : bool = 
    match (t1, t2) with
    | (TVar a, TVar b) -> equal (singleton a) (singleton b)
    | (TInt, TInt) -> true
    | (TBool, TBool) -> true
    | (TFun(a1, a2), TFun(b1, b2)) -> (equal_ty a1 b1) && (equal_ty a2 b2) 
    | (TList a, TList b) -> equal_ty a b
    | (TProd(a1, a2), TProd(b1, b2)) -> (equal_ty a1 b1) && (equal_ty a2 b2) 
    | _ -> false

let rec equal_sigma (s1 : sigma) (s2 : sigma) : bool = 
  match s1,s2 with 
  | [],[] -> true
  | (v1, t1)::s1', (v2,t2)::s2' -> 
    if equal_ty t1 t2 then equal_sigma s1' s2' else false
  | _, _ -> false

(*******************************************
 *         Type Inference Utils            *
 *******************************************)
module Utils = struct
  (** Substitute type variable [x] with type [t] in [ty] context [c] *)
  let rec subst (x : string) (t : ty) (c : ty) : ty =
  match c with 
  | TVar s -> if equal (singleton x) (singleton s) then t else c 
  | TInt -> TInt
  | TBool -> TBool
  | TFun (c1, c2) -> TFun((subst x t c1), (subst x t c2))
  | TList c' -> TList (subst x t c')
  | TProd (c1, c2) -> TProd((subst x t c1), (subst x t c2))

  (** Compute the free variable set of an [ty] *)
  let rec free_vars (t : ty) : Vars.t = 
    match t with
    | TVar v -> singleton v
    | TInt -> Vars.empty
    | TBool -> Vars.empty
    | TFun (t1, t2) -> union (free_vars t1) (free_vars t2)
    | TProd (t1, t2)-> union (free_vars t1) (free_vars t2)
    | TList t' -> free_vars t'


  (** Apply a sigma [s] to type [t] by performing all substitutions in [s] *)
  let rec apply_sigma (s : sigma) (t : ty) : ty = (** question: is it ok to add rec keyword**)
    match s with 
    | [] -> t 
    | (x, t')::s' -> apply_sigma s' (subst x t' t)

  (** Relabel bound type variables in increasing (or decreasing) order *)
  let normalize (pass : bool) (t : ty) : ty =
    let xs = free_vars t in
    let s =
      List.mapi
        (Vars.to_list xs |> List.sort ~compare:String.compare)
        ~f:(fun i x ->
          let y = "'t" ^ Int.to_string (if pass then -i - 1 else i + 1) in
          (x, TVar y))
    in
    apply_sigma s t

  let normalize p = p |> normalize true |> normalize false
end

(*******************************************
 *        Type Inference Engine            *  
 *******************************************)
module Infer (Flag : sig
  val polymorphic : bool
  (** flag that enables let-polymorphism *)
end) =
struct
  (***************************************************
   *         Constraint Accumulation Helpers         *
   ***************************************************)
  (** The list of accumulated constraints *)
  let _cs : cons list ref = ref []

  (** Add a constraint to the accumulator. Call it with [t1 === t2]. *)
  let ( === ) (t1 : ty) (t2 : ty) : unit =
    (* If you prefer the "printf" school of debugging, uncomment the following line,
       BUT DON'T FORGET TO REMOVE IT BEFORE YOU SUBMIT *)
    Fmt.epr "[constraint] %a\n%!" pp_cons (t1, t2);
    _cs := (t1, t2) :: !_cs

  (** Return the current list of constraints *)
  let curr_cons_list () : cons list = !_cs

  (******************************************
   *         Fresh Variable Helpers         *
   ******************************************)

  (** Counter to produce fresh variables *)
  let var_counter = ref 1

  (** Type string *)
  let ty_str_of_int (i : int) : string = "'X" ^ Int.to_string i

  (** Return the current var counter and increment it  *)
  let incr () =
    let v = !var_counter in
    var_counter := v + 1;
    v

  (** Generate a fresh string. For internal use only. *)
  let fresh_var_str () : string = ty_str_of_int (incr ())

  (** Generate a fresh [ty] type variable. Call it using [fresh_var ()]. *)
  let fresh_var () : ty = TVar (fresh_var_str ())

  (**************************************************
   *         Generalization/Instantiation           *
   **************************************************)

  (** Generalize a monomorphic type to a polymorphic type *)
  let generalize (gamma : gamma) (t : ty) : pty = part4 ()

  (** Instantiate a polymorphic type by replacing
  * quantified type variables with fresh type variables *)
  let instantiate (t : pty) : ty = part4 ()

  (*******************************************
   *         Constraint Generation           *
   *******************************************)

  (** Abstractly evaluate an expression to a type.
    * This function also generates constraints and accumulates them into 
    * the list [cs] whenever you call [t1 === t2]. *)
  let rec abstract_eval (gamma : gamma) (e : expr) : ty =
    (* The following line loads functions in DSL module, allowing you to write
       [int -> (bool * ??"'X")] instead of [TFun (TInt, TProd (TBool, TVar "'X"))].
        However, you don't have to use the DSL functions, and you can just
       call the appropriate [ty] constructors. *)
    let open DSL in
    (* If you prefer the "printf" school of debugging, uncomment the following line,
       BUT DON'T FORGET TO COMMENT IT OUT BEFORE YOU SUBMIT *)
    (* Fmt.epr "[abstract_eval] %a\n%!" Ast.Pretty.pp_expr e; *)
    (* Fmt.epr "[abstract_eval] Gamma:\n%!  %a\n%!" pp_gamma gamma; *)
    try
      match e with
      | Num _ -> TInt
      | True | False -> TBool
      | Var x -> if Flag.polymorphic then part4 () else 
        (match find gamma x with 
        | Some (Mono t) -> t 
        | None -> ty_err ("\nin expression Var" ^ show_expr e)
        )
      | Binop (_, e1, e2) ->
          let t1 = abstract_eval gamma e1 in
          let t2 = abstract_eval gamma e2 in
          (* constrain both t1 and t2 to be int type *)
          t1 === TInt;
          t2 === TInt;
          (* return int as the type of the overal binop expression *)
          TInt
      | Comp (_, e1, e2) -> 
        let t1 = abstract_eval gamma e1 in 
        let t2 = abstract_eval gamma e2 in 
        t1 === TInt;
        t2 === TInt;
        TBool
      | IfThenElse (e1, e2, e3) -> 
        let t1 = abstract_eval gamma e1 in 
        let t2 = abstract_eval gamma e2 in 
        let t3 = abstract_eval gamma e3 in 
        t1 === TBool; 
        t2 === t3; 
        t2
      | Let (e1, Scope (x, e2)) ->
          if Flag.polymorphic then part4 () else (
              let t1 = abstract_eval gamma e1 in 
              let gamma' = add gamma x (Mono t1) in 
              abstract_eval gamma' e2 )
      | Lambda (topt, Scope (x, e')) -> 
        let f = fresh_var() in
        let gamma' = add gamma x (Mono f) in 
        TFun(f, abstract_eval gamma' e')
      | App (e1, e2) -> 
        let t1 = abstract_eval gamma e1 in 
        let t2 = abstract_eval gamma e2 in 
        let x1 = fresh_var() in 
        let x2 = fresh_var() in 
        t1 === (TFun(x1, x2)); 
        t2 === x1; 
        x2
      | ListNil topt -> let x = fresh_var() in TList x
      | ListCons (e1, e2) -> 
        let t1 = abstract_eval gamma e1 in 
        let t2 = abstract_eval gamma e2 in 
        t2 === TList t1; 
        TList t1
      | ListMatch (e1, e2, Scope (x, Scope (y, e3))) -> 
        let t1 = abstract_eval gamma e1 in 
        let x' = fresh_var() in 
        let t2 = abstract_eval gamma e2 in 
        let gamma' = add gamma x (Mono x') in 
        let gamma'' = add gamma' y (Mono (TList x')) in 
        let t3 = abstract_eval gamma'' e3 in 
        t1 === TList x'; 
        t2 === t3; 
        t2
      | Fix (topt, Scope (f, e1)) -> 
        let f' = fresh_var () in 
        let gamma' = add gamma f (Mono f') in 
        let t = abstract_eval gamma' e1 in 
        t === f'; 
        f'
      | Annot (e, t_expected) ->
          let t_actual = abstract_eval gamma e in
          (* constrain t_actual to be equal to t_expected *)
          t_actual === t_expected;
          t_expected
      | Pair (e1, e2) -> part3 ()
      | Fst e' -> part3 ()
      | Snd e' -> part3 ()
      | _ -> ty_err ("[abstract_eval] ill-formed: " ^ show_expr e)
    with Type_error msg -> ty_err (msg ^ "\nin expression " ^ show_expr e)

  (*******************************************
   *           Constraint Solving            *
   *******************************************)

  (** Constraint solver = unification/forward substitution from the empty solution, then backward substitution *)
  and solve (cs : cons list) : sigma =
    let sigma = unify empty cs in
    print_endline "equal var strings";
    backward sigma

  (** Unification (aka forward substitution) phase of the constraint solver *)
  and unify (s : sigma) (cs : cons list) : sigma =
    match cs with 
    | [] -> s 
    | (t1, t2) :: cs' -> 
      if equal_ty t1 t2 then unify s cs' 
      else (
        match t1, t2 with 
        | TVar x, _ when not (mem x (Utils.free_vars t2)) -> 
          (* let cs'' = List.map (fun (t1',t2') -> (Utils.subst x t2 t1',Utils.subst x t2 t2')) cs' in  *)
          let cs'' = List.map ~f:(fun (t1', t2') -> (Utils.subst x t2 t1', Utils.subst x t2 t2')) cs' in
          compose x t2 (unify ((x, t2)::s)  cs'')
        | _, TVar x when not (mem x (Utils.free_vars t1))-> 
          let cs'' = List.map ~f:(fun (t1',t2') -> ((Utils.subst x t1 t1'),(Utils.subst x t1 t2'))) cs' in 
          compose x t2 (unify ((x, t2)::s)  cs'')
        | TFun (a1, a2), TFun (b1, b2) -> 
          unify s ((a1,b1)::(a2,b2)::cs')  (** question: do i add smth to sigma? **)
        | TList t1, TList t2 -> unify s ((t1,t2)::cs')
        | TProd(a1,a2),TProd(b1,b2) -> unify s ((a1,b1)::(a2,b2)::cs')
        | _-> ty_err ("\n ty err caught at tendof unify")
      )

  (** Backward substitution phase of the constraint solver *)
  and backward (s : sigma) : sigma = 
    (* let s' = List.map ~f:( fun (v',t') -> List.map ~f:( fun (v,t) -> (v, Utils.subst v' t' t)) s ) s in  *)
    let s' = List.map ~f:( fun (v,t) -> List.fold_right ~f:( fun (v',t') acc -> (fst acc, Utils.subst v' t' (snd acc))) s ~init:(v,t)) s in

    (* let s' = List.fold_right ~f:(fun (v',t') acc -> List.map ~f:( fun (v,t) -> (v, Utils.subst v' t' t) ) acc ) s s in  *)
    if equal_sigma s s' then s else backward s'
    
end

(*******************************************
 *             Type inference              *
 *******************************************)

(** Infer the type of expression [e] in the environment [g].
  * The flag [p] optionally enables polymorphic type inference *)
let infer_with_gamma ~(gamma : gamma) ~(p : bool) (e : expr) : ty =
  let module I = Infer (struct
    let polymorphic = p
  end) in
  let open I in
  let t = abstract_eval gamma e in
  let s = solve (I.curr_cons_list ()) in
  Utils.apply_sigma s t |> Utils.normalize

(** Infer the type of expression [e]. 
  * The flag [p] optionally enables polymorphic type inference *)
let infer ~(p : bool) (e : expr) : ty = infer_with_gamma ~gamma:[] ~p e
