open List;;
open Printf;;
type predicate = string * term list
and term = Var of string | Func of predicate;;
type clause = predicate * predicate list;;
module StrSet = Set.Make (struct type t = string
				    let compare = compare end);;
let rec variables t = 
  match t with
    | Var(x) -> StrSet.add x StrSet.empty
    | Func(_, []) -> StrSet.empty
    | Func(_, h::tl) -> 
	StrSet.union (variables h) 
	  (fold_right (fun el s -> StrSet.union (variables el) s) tl StrSet.empty);;

type substitution = {v : string; sv : term};;
let rec apply_substitutions subs t =
  match t with
    | Var(x) -> 
	(try (find (fun s -> s.v = x) subs).sv
	 with Not_found -> Var x)
    | Func(f, args) -> Func (f, (map (apply_substitutions subs) args));;

let copy_term start t =
  let vars = StrSet.elements (variables t) in
  let (subs, start') = 
    fold_right (fun v (vars', start') -> 
		  (let s = sprintf "_X%d" start' in
		     ({v=v; sv=Var(s)}::vars', start'+1))) vars ([], start) in
    (apply_substitutions subs t, start');;  

let rec occurs v t =
  let rec occ args =
    match args with
      | [] -> false
      | h::tl -> if occurs v h then true else occ tl
  in
    match t with
      | Var(x) -> v = x
      | Func(f, args) -> occ args;;

let rec zip l1 l2 =
  match (l1, l2) with
      ([], []) -> []
    | (x1::x1s, x2::x2s) -> (x1,x2)::zip x1s x2s
    | _ -> failwith "length of lists mismatch";;

exception Unify_error;;

let unify t1 t2 =
  let rec unify unif_stack subs =
    let rec substitute subs' stack =
      let ap = apply_substitutions subs' in
	match stack with
	  | [] -> []
	  | (h1, h2)::tl -> (ap h1, ap h2)::substitute subs tl
    in
      match unif_stack with
	| (Var(x), Var(y))::tl when x = y -> (tl, subs)
	| (Var(x), t)::tl
	| (t, Var(x))::tl -> 
	    if not (occurs x t) then
	      let s = {v=x; sv=t} in
		(substitute [s] tl, s::subs)
	    else raise Unify_error
	| (Func(f, args), Func(f', args'))::tl ->
	    if f <> f' || length args <> length args' then
	      raise Unify_error
	    else unify (append (zip args args') tl) subs
	| [] -> ([], subs)
  in
    snd (unify [(t1, t2)] [])
;;    

let unify_predicates pred1 pred2 = unify (Func pred1) (Func pred2);;

type database = clause list;;
type goal = predicate list;;

let rec matching_clause (db : database) start g =
  match db with
    | [] -> None
    | (h, _)::tl -> 
	try
	  let (h', start') = copy_term start (Func h) in
	  let subs = unify (Func g) h' in
	    Some (subs, tl, start')
	with Unify_error -> matching_clause tl start g
;;
