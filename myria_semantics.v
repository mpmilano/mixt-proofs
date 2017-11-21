
Require Import Bool Arith String List CpdtTactics.
Open Scope string_scope.
Open Scope list_scope.

Import ListNotations.

Inductive var : Type :=
| User : nat -> var
| System : nat -> var.

Inductive binop := Plus | Times | Minus | And | Or | Eq.

Inductive exp : Type := 
| Const : nat -> exp
| Var : var -> exp
| Binop : exp -> binop -> exp -> exp
| Tt : exp
| Ff : exp
| Not : exp -> exp
| Deref : exp -> exp.

Inductive com : Type := 
| Skip : com
| Return : exp -> com
| Declaration : var -> exp -> com -> com 
| Assign_var : var -> exp -> com
| Assign_ptr : exp -> exp -> com
| Seq : com -> com -> com
| If : exp -> com -> com -> com
| While : exp -> com -> com.

Inductive value : Type :=
| Nat_value : nat -> value
| Bool_value : bool -> value
| Remote_value : var -> value.
Inductive answer : Type :=
| Value : value -> answer
| TypeError : answer.

Inductive flat_exp : Type := 
| Flat_Const : nat -> flat_exp
| Flat_Var : var -> flat_exp
| Flat_Binop : var -> binop -> var -> flat_exp
| Flat_Tt : flat_exp
| Flat_Ff : flat_exp
| Flat_Not : var -> flat_exp
(*This one doesn't exist: *)| Flat_Deref : var -> flat_exp.

Inductive flat_com : Type := 
| Flat_Skip : flat_com
| Flat_Return : var -> flat_com
| Flat_Declaration : var -> flat_exp -> flat_com -> flat_com 
| Flat_Assign_var : var -> var -> flat_com
| Flat_Assign_ptr : exp -> var -> flat_com
| Flat_Seq : flat_com -> flat_com -> flat_com
| Flat_If : var -> flat_com -> flat_com -> flat_com
| Flat_While : var -> flat_com -> flat_com.

Inductive flat_value : Type :=
| Flat_Nat_value : nat -> flat_value
| Flat_Bool_value : bool -> flat_value
| Flat_Remote_value : var -> flat_value.
Inductive flat_answer : Type :=
| Flat_Value : flat_value -> flat_answer
| Flat_TypeError : flat_answer. 

Definition local_state := var -> option value.

Definition σ : local_state := (fun _ => None).

Definition remote_state := var -> option value.

Definition ρ : remote_state := (fun _ => None).

Definition state := prod local_state remote_state.


Definition get_remote (x:var) (s:state) : option value :=
  match s with
    | (_,s') => s' x
  end.

Definition get_local (x:var) (s:state) : option value :=
  match s with
    | (s',_) => s' x
  end.

Definition get (x : var) (s : state) : option value :=
  match (get_local x s) with
    | Some y => Some y
    | None => get_remote x s
  end.


Definition set_remote (x:var) (n:value) (s':state) : state :=
  match s' with
    | (l,s) =>  (l,
                 (fun y =>
                    match (x,y) with
                      | (User x', User y') => if Nat.eqb x' y' then Some n else get y s'
                      | (System x', System y') => if Nat.eqb x' y' then Some n else get y s'
                      | _ => get y s'
                    end))
    end.

Definition set_local (x:var) (n:value) (s':state) : state :=
  match s' with
    | (s,r) =>  (
        (fun y =>
           match (x,y) with
             | (User x', User y') => if Nat.eqb x' y' then Some n else get y s'
             | (System x', System y') => if Nat.eqb x' y' then Some n else get y s'
             | _ => get y s'
           end),r)
    end.

Definition set (x:var) (n:value) (s:state) : state :=
  match (get_local x s) with
    | Some _ => set_local x n s
    | None => (match get_remote x s with
                 | Some _ => set_remote x n s
                 | None => set_local x n s
              end)
  end.


Definition eval_binop (b:binop) : nat -> nat -> nat := 
  match b with 
    | Plus => plus
    | Times => mult
    | Minus => minus
    | _ => (fun _ => (fun _ => 0))
  end.

  (** We'll begin by defining a monad where the results are always answers. *)
  Definition Ret(v:value) : answer := Value v.
  (** This will take care of propagating type errors for us. *)
  Definition Bind(c:answer) (f:value -> answer) : answer := 
    match c with 
      | Value v => f v
      | TypeError => TypeError
    end.

  (** Coq notation really comes in handy. *)
  Notation "'ret' x" := (Ret x) (at level 75) : comp_scope.
  Notation "x <- c ; f" := (Bind c (fun x => f))
    (right associativity, at level 84, c at next level) : comp_scope.
  Local Open Scope comp_scope.
  
Fixpoint eval_exp (e:exp) (s:state) : answer := 
  match e with 
    | Const n => ret (Nat_value n)
    | Var x => match (get x s) with
                 | Some e => ret e
                 | None => TypeError
               end
    | Deref e =>
      match (eval_exp e s) with
        | Value (Remote_value x) =>
          match (get x s) with | None => TypeError
                            | Some a => ret a
          end
        | _ => TypeError
      end          
    | Binop e1 b e2 =>
      fst <- (eval_exp e1 s); snd <- (eval_exp e2 s);
      match (fst,snd) with
        | ((Nat_value _fst), (Nat_value _snd)) =>
          ret (Nat_value ((eval_binop b) _fst _snd))
        | _ => TypeError
      end
    | Tt => ret (Bool_value true)
    | Ff => ret (Bool_value false)
    | Not b => tmp <- (eval_exp b s);
        match tmp with | (Bool_value tmp) => ret (Bool_value (negb tmp))
                    | _ => TypeError
        end
  end.

(* end hide *)


Inductive imp_type :=
| Nat_type : imp_type
| Bool_type : imp_type
.

Definition is_declared x s :=
  match (get x s) with | Some _ => true | None => false end.

Definition type_matches ( l r : answer)  :=
  match (l,r) with
    | (Value (Nat_value _), Value (Nat_value _)) => true
    | (Value (Bool_value _), Value (Bool_value _)) => true
    |  _ => false
  end.

Definition type_matches_op l r :=
  match (l,r) with
    | (Some l, Some r) => type_matches l r
    | _ => false
  end.

(** ** 1. Give a definition of the same small-step semantics, as a function.
    Note that a final configuration should step to [None].
*)

Definition ret_op a := match a with | Some a => Some (ret a) | None => None end.

Fixpoint step_com_fn (cmd : com) (s : state) : option (com * state * (option value)) :=
  match cmd with
    | Seq c1 c2 =>
      (match (step_com_fn c1 s) with
              | Some (newcmd,newstate,newret)  =>
                match newret with
                  | Some a => None
                  | None => Some ((Seq newcmd c2), newstate, None)
                end
              | None => Some (c2, s, None)
      end)
    | Skip => None
    | Return e => match (eval_exp e s) with
                    | Value ans => Some (Skip, s, Some ans)
                    | TypeError => None
                  end
    | Declaration x e next =>
      match (is_declared x s) with
        | true => None
        | false =>
          match (eval_exp e s) with
            | Value ans => Some (next , (set x ans s), None)
            | TypeError => None
          end
      end
    | Assign_var x e => if (is_declared x s)
                             && (type_matches_op (ret_op (get x s)) (Some (eval_exp e s)))
                        then
                          match (eval_exp e s) with
                            | Value ans => Some (Skip , (set_local x ans s), None)
                            | TypeError => None
                          end
                        else None
    | Assign_ptr x' e => match (eval_exp x' s) with
                           | Value (Remote_value x) =>
                             if (is_declared x s)
                                  && (type_matches_op (ret_op (get x s)) (Some (eval_exp e s)))
                             then
                               match (eval_exp e s) with
                                 | Value ans => Some (Skip , (set_remote x ans s), None)
                                 | TypeError => None
                          end
                             else None
                           | _ => None
                       end
    | If condition thn els =>
      match (eval_exp condition s) with
        | Value (Bool_value true) => Some (thn, s, None)
        | Value (Bool_value false) => Some (els, s, None)
        | _ => None
      end
    | While condition thn => Some ((If condition (Seq thn cmd) Skip), s, None)
  end.

Definition last_index index (l : (list (nat * flat_exp))) : nat:=
  match l return nat with
    | hd :: tl => (fst (last l hd))
    | [] => index
  end.

Definition last_indexp index (l : (prod (list (prod nat flat_exp)) flat_exp)) :=
  last_index index (fst l).

Definition next_index index l := S (last_index index l).

(* Order: list hd is last declaration, list tail is first.  2nd elem of outer pair is a varref.*)
Fixpoint flatten_exp' (index : nat) (e : exp) : prod (list (prod nat flat_exp)) var
  := match e with 
       | Var x => ([], x)
       | Binop e₁ op e₂ =>
         match (flatten_exp' (S index) e₂) with
           | (rest_right,right_ref) =>
             match (flatten_exp' (next_index (S index) rest_right) e₁) with
               | (rest_left,left_ref) =>
                 (((index, Flat_Binop left_ref op right_ref)::(rest_right ++ rest_left)), System index)
             end
         end
       | Not e =>
         match (flatten_exp' (S index) e) with
           | (rest, var) => ((index, (Flat_Not var))::rest, System index)
         end
       | Const x => ((index,Flat_Const x)::[],System index)
       | Tt => ((index,Flat_Tt)::[],System index)
       | Ff => ((index,Flat_Ff)::[],System index)
       | Deref e => match (flatten_exp' (S index) e) with
                        | (rest,var) => ((index,(Flat_Deref var))::rest,System index)
                    end
     end.

Lemma flatten_exp'_index_unique : forall e (index : nat),
                                   index > 0 -> 
                                   NoDup (List.map fst (fst (flatten_exp' index e))).
Admitted.

Lemma flatten_exp_sequential : forall e index n, index > 0 ->
                                                 S (nth n (List.map fst (fst (flatten_exp index e))) 0)
                                                 = (nth (S n) (List.map fst (fst (flatten_exp index e))) 1).
Admitted.


Fixpoint declare_everything (l : (list (prod nat flat_exp))) (c : flat_com)  : flat_com :=
  match l return flat_com with
    | ((var,exp)::rest) => Flat_Declaration var exp (declare_everything rest c)
    | [] => c
  end.

Definition max_nat a b c :=
  if Nat.ltb a b
  then if Nat.ltb b c then c else b
  else if Nat.ltb a c then c else a.

Lemma max_nat_correct : forall (a b c : nat), (Nat.ltb a b) = Nat.ltb a (max_nat a b c).
  Admitted.
                                    

Definition next_var_cmd (index : nat)  (c : flat_com) := index.
(*
  match c with
    | Flat_Return x => S x
    | Flat_Assign_var x y => if Nat.ltb x y then S y else S x
    | Flat_Assign_ptr x y => if Nat.ltb x y then S y else S x
    | Flat_Declaration x e s => S (max_nat x (next_var_cmd index e) (next_var_cmd index s))
    | Flat_If x e s => S (max_nat x (next_var_cmd index e) (next_var_cmd index s))
*)
  
Fixpoint flatten (index : nat) (c : com) : flat_com :=
  match c with
    | Return e => let (lst,ref) := flatten_exp index e in
                  declare_everything lst (Flat_Return ref)
    | Assign_var y e => let (lst,ref) := flatten_exp index e in
                        declare_everything lst (Flat_Assign_var y ref)
    | Assign_ptr y e => let (lst,ref) := flatten_exp index e in
                        declare_everything lst (Flat_Assign_ptr y ref)
    | Declaration x e s => let (lst,ref) := flatten_exp index e in
                           let next_ind := next_index index lst in
                           declare_everything lst (Flat_Declaration x (Flat_Var ref) (flatten next_ind s) )
    | If c t e => let (lst,ref) := flatten_exp index c in
                  let next_ind := next_index index lst in
                  (* Note: t and e not disjoin in this approach.  might be an issue?*)
                  declare_everything lst (Flat_If ref (flatten next_ind t) (flatten next_ind e) )
    | While c t => let (lst,ref) := flatten_exp index c in
                   let next_ind := next_index index lst in
                   declare_everything lst (Flat_While ref (flatten next_ind t) )
    | Seq s₁ s₂ =>
      let fst_stmt := (flatten index s₁) in 
      Flat_Seq fst_stmt (flatten (next_var_cmd index fst_stmt) s₂)
    | Skip => Flat_Skip
  end.

Variable unique_decl_com : com -> Prop.
Variable max_declaration_com : com -> nat.
Variable unique_decl_flat : flat_com -> Prop.

Lemma flatten_unique : forall (index : nat) (c : com), ((max_declaration_com c) < 40) -> (index > 40) -> (unique_decl_com c) -> (unique_decl_flat (flatten index c)).
Admitted.



(* if we move back to vars being pairs, then we can avoid the problem of ensuring no collisions between user-names and system-names by making left user and right system. i.e. user-right is always 0. *)

Eval compute in (flatten_exp 1 (Binop ((Binop (Const 7) Plus (Const 15) )) Plus ((Binop (Const 7) Plus (Const 15) )) )).


Fixpoint eval_flat_exp (e:flat_exp) (s:state) : answer := 
  match e with 
    | Flat_Const n => ret (Nat_value n)
    | Flat_Var x => match (get x s) with
                      | Some e => ret e
                      | None => TypeError
                    end
    | Flat_Deref x =>
      match (get x s) with
        | Some (Remote_value x) =>
          match (get x s) with | None => TypeError
                            | Some a => ret a
          end
        | _ => TypeError
      end
    | Flat_Binop e1 b e2 =>
      match (get e1 s) with
        | Some (Nat_value _fst) =>
          match (get e2 s) with
            | Some (Nat_value _snd) => ret (Nat_value ((eval_binop b) _fst _snd))
            | _ => TypeError
          end
        | _ => TypeError
      end
    | Flat_Tt => ret (Bool_value true)
    | Flat_Ff => ret (Bool_value false)
    | Flat_Not b =>
      match (get b s) with
        | Some (Bool_value tmp) => ret (Bool_value (negb tmp))
        | _ => TypeError
      end
  end.


Fixpoint step_com_flat (cmd : flat_com) (s : state) : option (flat_com * state * (option value)) :=
  match cmd with
    | Flat_Seq c1 c2 =>
      (match (step_com_flat c1 s) with
              | Some (newcmd,newstate,newret)  =>
                match newret with
                  | Some a => None
                  | None => Some ((Flat_Seq newcmd c2), newstate, None)
                end
              | _ => Some (c2, s, None)
      end)
    | Flat_Skip => None
    | Flat_Return x => match (get x s) with
                         | Some ans => Some (Flat_Skip, s, Some ans)
                         | None => None
                       end
    | Flat_Declaration x e next =>
      match (is_declared x s) with
        | true => None
        | false =>
          match (eval_flat_exp e s) with
            | Value ans => Some (next , (set x ans s), None)
            | TypeError => None
          end
      end
    | Flat_Assign_var x y =>
      match (get x s) with
        | None => None
        | Some ans => 
          if (is_declared x s)
          then
            match (get y s) with
              | Some ans => Some (Flat_Skip , (set_local x ans s), None)
              | None => None
            end
          else None
      end
    | Flat_If condition thn els =>
      match (get condition s) with
        | Some (Bool_value true) => Some (thn, s, None)
        | Some (Bool_value false) => Some (els, s, None)
        | _ => None
      end
    | Flat_While condition thn => Some ((Flat_If condition (Flat_Seq thn cmd) Flat_Skip), s, None)
    (* | Flat_Assign_ptr x' e => match (get x' s) with
                                | Some (Remote_value x) =>
                                  if (is_declared x s)
                                  then
                                    match (get e s) with
                                      | Some ans => Some (Flat_Skip , (set_remote x ans s), None)
                                      | None => None
                                    end
                                  else None
                                | None => None
                       end *)
    | _ => None
  end.
