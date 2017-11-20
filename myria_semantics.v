
Require Import Bool Arith String List CpdtTactics.
Open Scope string_scope.
Open Scope list_scope.

Import ListNotations.

Definition var := nat.

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
        (fun y => if Nat.eqb x y then Some n else get y s'))
    end.

Definition set_local (x:var) (n:value) (s':state) : state :=
  match s' with
    | (s,r) =>  (
        (fun y => if Nat.eqb x y then Some n else get y s'),r)
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

Definition last_index (l : (list (nat * flat_exp))) : nat:=
  match l return nat with
    | hd :: tl => (fst (last l hd))
    | [] => 0
  end.

Definition last_indexp (l : (prod (list (prod nat flat_exp)) flat_exp)) :=
  last_index (fst l).

Definition next_index l := S (last_index l).

(* Order: list hd is last declaration, list tail is fst.  2nd elem of outer pair is a varref.*)
Fixpoint flatten_exp (index : var) (e : exp) : prod (list (prod nat flat_exp)) var
  := match e with 
       | Var x => ([], x)
       | Binop e₁ op e₂ =>
         match (flatten_exp (S index) e₂) with
           | (rest_right,right_ref) =>
             match (flatten_exp (next_index rest_right) e₁) with
               | (rest_left,left_ref) =>
                 (((index, Flat_Binop left_ref op right_ref) :: (rest_right ++ rest_left)), index)
             end
         end
       | Not e =>
         match (flatten_exp (S index) e) with
           | (rest, var) => ((index, (Flat_Not var))::rest, index)
         end
       | Const x => ((index,Flat_Const x)::[],index)
       | Tt => ((index,Flat_Tt)::[],index)
       | Ff => ((index,Flat_Ff)::[],index)
       | Deref e => match (flatten_exp (S index) e) with
                        | (rest,var) => ((index,(Flat_Deref var))::rest,index)
                    end
     end.

Lemma flatten_exp_index_unique : forall e index,
                                   index > 0 -> 
                                   NoDup (List.map fst (fst (flatten_exp index e))).


Fixpoint next_var (index : var) (e : exp) : var
  := match e with 
       | Var x => index
       | Binop e₁ op e₂ =>
         match (next_var (S index) e₁) with | next => next_var (S next) e₂ end
       | Not e => next_var (S index) e
       | Const x => index
       | Tt => index
       | Ff => index
       | Deref e => next_var (S index) e
     end.


Fixpoint flatten_exp2 (index : var) (e : exp) (context : (flat_exp -> flat_com)) : flat_com
  := match e with 
       | Var x => context (Flat_Var x)
       | Binop e₁ op e₂ =>
         match (next_var (S index) e₁) with | m => 
         match (flatten_exp
                  (S index) e₂
                  (fun e'' => Flat_Declaration
                                index e''
                                (context (Flat_Binop index op m))
                  )) with
           | inner_exp =>
             flatten_exp (S m)
                         e₁
                         (fun e' => Flat_Declaration
                                      m e' inner_exp
                         )
         end
         end
       | Not e => 
         flatten_exp (S index) e (fun e' => Flat_Declaration index e' (context (Flat_Not index)))
       | Const x => context (Flat_Const x)
       | Tt => context (Flat_Tt)
       | Ff => context (Flat_Ff)
       | Deref e => 
         flatten_exp (S index) e (fun e' => Flat_Declaration index e' (context (Flat_Deref index)))
     end.

Check nat.

Fixpoint all_declared_vars_surface (c : com) : list var :=
  match c with
    | Declaration x _ s => x :: (all_declared_vars_surface s)
    | Assign_var _ _ => []
    | Assign_ptr _ _ => []
    | Seq s₁ s₂ => (all_declared_vars_surface s₁) ++ (all_declared_vars_surface s₂)
    | If _ _ s => all_declared_vars_surface s
    | While _ s => all_declared_vars_surface s
    | Return _ => []
    | Skip => []
  end.

Fixpoint all_declared_vars (c : flat_com) : list var :=
  match c with
    | Flat_Declaration x _ s => x :: (all_declared_vars s)
    | Flat_Assign_var _ _ => []
    | Flat_Assign_ptr _ _ => []
    | Flat_Seq s₁ s₂ => (all_declared_vars s₁) ++ (all_declared_vars s₂)
    | Flat_If _ _ s => all_declared_vars s
    | Flat_While _ s => all_declared_vars s
    | Flat_Return _ => []
    | Flat_Skip => []
  end.

Lemma flatten_exp_index_unique_retc : forall e index,
                                        index > 0 -> 
                                   NoDup
                                     (all_declared_vars
                                           (flatten_exp index e (fun e' => (Flat_Declaration 0 e' (Flat_Return 0))))).
Admitted.

Eval compute in (flatten_exp 1 (Binop ((Binop (Const 7) Plus (Const 15) )) Plus ((Binop (Const 7) Plus (Const 15) )) ) (fun e' => (Flat_Declaration 0 e' (Flat_Return 0)))).


Fixpoint next_var_cmd (index : var) (c : com) : var
  := match c with 
       | Return e => next_var index e
       | Skip => index
       | Assign_var x e => next_var index e
       | Assign_ptr x e => next_var index e
       | If c t e => next_var_cmd (next_var_cmd (next_var index c) t) e
       | While c t => next_var_cmd (next_var index c) t
       | Seq s₁ s₂ => next_var_cmd (next_var_cmd index s₁) s₂
       | Declaration x e s => match (if (Nat.ltb index x) then index else S x) with
                                | index => next_var_cmd (next_var index e) s
                              end
     end.

Fixpoint flatten (index : nat) (c : com) : flat_com :=
  match c with
    | Return (Var x) => Flat_Return x
    | Return e => flatten_exp (S index) e (fun e' => (Flat_Declaration index e' (Flat_Return index)))
    | Assign_var y (Var x) => Flat_Assign_var y x
    | Assign_var x e => flatten_exp (S index) e (fun e' => Flat_Declaration index e' (Flat_Assign_var x index))
    | Declaration x e s => match (next_var index e) with
                             | m => flatten_exp
                                      index e
                                      (fun e' => Flat_Declaration x e' (flatten m s)) end
    | Assign_ptr y (Var x) => Flat_Assign_ptr y x
    | Assign_ptr x e => flatten_exp (S index) e (fun e' => Flat_Declaration index e' (Flat_Assign_ptr x index))
    | If (Var c) t e =>
      match (next_var_cmd index t) with
        | m => Flat_If c (flatten index t) (flatten m e)
      end
    | If c t e =>
      match (next_var (S index) c) with
        | index' =>
          flatten_exp
            (S index) c
            (fun e' => Flat_Declaration
                         index e'
                         (Flat_If index
                                  match (next_var_cmd index' t) with
                                    | m => Flat_If index (flatten index' t) (flatten m e)
                                  end
                         ))
      end
    | While (Var c) t => Flat_While c (flatten index t)
    | While c t =>
      match (next_var (S index) c) with
        | index' =>
          flatten_exp
            (S index) c
            (fun e' => Flat_Declaration
                         index e' 
                         (Flat_While index  (flatten index' t)))
      end
    | Seq s₁ s₂ =>
      Flat_Seq (flatten index s₁) (flatten (next_var_cmd index s₁) s₂)
    | Skip => Flat_Skip
  end.


Fixpoint step_com_flat (cmd : com_flat) (s : state) : option (com * state * (option value)) :=
  match cmd with
    | Flat_Seq c1 c2 =>
      (match (step_com_flat c1 s) with
              | Some (newcmd,newstate,newret)  =>
                match newret with
                  | Some a => None
                  | None => Some ((Seq newcmd c2), newstate, None)
                end
              | None => Some (c2, s, None)
      end)
    | Flat_Skip => None
    | Flat_Return x => match (get x s) with
                         | Some ans => Some (Skip, s, Some ans)
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
      match (get y s) with
        | None => None
        | Some ans => 
          if (is_declared x s)
               && (type_matches_op (ret_op (get x s)) (Some (eval_exp e s)))
          then
            match (eval_exp e s) with
              | Value ans => Some (Skip , (set_local x ans s), None)
              | TypeError => None
            end
          else None
        | Flat_Assign_ptr x' e => match (eval_exp x' s) with
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
    | Flat_If condition thn els =>
      match (eval_exp condition s) with
        | Value (Bool_value true) => Some (thn, s, None)
        | Value (Bool_value false) => Some (els, s, None)
        | _ => None
      end
    | Flat_While condition thn => Some ((If condition (Seq thn cmd) Skip), s, None)
  end.
