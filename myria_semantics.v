(** * Problem Set 3 *)

(** In class we saw a relational small-step semantics for IMP.
    Abhishek observed that the small-step semantics could be written as
    a function instead, since there is no recursion in the 'while'
    case. (However, there is a loss of extensibility to some
    nondeterministic features like concurrency.) Are these semantics
    really equivalent?

    Here is the relational semantics we saw in class:
 *)

(* begin hide *)
Require Import Bool Arith String List CpdtTactics.
Open Scope string_scope.


Definition var := nat.

Inductive binop := Plus | Times | Minus.

Inductive exp : Type := 
| Const : nat -> exp
| Var : var -> exp
| Binop : exp -> binop -> exp -> exp
| Tt : exp
| Ff : exp
| Eq : exp -> exp -> exp
| Lt : exp -> exp -> exp
| And : exp -> exp -> exp
| Or : exp -> exp -> exp
| Not : exp -> exp
| FieldRef : exp -> var -> exp
| Deref : exp -> exp.

Inductive com : Type := 
| Skip : com
| Return : exp -> com
| Declaration : var -> exp -> com 
| Assign_var : var -> exp -> com
| Assign_ptr : exp -> exp -> com
| Seq : com -> com -> com
| If : exp -> com -> com -> com
| While : exp -> com -> com.

Inductive value : Type :=
| Nat_value : nat -> value
| Bool_value : bool -> value
| Record_value : var -> value -> value -> value
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
| Flat_Eq : var -> var -> flat_exp
| Flat_Lt : var -> var -> flat_exp
| Flat_And : var -> var -> flat_exp
| Flat_Or : var -> var -> flat_exp
| Flat_Not : var -> flat_exp
| Flat_FieldRef : var -> var -> flat_exp
(*This one doesn't exist: *)| Flat_Deref : var -> flat_exp.

Inductive flat_com : Type := 
| Flat_Skip : flat_com
| Flat_Return : flat_exp -> flat_com
| Flat_Declaration : var -> flat_exp -> flat_com -> flat_com 
| Flat_Assign_var : var -> var -> flat_com
| Flat_Assign_ptr : exp -> var -> flat_com
| Flat_Seq : flat_com -> flat_com -> flat_com
| Flat_If : var -> flat_com -> flat_com -> flat_com
| Flat_While : var -> flat_exp -> flat_com -> flat_com.

Inductive flat_value : Type :=
| Flat_Nat_value : nat -> flat_value
| Flat_Bool_value : bool -> flat_value
| Flat_Record_value : var -> flat_value -> flat_value -> flat_value
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

  Fixpoint lookup_field x e :=
    match e with
      | Record_value field_name field_val rest =>
        if (Nat.eqb x field_name) then ret field_val else lookup_field x rest
      | _ => TypeError
    end.
  
Fixpoint eval_exp (e:exp) (s:state) : answer := 
  match e with 
    | Const n => ret (Nat_value n)
    | Var x => match (get x s) with
                 | Some e => ret e
                 | None => TypeError
               end
    | FieldRef e field_name =>
      match (eval_exp e s) with
        | Value (Record_value a b c) =>
          lookup_field field_name (Record_value a b c)
        | _ => TypeError
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
    | Eq e1 e2 => fst <- (eval_exp e1 s);
        snd <- (eval_exp e2 s);
        match (fst,snd) with
          | ((Nat_value fst), (Nat_value snd)) =>
            ret (Bool_value (Nat.eqb fst snd))
          | _ => TypeError
        end
    | Lt e1 e2 => fst <- (eval_exp e1 s);
        snd <- (eval_exp e2 s);
        match (fst,snd) with
          | ((Nat_value fst), (Nat_value snd)) =>
            ret (Bool_value (Nat.ltb fst snd))
          |_  => TypeError
        end
    | And b1 b2 => fst <- (eval_exp b1 s);
        snd <- (eval_exp b2 s);
        match (fst,snd) with
          | ((Bool_value fst), (Bool_value snd)) =>
            ret (Bool_value (fst && snd))
          |_  => TypeError
        end
    | Or b1 b2 => fst <- (eval_exp b1 s);
        snd <- (eval_exp b2 s);
        match (fst,snd) with
          | ((Bool_value fst), (Bool_value snd)) =>
            ret (Bool_value (fst || snd))
          |_  => TypeError
        end
    | Not b => tmp <- (eval_exp b s);
        match tmp with | (Bool_value tmp) => ret (Bool_value (negb tmp))
                    | _ => TypeError
        end
  end.

(* end hide *)


Inductive imp_type :=
| Nat_type : imp_type
| Bool_type : imp_type
| Record_type : imp_type
.

Definition is_declared x s :=
  match (get x s) with | Some _ => true | None => false end.

Definition type_matches ( l r : answer)  :=
  match (l,r) with
    | (Value (Nat_value _), Value (Nat_value _)) => true
    | (Value (Bool_value _), Value (Bool_value _)) => true
    | (Value (Record_value _ _ _), Value (Record_value _ _ _)) => true
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
    | Declaration x e =>
      match (is_declared x s) with
        | true => None
        | false =>
          match (eval_exp e s) with
            | Value ans => Some (Skip , (set x ans s), None)
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

Eval compute in (step_com_fn (Declaration 0 (And Tt Tt) )
                             (σ,ρ)
                ).
  
Fixpoint flatten_exp (index : nat) (context : (flat_exp -> flat_com)) (e : exp) : flat_com
  :=
  | Var x => context (Flat_Var x)
  | Not e => match index with
               | S n => flatten_exp n (fun e' => Flat_Declaration index (Flat_Not e')
                                                                  (context (Flat_Var index)))
                                    e
               | _ => Flat_Skip
                 end
  | _ => Flat_Skip

with flatten (index : nat) (c : com) :=
  match c with
    | Return e =>
      match (index,e) with
        | (_,Var x) => Flat_Return (Flat_Var x)
        | (S index',_) => flatten_exp index'
                                      (fun e' => (Flat_Declaration index e' (Flat_Return (Flat_Var index)))) e
        | _ => Flat_Skip

      end
        (*
    | Declaration : var -> exp -> com 
    | Assign_var : var -> exp -> com
    | Assign_ptr : exp -> exp -> com
    | Seq : com -> com -> com
    | If : exp -> com -> com -> com
    | While : exp -> com -> com. *)
    | _ => Flat_Skip
  end.