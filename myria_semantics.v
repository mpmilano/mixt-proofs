
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
| Flat_Assign_ptr : var -> var -> flat_com
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

Definition last_index index (l : (list nat )) : nat:=
  match l return nat with
    | hd :: tl => (last l hd)
    | [] => index
  end.


Definition next_index' index l := S (last_index index l). 
(* Order: list hd is last declaration, list tail is first.  2nd elem of outer pair is a varref.*)
Fixpoint flatten_exp' (index : nat) (e : exp) : prod (list (prod nat flat_exp)) var
  := match e with 
       | Var x => ([], x)
       | Binop e₁ op e₂ =>
         match (flatten_exp' (S index) e₂) with
           | (decls_e2, ref_e2) =>
             match ((flatten_exp' (next_index' (S index) 
                                               (map fst decls_e2))
                                  e₁)) with
               | (decls_e1, ref_e1) => 
                 ( (index, Flat_Binop ref_e1 op ref_e2)
                     ::match (map fst decls_e2) with
                         | [] => (fst (flatten_exp' (S index) e₁)) 
                         | _::_ => decls_e2 
                                     ++ (fst (flatten_exp' (next_index' (S index) (map fst decls_e2)) e₁))
                       end
                   ,System index)
             end
         end
       | Not e =>
         ((match (flatten_exp' (S index) e) with
             | (decls,ref) => (index, (Flat_Not ref))::decls
           end), System index)
       | Const x => ((index,Flat_Const x)::[],System index)
       | Tt => ((index,Flat_Tt)::[],System index)
       | Ff => ((index,Flat_Ff)::[],System index)
       | Deref e =>
         (match (flatten_exp' (S index) e) with
           | (decls,ref) => (index,(Flat_Deref ref))::decls
         end, System index)
     end.


Eval compute in (flatten_exp' 3 (Binop Tt Or (Binop Tt And Ff))).


Definition test: list nat := nil.
Eval compute in next_index' 1 test.
Eval compute in next_index' 2  (map (fun x=> S x) test).

Lemma last_append_head: forall {A:Type}(a:A) (l:list A),
last l a = last (a::l) a.
Proof. induction l; crush. Qed.

Lemma next_index'_index: forall  l index,
(next_index' (S index) (map (fun x : nat => S x) l))
            =
 S (next_index' index l).

Proof. induction l; crush.
 unfold next_index'. unfold last_index.
repeat rewrite <- last_append_head. 
assert (forall (t:list nat)(b:nat),last (map (fun x : nat => S x) t) (S b) = (S (last t b))).
induction t; crush. destruct t. Focus 2.


assert (forall (h:nat) (l:list nat), map (fun x : nat => S x) (h :: l)
= (S h) :: map (fun x : nat => S x) l).

induction l; crush.
rewrite H. auto. auto. auto.
Qed.

Lemma last_drop_head: forall (l: list nat)(a n0 n:nat),
last (a::n0::l) n = last (n0::l) n.
Proof.
induction l; crush.
Qed.
 
Lemma last_in: forall (n:nat) (l: list nat),In (last (n :: l) n) (n :: l).
Proof. induction l. compute. auto. rewrite <- last_append_head.
 rewrite <- last_append_head in IHl.
 destruct l. compute. auto.
 assert (last (a::n0::l) n = last (n0::l) n). apply last_drop_head.
 rewrite H.
 apply in_inv in IHl. destruct IHl. crush. crush.
Qed.
 

Lemma map_S_first: (forall (h:nat) (l:list nat), map (fun x : nat => S x) (h :: l)
= (S h) :: map (fun x : nat => S x) l).
Proof. induction l; crush.
Qed.

Ltac remember_destruct x name := remember x as name; destruct name; subst.
Ltac remember_destruct' x  := remember x as tmpname; destruct tmpname; subst.

Lemma pairs_in_context_work: forall {A B : Type} {l : A} {r : B} {e : (prod A B)} , (l,r) = e -> l = (fst e) /\ r = (snd e). crush. Qed. 

Ltac clear_context_pairs := match goal with | [H : (?l,?r) = ?e |- _] =>
                                              assert (l = fst e) by apply (pairs_in_context_work H );
                                                assert (r = snd e) by apply (pairs_in_context_work H );
                                                clear H
                            end.
Ltac destruct_lets :=
  match goal with
    | [|- context [let (_,_) := ?expr in _] ] =>  remember_destruct' expr
    | [ H : context [let (_,_) := ?expr in _] |- _ ] =>  remember_destruct' expr
    | [|- context [map (fun x : nat => S x) (map ?fst ?subexpr)] ] => remember_destruct' (map (fun x : nat => S x) (map fst subexpr)) 
  end; clear_context_pairs.

Ltac mycrush := crush; repeat destruct_lets; crush.

Lemma flatten_exp'_index: forall (e:exp) (index :nat),
(map fst (fst (flatten_exp' (S index) e))) = (map (fun x=>S x)
(map fst (fst (flatten_exp' index e)))).
Proof. induction e; mycrush.
  remember (map fst (fst (flatten_exp' index e2))) as  l.
  destruct l eqn: Q; crush.
 repeat rewrite map_app. crush.
 remember (map (fun x : nat => S x)
                    (map fst (fst (flatten_exp' index e2))))
 as temp.
 repeat rewrite <- map_S_first. 
 rewrite next_index'_index. crush.

Qed.


Require Import Omega.
Lemma S_in: forall a l,  In (S a) (map (fun x=> S x) l)-> In a l.
Proof. induction l; crush.
Qed.


Lemma in_S: forall a l, In a l -> In (S a) (map (fun x=> S x) l).
Proof. induction l; crush.
Qed.

Lemma in_S_iff: forall a l, In a l <-> In (S a) (map (fun x=> S x) l).
Proof. split. apply in_S. apply S_in. Qed.


Eval compute in (map fst (fst (flatten_exp' 0 (Binop Tt Or (Binop Tt And Ff))))).

Fixpoint is_sequential (l: list nat) : Prop :=
  match l with 
  | [] => True
  | h :: t => match t with
                | [] => True
                | h0 :: t0 => h0 = S h /\ is_sequential t
              end
  end.

Lemma S_is_sequential: forall (l:list nat),
 is_sequential l -> is_sequential (map (fun x=> S x) l).
Proof.
  induction l ; crush. induction l; crush.
Qed.

Lemma first_is_index : forall e index h t,
h::t=(map fst (fst (flatten_exp' index e))) -> index = h.
induction e; mycrush.
Qed.

Lemma last_default_irrelevant : forall (n a:nat)( l:list nat),
  last (n::l) a = last (n::l) n.
Proof. induction l; crush. destruct l; auto.
Qed.
Lemma seq_concat_h: forall l1 n1 ,
  is_sequential (n1::l1) 
   -> is_sequential ((n1::l1)++[next_index' (S n1) (n1::l1) ]).

Proof.
  induction l1 as [|l1' a]; crush.
  destruct a. simpl. split. compute. auto. auto.
 assert ((n :: a) ++ [next_index' (S n1) (n1 :: S n1 :: n :: a)]=
n :: (a ++ [next_index' (S n1) (n1 :: S n1 :: n :: a)])).
 auto.
   rewrite H. split. destruct H1. auto.
   apply IHa in H1.
 assert ( (n :: a) ++ [next_index' (S (S n1)) (S n1 :: n :: a)]
  =  n :: (a ++ [next_index' (S (S n1)) (S n1 :: n :: a)])). auto.
 rewrite H0 in H1.
  assert (next_index' (S (S n1)) (S n1 :: n :: a)=next_index' (S n1) (n1 :: S n1 :: n :: a)).
  unfold next_index'. unfold last_index.  repeat rewrite last_drop_head.
  repeat rewrite last_default_irrelevant.
  
 Hint Resolve last_default_irrelevant. auto.
 rewrite <- H2.  destruct H1. auto.
 Qed.

Lemma seq_concat : forall (a:nat)(l1 l2: list nat),
  is_sequential (l1++[a]) -> is_sequential (a::l2) ->
  is_sequential (l1++(a::l2)).
Proof.
  induction l1; crush. 
  destruct (l1 ++ a :: l2) eqn: Q. auto.
  destruct l1 eqn:Q2. simpl in *. inject Q. crush.
  simpl in Q. inject Q.
  split. crush. apply IHl1.
  destruct((n :: l0) ++ [a]). auto. destruct H; auto.
  destruct l2; auto.
  Qed.


Lemma flatten_exp'_sequential : forall e index ,
  is_sequential (map fst (fst (flatten_exp' index e))).
Proof. induction e; mycrush.
  Focus 2. rewrite flatten_exp'_index.
  remember (map fst (fst (flatten_exp' index e))) as l.
  destruct l. simpl; auto.
  rename index into i.
  assert (is_sequential ( map fst (fst (flatten_exp' i e)))).
  apply IHe.
  rewrite <- Heql in H.  
 assert (forall (h:nat) (l:list nat), map (fun x : nat => S x) (h :: l)
= (S h) :: map (fun x : nat => S x) l).
  induction l; crush.
  rewrite H0. split.
  assert (n=i). apply first_is_index in Heql. auto. auto.
  rewrite <- H0. apply S_is_sequential. auto.
    Focus 2. rewrite flatten_exp'_index.
  remember (map fst (fst (flatten_exp' index e))) as l.
  destruct l. simpl; auto.
  rename index into i.
  assert (is_sequential ( map fst (fst (flatten_exp' i e)))).
  apply IHe.
  rewrite <- Heql in H.  
 assert (forall (h:nat) (l:list nat), map (fun x : nat => S x) (h :: l)
= (S h) :: map (fun x : nat => S x) l).
  induction l; crush.
  rewrite H0. split.
  assert (n=i). apply first_is_index in Heql. auto. auto.
  rewrite <- H0. apply S_is_sequential. auto.
  (*hard case*)
  repeat rewrite map_app.
  remember (map fst (fst (flatten_exp' (S index) e2)))  as l1.
  destruct l1 eqn:Q1. rename index into i.
  Eval compute in flatten_exp' 0 (Binop (Binop (Var (User 3)) And Tt) And (Binop (Var (User 4)) And Tt)).
 
  destruct (map fst (fst (flatten_exp' (S i) e1))) eqn:Q2.
  auto. split. symmetry in Q2. apply first_is_index in Q2.
 auto. rewrite <- Q2. apply IHe1.
  repeat rewrite Heql1.
  remember (map fst
    (fst (flatten_exp' (S index) e2) ++
     fst
       (flatten_exp'
          (next_index' (S index)
             (map fst (fst (flatten_exp' (S index) e2)))) e1))) as m.
  destruct m eqn:Q2. auto. 
  

  
  rewrite map_app in Heqm.
 
  assert (is_sequential l1). rewrite Q1. rewrite Heql1. auto.
  assert (is_sequential (l1++[(next_index' (S index) l1)])).
  
  apply first_is_index in Heql1. rewrite Heql1. rewrite Q1.
  apply seq_concat_h. rewrite <- Q1. auto.
  rewrite <- Heql1 in Heqm. rewrite <- Q1 in Heqm.
  remember (map fst
         (fst (flatten_exp' (next_index' (S index) l1) e1))) as l2.
  assert (is_sequential l2).
  rewrite Heql2; auto. rewrite Heqm.
  destruct l2. assert (forall l1:list nat, l1++[]=l1). induction l2; crush. rewrite H2 in *. split.
  apply first_is_index in Heql1. rewrite Q1 in Heqm.  inject Heqm. auto. auto. 
  split. rewrite Q1 in Heqm. rewrite <- app_comm_cons in Heqm.
  inject Heqm. apply first_is_index in Heql1. auto.
  apply seq_concat; auto. apply first_is_index in Heql2. 
  rewrite <- Heql2. auto. 
  Qed.


Definition flatten_exp index e := let (tmpl,var) := (flatten_exp' index e) in (List.rev tmpl, var).


Definition next_index (index : nat) (l : list (prod nat flat_exp)) :=
  match l with
    | (n,_)::_ => S n
    | _ => S index
  end.

Fixpoint declare_everything (l : (list (prod nat flat_exp))) (c : flat_com)  : flat_com :=
  match l return flat_com with
    | ((var,exp)::rest) => Flat_Declaration (System var) exp (declare_everything rest c)
    | [] => c
  end.

Definition max_nat a b c :=
  if Nat.ltb a b
  then if Nat.ltb b c then c else b
  else if Nat.ltb a c then c else a.

Lemma max_nat_correct : forall (a b c : nat), (Nat.ltb a b) = Nat.ltb a (max_nat a b c).
  
  Admitted.
                                    

Definition next_var2 (a b : var) (index : nat) :=
  match (a,b) with
    | (System a, User _) => S a
    | (System a, System b) => if Nat.ltb a b then S b else S a
    | (User _, System a) => S a
    | (User _, User _) => index
  end.


Definition next_var3 (a b c: var) (index : nat) :=
  next_var2 (System (next_var2 a b index)) c index.

Definition next_var a index := match a with | System a => S a | User _ => index end.

Fixpoint next_var_exp (index : nat)  (e : flat_exp) :=
  match e with
    | Flat_Const _ => S index
    | Flat_Var a => next_var a index
    | Flat_Binop a op b => next_var2 a b index
    | Flat_Tt => S index
    | Flat_Ff => S index
    | Flat_Not a => next_var a index
    | Flat_Deref a => next_var a index
  end.

Fixpoint next_var_cmd (index : nat)  (c : flat_com) := 
  match c return nat -> nat with
    | Flat_Return x => next_var x
    | Flat_Assign_var x y => next_var2 x y 
    | Flat_Assign_ptr x y => next_var2 x y 
    | Flat_Declaration x e s => next_var3 x (System (next_var_exp index e)) (System (next_var_cmd index s))
    | Flat_If x e s => next_var3 x (System (next_var_cmd index e)) (System (next_var_cmd index s))
    | Flat_While c t => next_var2 c (System (next_var_cmd index t)) 
    | Flat_Seq s₁ s₂ => next_var2 (System (next_var_cmd index s₁)) (System (next_var_cmd index s₂))
    | Flat_Skip => (fun y => y)
  end index.

  
Fixpoint flatten (index : nat) (c : com) : flat_com :=
  match c with
    | Return e => let (lst,ref) := flatten_exp index e in
                  declare_everything lst (Flat_Return ref)
    | Assign_var y e => let (lst,ref) := flatten_exp index e in
                        declare_everything lst (Flat_Assign_var y ref)
    | Assign_ptr y e => let (lst,ref) := flatten_exp index e in
                        let index' := match ref with | System x => S x | User _ => index end in
                        let (lst2,ref2) := flatten_exp index' y in
                        declare_everything lst (declare_everything lst2 (Flat_Assign_ptr ref2 ref))
    | Declaration x e s => let (lst,ref) := flatten_exp index e in
                           let next_ind := next_index index lst in
                           declare_everything lst (Flat_Declaration x (Flat_Var ref) (flatten next_ind s) )
    | If c t e => let (lst,ref) := flatten_exp index c in
                  let next_ind := next_index index lst in
                  let flat_t := (flatten next_ind t) in
                  declare_everything lst (Flat_If ref flat_t (flatten (next_var_cmd next_ind flat_t) e) )
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
    | Flat_Assign_ptr x' e => match (get x' s) with
                                | Some (Remote_value x) =>
                                  if (is_declared x s)
                                  then
                                    match (get e s) with
                                      | Some ans => Some (Flat_Skip , (set_remote x ans s), None)
                                      | None => None
                                    end
                                  else None
                                | _ => None
                       end
  end.
