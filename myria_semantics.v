
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
       | Var x => ((index,Flat_Var x)::[],System index)
       | Binop e₁ op e₂ =>
         let (decls_e2, ref_e2) := (flatten_exp' (S index) e₂) in
         let (decls_e1, ref_e1) := ((flatten_exp' (next_index' (S index) (map fst decls_e2)) e₁)) in
         let binop_decl := (index, Flat_Binop ref_e1 op ref_e2) in
         ( binop_decl :: decls_e2 ++ decls_e1, System index)
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

Ltac remember_destruct x name eqname := remember x as name eqn:eqname; destruct name; subst.
Ltac remember_destruct' x  := remember x as tmpname; destruct tmpname; subst.

Ltac remember_destruct'' x  := remember x;
    match goal with [H : ?name = x |- _] => destruct name; subst
    end.

Ltac remember_induct x  := remember x;
    match goal with [H : ?name = x |- _] => induction name; subst; crush
    end.

Lemma pairs_in_context_work: forall {A B : Type} {l : A} {r : B} {e : (prod A B)} , (l,r) = e -> l = (fst e) /\ r = (snd e). crush. Qed. 

Ltac clear_context_pairs := match goal with | [H : (?l,?r) = ?e |- _] =>
                                              assert (l = fst e) by apply (pairs_in_context_work H );
                                                assert (r = snd e) by apply (pairs_in_context_work H );
                                                clear H
                            end.
Ltac destruct_things :=
  match goal with
    | [|- context [let (_,_) := ?expr in _] ] =>  remember_destruct' expr
    | [ H : context [let (_,_) := ?expr in _] |- _ ] =>  remember_destruct' expr
    | [|- context [map (fun x : nat => S x) (map ?fst ?subexpr)] ] => remember_destruct' (map (fun x : nat => S x) (map fst subexpr)) 
  end; clear_context_pairs.

Ltac mycrush := crush; repeat destruct_things; crush.

Ltac first_equal :=
  match goal with | [|- ?fst :: ?expr1 = ?fst :: ?expr2] =>
                    assert (expr1 = expr2 -> fst::expr1 = fst::expr2) as Hfst_equal by crush;
                      apply Hfst_equal; crush; clear Hfst_equal
               | [|- ?fst ++ ?expr1 = ?fst ++ ?expr2] =>
                 assert (expr1 = expr2 -> fst++expr1 = fst++expr2) as Hfst_equal by crush;
                   apply Hfst_equal; crush; clear Hfst_equal
  end.



Lemma map_deterministic : forall {A B : Type} (f : A->B) (l1 l2 : list A), l1 = l2 -> map f l1 = map f l2.
  crush.
Qed.


Lemma flatten_exp'_index: forall (e:exp) (index :nat),
(map fst (fst (flatten_exp' (S index) e))) = (map (fun x=>S x)
(map fst (fst (flatten_exp' index e)))).
Proof. induction e; mycrush. 
       first_equal. 
         repeat rewrite map_app. repeat rewrite IHe2. first_equal. repeat rewrite next_index'_index.
         crush. 
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

Lemma first_is_index' : forall e index h t,
h::t=(fst (flatten_exp' index e)) -> index = fst h.
induction e; mycrush.
Qed.

Lemma last_default_irrelevant : forall (n a:nat)( l:list nat),
  last (n::l) a = last (n::l) n.
Proof. induction l; crush. destruct l; auto.
Qed.

Lemma last_default_irrelevant' : forall (b n a:nat)( l:list nat),
  last (n::l) a = last (n::l) b.
Proof. induction l; crush. destruct l; auto.
Qed.


Lemma seq_concat_h: forall l1 n1 n2,
  is_sequential (n1::l1) 
   -> is_sequential ((n1::l1)++[next_index' n2 (n1::l1) ]).

Proof.
  induction l1 as [|l1' a]; crush.
  destruct a. simpl. split. compute. auto. auto.
  Ltac reassociate_list := match goal with
                             | [ |- context [(?n::?a) ++ ?e] ] => replace ((n::a) ++ e) with (n :: (a ++ e)) by (crush; tauto)
                             | [ |- context [?n::?a ++ ?e] ] => replace (n::a ++ e) with ((n :: a) ++ e) by (crush; tauto)
                           end.
  Ltac reassociate_list_in := match goal with
                             | [ H: context [(?n::?a) ++ ?e] |- _] => replace ((n::a) ++ e) with (n :: (a ++ e)) in H by (crush; tauto)
                             | [ H: context [?n::?a ++ ?e] |- _ ] => replace (n::a ++ e) with ((n :: a) ++ e) in H by (crush; tauto)
                              end.
  Ltac next_index_machinery := match goal with
                                 | [H : context [next_index' _ _ ] |- _] => unfold next_index' in H
                                 | [|- context [next_index' _ _ ] ] => unfold next_index' 
                                 | [|- context [(last_index _ _)] ] => unfold last_index
                                 | [H : context [last_index _ _ ] |- _ ] => unfold last_index in H
                                 | [|- context [last (?a::?b::?tl)]] => repeat rewrite last_drop_head
                                 | [H : context [last (?a::?b::?tl)] |- _] => repeat rewrite last_drop_head in H
                               end.
  reassociate_list.
  split.
  * tauto.
  * repeat next_index_machinery.
    specialize (IHa (S n1) n1 H1). reassociate_list_in. 
    rewrite (last_default_irrelevant' n). rewrite (last_default_irrelevant' n) in IHa. 
    crush. 
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

Ltac use_flatten_exp'_index := match goal with
  | [ |- context [map fst (fst (flatten_exp' (S ?index) ?e))]] => repeat rewrite flatten_exp'_index; crush
  | [ H : context [map fst (fst (flatten_exp' (S ?index) ?e))] |- _ ] => repeat rewrite flatten_exp'_index in H; crush
end.

Lemma sequential_cons : forall a l1, (is_sequential (a::l1)) -> (is_sequential l1). induction l1; crush. Qed.

Lemma flatten_exp'_never_empty: forall n e, [] = fst (flatten_exp' n e) -> False.
  induction e; mycrush.
Qed.

Lemma flatten_exp'_never_empty': forall n e, [] = map fst (fst (flatten_exp' n e)) -> False.
  induction e; mycrush.
Qed.

Ltac empty_flatten := match goal with
                        | [H : [] = fst (flatten_exp' ?n ?e) |- _] =>
                          apply flatten_exp'_never_empty in H
                        | [H : [] = map fst (fst (flatten_exp' ?n ?e)) |- _] =>
                          apply flatten_exp'_never_empty' in H
                      end; crush; tauto .

Ltac normalize_map := repeat rewrite map_app; repeat rewrite map_cons.

Ltac first_index Hnew Hevidence := match goal with
                      | [H : ?p :: ?l = fst (flatten_exp' ?n ?e2) |- _] =>
                        assert (fst p = n) as Hnew by (symmetry; apply (first_is_index' _ _ _ _ Hevidence); tauto )
                      | [H : ?p :: ?l = map fst (fst (flatten_exp' ?n ?e2)) |- _] =>
                        assert (p = n) as Hnew by (symmetry; apply (first_is_index _ _ _ _ Hevidence); tauto )
                         end.


Ltac app_nil := match goal with | [|- context [?e ++ []] ] => replace (e ++ []) with e by crush end. 

Lemma flatten_exp'_sequential : forall e index ,
  is_sequential (map fst (fst (flatten_exp' index e))).
Proof.
  Ltac simple_subcase l Heql := match goal with | [|- match ?expr with | [] => True | _::_ => _ end] =>
                             assert (is_sequential expr) by crush;
                               remember_destruct expr l Heql; crush; apply first_is_index in Heql; crush;
                               tauto
           end. 
  induction e; mycrush;
  try simple_subcase l Heql.
  - assert (is_sequential (map fst (fst (flatten_exp' (S index) e2)))) by crush.
    remember_destruct (fst (flatten_exp' (S index) e2)) e2l Heqe2l. crush.
    * empty_flatten.
    * normalize_map. rewrite <- app_comm_cons. first_index H0 Heqe2l. rewrite H0. 
      split; try tauto.
      match goal with | [|- is_sequential (?e :: ?a ++ ?b) ] => remember b as big_sequential end.
      assert (is_sequential big_sequential) by (rewrite Heqbig_sequential; crush).
      destruct big_sequential; try (empty_flatten; tauto).
      replace (S index :: map fst e2l) with (map fst (p :: e2l)) by crush.
      first_index H2 Heqbig_sequential. 
      subst. 
      assert (is_sequential ((S index :: map fst e2l) ++ [next_index' (S index) (S index :: map fst e2l)])) by 
          (apply seq_concat_h; rewrite map_cons in H; rewrite <- H0; assumption).
      specialize (seq_concat _ _ _ H2 H1). crush. 
Qed.

Definition flatten_exp index e := let (tmpl,var) := (flatten_exp' index e) in (List.rev tmpl, var).

Definition stupid := (0,Flat_Var (System 0)).

Lemma flatten_exp_returns_right_nat : forall e index, (snd (flatten_exp' index e)) = (System (fst (last (fst (flatten_exp' index e)) stupid ))).
  induction e; try (mycrush; tauto). intros. Admitted.


Definition next_index (index : nat) (l : list (prod nat flat_exp)) :=
  match l with
    | (n,_)::_ => S n
    | _ => S index
  end.


(* To change:   have it return the next System variable available too *)
Fixpoint declare_everything (index : nat) (l : (list (prod nat flat_exp))) (c : flat_com)  : (prod nat flat_com) :=
  ((next_index index l),
  match l return flat_com with
    | ((var,exp)::rest) => Flat_Declaration (System var) exp (snd (declare_everything index rest c))
    | [] => c
  end).


Definition index_from_var (v : var) : nat :=
  match v with
    | System n => n
    | User n => n
  end.
  
Fixpoint flatten' (index : nat) (c : com) : (prod nat flat_com) :=
  match c with
    | Return e => let (lst,ref) := flatten_exp index e in
                  declare_everything (index_from_var ref) lst (Flat_Return ref)
    | Assign_var y e => let (lst,ref) := flatten_exp index e in
                        declare_everything (index_from_var ref) lst (Flat_Assign_var y ref)
    | Assign_ptr y e => let (lst,ref) := flatten_exp index e in
                        let index' := match ref with | System x => S x | User _ => index end in
                        let (lst2,ref2) := flatten_exp index' y in
                        declare_everything (index_from_var ref2) lst
                                           (snd (declare_everything (index_from_var ref) lst2 (Flat_Assign_ptr ref2 ref)))
    | Declaration x e s => let (lst,ref) := flatten_exp index e in
                           let next_ind := next_index index lst in
                           let (_,body) := (flatten' next_ind s) in
                           declare_everything (index_from_var ref) lst (Flat_Declaration x (Flat_Var ref) body )
    | If c t e => let (lst,ref) := flatten_exp index c in
                  let next_ind := next_index index lst in
                  let (next_index, flat_t) := (flatten' next_ind t) in
                  let (_, body) := (flatten' next_index e) in
                  declare_everything (index_from_var ref) lst (Flat_If ref flat_t body )
    | While c t => let (lst,ref) := flatten_exp index c in
                   let next_ind := next_index index lst in
                   let (_, body) := flatten' next_ind t in
                   declare_everything (index_from_var ref) lst (Flat_While ref body )
    | Seq s₁ s₂ =>
      let (next_index,fst_stmt) := (flatten' index s₁) in
      let (ret_index,snd_stmt) := (flatten' next_index s₂) in
      (ret_index, Flat_Seq fst_stmt snd_stmt)
    | Skip => (index, Flat_Skip)
  end.

Definition flatten (c : com) : flat_com := snd (flatten' 0 c).

Fixpoint collect_declared_vars_com (c:com) : list var :=
  match c with
    | Declaration x e rest => x::collect_declared_vars_com rest
    | _ => []
  end.

Fixpoint collect_declared_vars_flatcom (c:flat_com) : list var :=
  match c with
    | Flat_Declaration x e rest => x::collect_declared_vars_flatcom rest
    | _ => []
  end.


Definition unique_decl_com (c:com): Prop :=
  NoDup (collect_declared_vars_com c).
Definition unique_decl_flat (c:flat_com): Prop :=
  NoDup (collect_declared_vars_flatcom c).
Fixpoint user_var_only (c:com): Prop :=
  match c with
    | Declaration x e rest =>
        match x with
          | User _ => user_var_only rest
          | System _ => False
        end
    | _ => True
  end.

Lemma flatten_unique : forall (c : com), (unique_decl_com c) -> (user_var_only c) -> unique_decl_flat (flatten c).

Admitted.


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


Fixpoint sn_flat_steps n c s :=
  match n with
    | S n' =>
      match (step_com_flat c s) with
        | Some (next_c,next_s,_) => sn_flat_steps n' next_c next_s
        | None => None
      end
    | _ => step_com_flat c s
  end.

Theorem flatten_correct : forall c s, 
                            match (step_com_fn c s) with
                              | None => True
                              | Some (cmd,s,val) =>
                                exists n,
                                match (sn_flat_steps n (flatten c) s) with
                                  | Some (cmd2,s2,val2) =>
                                    s = s2 /\ val = val2 /\ ((flatten cmd) = cmd2)
                                  | None => False
                                end
                            end.
