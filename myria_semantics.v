
Require Import Bool Arith String List CpdtTactics.
Open Scope string_scope.
Open Scope list_scope.

Import ListNotations.

Inductive flat_var : Type :=
| User : nat -> flat_var
| System : nat -> flat_var.

Definition surface_var := nat.

Inductive binop := Plus | Times | Minus | And | Or | Eq.

Inductive exp : Type := 
| Const : nat -> exp
| Var : surface_var -> exp
| Binop : exp -> binop -> exp -> exp
| Tt : exp
| Ff : exp
| Not : exp -> exp
| Deref : exp -> exp.

Inductive com : Type := 
| Skip : com
| Return : exp -> com
| Declaration : surface_var -> exp -> com -> com 
| Assign_var : surface_var -> exp -> com
| Assign_ptr : exp -> exp -> com
| Seq : com -> com -> com
| If : exp -> com -> com -> com
| While : exp -> com -> com.

Inductive value : Type :=
| Nat_value : nat -> value
| Bool_value : bool -> value
| Remote_value : flat_var -> value.
Inductive answer : Type :=
| Value : value -> answer
| TypeError : answer.

Inductive flat_exp : Type := 
| Flat_Const : nat -> flat_exp
| Flat_Var : flat_var -> flat_exp
| Flat_Binop : flat_var -> binop -> flat_var -> flat_exp
| Flat_Tt : flat_exp
| Flat_Ff : flat_exp
| Flat_Not : flat_var -> flat_exp
(*This one doesn't exist: *)| Flat_Deref : flat_var -> flat_exp.

Inductive flat_com : Type := 
| Flat_Skip : flat_com
| Flat_Return : flat_var -> flat_com
| Flat_Declaration : flat_var -> flat_exp -> flat_com -> flat_com 
| Flat_Assign_var : flat_var -> flat_var -> flat_com
| Flat_Assign_ptr : flat_var -> flat_var -> flat_com
| Flat_Seq : flat_com -> flat_com -> flat_com
| Flat_If : flat_var -> flat_com -> flat_com -> flat_com
| Flat_While : flat_var -> flat_com -> flat_com.

Inductive flat_value : Type :=
| Flat_Nat_value : nat -> flat_value
| Flat_Bool_value : bool -> flat_value
| Flat_Remote_value : flat_var -> flat_value.
Inductive flat_answer : Type :=
| Flat_Value : flat_value -> flat_answer
| Flat_TypeError : flat_answer. 

Definition local_state := flat_var -> option value.

Definition σ : local_state := (fun _ => None).

Definition remote_state := flat_var -> option value.

Definition ρ : remote_state := (fun _ => None).

Definition state := prod local_state remote_state.

Definition get_remote_flat (x:flat_var) (s:state) : option value :=
  match s with
    | (_,s') => s' x
  end.


Definition get_remote_surface (x:surface_var) (s:state) : option value :=
  get_remote_flat (User x) s.

Definition get_local_flat (x:flat_var) (s:state) : option value :=
  match s with
    | (s',_) => s' x
  end.

Definition get_local_surface (x:surface_var) (s:state) : option value :=
  get_local_flat (User x) s.


Definition get_flat (x : flat_var) (s : state) : option value :=
  match (get_local_flat x s) with
    | Some y => Some y
    | None => get_remote_flat x s
  end.

Definition get_surface (x : surface_var) (s : state) : option value :=
  get_flat (User x) s.


Definition set_remote_flat (x:flat_var) (n:value) (s':state) : state :=
  match s' with
    | (l,s) =>  (l,
                 (fun y =>
                    match (x,y) with
                      | (User x', User y') => if Nat.eqb x' y' then Some n else get_flat y s'
                      | (System x', System y') => if Nat.eqb x' y' then Some n else get_flat y s'
                      | _ => get_flat y s'
                    end))
    end.

Definition set_remote_surface (x:surface_var) (n:value) (s':state) : state :=
  set_remote_flat (User x) n s'.


Definition set_local_flat (x:flat_var) (n:value) (s':state) : state :=
  match s' with
    | (s,r) =>  (
        (fun y =>
           match (x,y) with
             | (User x', User y') => if Nat.eqb x' y' then Some n else get_flat y s'
             | (System x', System y') => if Nat.eqb x' y' then Some n else get_flat y s'
             | _ => get_flat y s'
           end),r)
  end.

Definition set_local_surface (x:surface_var) (n:value) (s':state) : state :=
  set_local_flat (User x) n s'.

Definition set_flat (x:flat_var) (n:value) (s:state) : state :=
  match (get_local_flat x s) with
    | Some _ => set_local_flat x n s
    | None => (match get_remote_flat x s with
                 | Some _ => set_remote_flat x n s
                 | None => set_local_flat x n s
              end)
  end.

Definition set_surface (x : surface_var) (n : value) ( s : state) : state :=
  set_flat (User x) n s.

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
    | Var x => match (get_surface x s) with
                 | Some e => ret e
                 | None => TypeError
               end
    | Deref e =>
      match (eval_exp e s) with
        | Value (Remote_value x) =>
          match (get_flat x s) with | None => TypeError
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

Definition is_declared_flat (x : flat_var) s :=
  match (get_flat x s) with | Some _ => true | None => false end.

Definition is_declared_surface (x : surface_var) s :=
  is_declared_flat (User x) s.

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
      match (is_declared_surface x s) with
        | true => None
        | false =>
          match (eval_exp e s) with
            | Value ans => Some (next , (set_surface x ans s), None)
            | TypeError => None
          end
      end
    | Assign_var x e => if (is_declared_surface x s)
                             && (type_matches_op (ret_op (get_surface x s)) (Some (eval_exp e s)))
                        then
                          match (eval_exp e s) with
                            | Value ans => Some (Skip , (set_local_surface x ans s), None)
                            | TypeError => None
                          end
                        else None
    | Assign_ptr x' e => match (eval_exp x' s) with
                           | Value (Remote_value x) =>
                             if (is_declared_flat x s)
                                  && (type_matches_op (ret_op (get_flat x s)) (Some (eval_exp e s)))
                             then
                               match (eval_exp e s) with
                                 | Value ans => Some (Skip , (set_remote_flat x ans s), None)
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
Fixpoint flatten_exp' (index : nat) (e : exp) : prod (list (prod nat flat_exp)) nat
  := match e with 
       | Var x => ((index,Flat_Var (User x))::[],index)
       | Binop e₁ op e₂ =>
         let (decls_e2, ref_e2) := (flatten_exp' (S index) e₂) in
         let (decls_e1, ref_e1) := ((flatten_exp' (next_index' (S index) (map fst decls_e2)) e₁)) in
         let binop_decl := (index, Flat_Binop (System ref_e1) op (System ref_e2)) in
         ( binop_decl :: decls_e2 ++ decls_e1, index)
       | Not e =>
         ((match (flatten_exp' (S index) e) with
             | (decls,ref) => (index, (Flat_Not (System ref)))::decls
           end), index)
       | Const x => ((index,Flat_Const x)::[],index)
       | Tt => ((index,Flat_Tt)::[],index)
       | Ff => ((index,Flat_Ff)::[],index)
       | Deref e =>
         (match (flatten_exp' (S index) e) with
           | (decls,ref) => (index,(Flat_Deref (System ref)))::decls
         end, index)
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

Lemma last_default_irrelevant : forall {A} (n a: A)( l:list A),
  last (n::l) a = last (n::l) n.
Proof. induction l; crush. destruct l; auto.
Qed.

Lemma last_default_irrelevant' : forall {A} (b n a: A)( l:list A),
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

Definition flatten_exp index e := let (tmpl,var) := (flatten_exp' index e) in (List.rev tmpl, System var).

Definition stupid index := (index,Flat_Var (System index)).


Ltac destruct_match :=
  match goal with
    | [|- context [match ?e with | [] => _ | _::_ => _ end] ] =>
      remember e as match_expr; destruct match_expr
  end.

Eval compute in (flatten_exp' 0 (Binop Tt Or (Binop (Not (Not Tt)) And Ff))).

Eval compute in (flatten_exp' 0 (Not (Not (Tt)))).

Lemma flatten_exp'_returns_right_nat : forall e index, (snd (flatten_exp' index e)) = (fst (hd (stupid index) (fst (flatten_exp' index e)) )).
  induction e; mycrush.
Qed.

Ltac remove_ctr Ctr := match goal with
                         | [|- Ctr ?e1 = Ctr ?e2] =>
                           assert ((e1 = e2) -> (Ctr e1 = Ctr e2)) as Hremove_ctr by crush;
                             apply Hremove_ctr; clear Hremove_ctr
                       end.

Lemma nil_app_comm : forall {A : Type} (l1 l2 : list A), ([] = l1 ++ l2) -> ([] = l2 ++ l1).
  induction l1; induction l2; crush.
Qed.

Lemma last_is_last : forall {A : Type} (l : list A) (a d: A), last (l ++ [a]) d = a.
  induction l; crush. destruct_match; crush. apply nil_app_comm in Heqmatch_expr. crush. 
Qed.

Lemma last_rev_is_fst : forall {A} (l : list A) (d : A), (last (rev l) d) = (hd d l).
  induction l; try (crush; tauto).
  intros. crush. rewrite last_is_last. crush. 
Qed.


Lemma flatten_exp_returns_right_nat : forall e index, (snd (flatten_exp index e)) = (System (fst (last (fst (flatten_exp index e)) (stupid index) ))).
  intros. unfold flatten_exp. mycrush.
  rewrite last_rev_is_fst.
  remove_ctr System. apply flatten_exp'_returns_right_nat. 
Qed.

Lemma rev_map_combine : forall {A B : Type} (l : list A) (f : A -> B), (rev (map f (rev l ) )) = (map f l).
  intros. rewrite map_rev. rewrite rev_involutive. tauto.
Qed.

Lemma flatten_exp_sequential : forall e index ,
                                 is_sequential (rev (map fst (fst (flatten_exp index e)))).
  unfold flatten_exp. mycrush. normalize_map. rewrite rev_map_combine. apply flatten_exp'_sequential.
Qed.

Fixpoint system_bound_in (v : flat_var) (l : list (prod nat flat_exp)) : bool :=
  match v with
      | System var =>  
        match l with
          | [] => false
          | (var',_)::tl => (Nat.eqb var var') || (system_bound_in v tl)
        end 
      | User _ => true
  end.

Definition bound_system_exp (e : flat_exp) (l : list (prod nat flat_exp)) : bool := 
  match e with
    | Flat_Const _ => true
    | Flat_Tt => true
    | Flat_Ff => true
    | Flat_Var var => system_bound_in var l
    | Flat_Not var => system_bound_in var l
    | Flat_Deref var => system_bound_in var l
    | Flat_Binop var1 op var2 => ((system_bound_in var1 l) && (system_bound_in var2 l))
  end.

Lemma destruct_system_bound_in: forall f (l1 : list (nat * flat_exp)) (hd : nat * flat_exp),
                                  system_bound_in f [hd] || system_bound_in f l1 = system_bound_in f (hd :: l1).
  destruct f.
  - crush.
  - induction l1.
    * crush; tauto.
    * intros. simpl. remember_destruct hd hd' hd'eq. remember_destruct a a' a'eq. remember_destruct' (n =? n0); tauto.
Qed.

Lemma destruct_system_bound_in': forall f (l1 : list (nat * flat_exp)) (hd : nat * flat_exp),
                                  (system_bound_in f [hd] && system_bound_in f l1 = true ) -> (system_bound_in f (hd :: l1) = true).
  intros. rewrite <- destruct_system_bound_in. apply andb_true_iff in H. destruct H; rewrite H; rewrite H0; tauto.
Qed. 

Ltac bool_identity := repeat match goal with
                              | [|- context [true && ?e] ] => replace (true && e) with e by crush
                              | [|- context [?e && true] ] => replace (e && true) with (e) by (rewrite andb_comm; crush; tauto)
                              | [|- context [false || ?e] ] => replace (false || e) with e by crush
                              | [|- context [?e || false] ] => replace (e || false) with (e) by (rewrite orb_comm; crush; tauto)
                              | [|- context [false && ?e] ] => replace (true && e) with false by crush
                              | [|- context [?e && false] ] => replace (e && false) with (false) by (rewrite andb_comm; crush; tauto)
                              | [|- context [true || ?e] ] => replace (true || e) with true by crush
                              | [|- context [?e || true] ] => replace (e || true) with (true) by (rewrite orb_comm; crush; tauto)
                            end.

Lemma induct_bound_system_exp: forall e hd l1, ((bound_system_exp e l1) = true) -> ((bound_system_exp e (hd :: l1)) = true).
  induction e; intros; try (simpl; tauto);
  try (specialize (destruct_system_bound_in f l1 hd); crush; tauto);
  intros; unfold bound_system_exp; unfold bound_system_exp in H; 
  try (rewrite <- destruct_system_bound_in; rewrite H; rewrite orb_true_r; tauto).
  - symmetry in H. apply andb_true_eq in H. destruct H. rewrite <- destruct_system_bound_in. rewrite andb_comm. rewrite <- destruct_system_bound_in.
    rewrite <- H. rewrite <- H0. bool_identity. tauto.
Qed.


Lemma list_sizes_match' : forall {A: Type} (l hd tl : A) (mid : list A), [l] = hd :: mid ++ [tl] -> False.
  induction mid; crush.
Qed.

Lemma mid_cons_nonempty : forall {A : Type} (a c: list A) (b : A), ([] = a ++ b :: c) -> False.
  induction a; crush.
Qed.
                                                  
Lemma empty_lists : forall {A : Type} (pre post : list A) (lft mid : A), ([lft] = (pre ++ mid :: post)) -> (pre = []) /\ (post = []).
  intro A. 
  specialize (@mid_cons_nonempty A). 
  induction pre; crush.
Qed.

Lemma empty_rev : forall {A : Type} (l : list A) , ([] = rev l) -> ([] = l).
  intros. destruct l.
  - tauto.
  - simpl in H. apply mid_cons_nonempty in H. exfalso; tauto.
Qed.

Lemma flatten_exp_exp'_relate : forall index e, (rev (fst (flatten_exp' index e)) = fst (flatten_exp index e)).
  intros. unfold flatten_exp. mycrush. Qed.

Lemma flatten_system_exp_all_bound : forall e interim l1 l2 index, (fst((flatten_exp index e)) = (l1 ++ interim ::l2)) ->  ((bound_system_exp (snd interim) l1) = true).
  specialize (@empty_lists (nat * flat_exp) ).
  specialize (@mid_cons_nonempty (nat * flat_exp) ).
  specialize (@list_sizes_match' (nat * flat_exp)).
  Ltac empty_lists := match goal with
                        | [H : [?a] = ?l1 ++ ?e :: ?l2 |- _] =>
                          assert (l1 = []) by (induction l1; crush); subst;
                          assert (l2 = []) by (induction l2; crush); subst;
                          assert (a = e) by crush; subst;
                          clear H
                        | [H : [?a] = ?e :: ?l2 |- _] =>
                          assert (l2 = []) by (induction l2; crush); subst;
                          assert (a = e) by crush; subst;
                          clear H
                        | [H : [?a] = ?l1 ++ [?e] |- _] =>
                          assert (l1 = []) by (induction l1; crush); subst;
                          assert (a = e) by crush; subst;
                          clear H
                        | [H : context [[] ++ ?e] |- _] => replace ([] ++ e) with e in H by crush
                        | [H : [] = rev ?l |- _] => apply (empty_rev l) in H
                      end.
  Ltac split_context_pair := match goal with
                               | [H : (?a,?b) = (?a',?b') |- _] => assert (a = a') by crush; assert (b = b') by crush; clear H
                             end.
  Ltac list_head_equal := match goal with | [H : ?hd::?tl = ?hd'::?tl' |- _] => assert (hd = hd') by crush; assert (tl = tl') by crush end.
  Ltac clear_reflexives := match goal with | [H : ?e = ?e |- _] => clear H end.
  Ltac generalize4 b a index l2 := generalize dependent b; generalize dependent a; generalize dependent index; generalize dependent l2.
  induction e; mycrush;
  (*trivial case*) try (empty_lists; split_context_pair; crush; tauto).
  - admit.
  - generalize4 b a index l2.  induction l1.
    * intros. simpl in H2. remember_destruct (rev (fst (flatten_exp' (S index) e))) l2' l2'def.
      + repeat empty_lists. empty_flatten.
      + simpl in H2. list_head_equal. subst. clear_reflexives. specialize (IHe (a,b) [] l2' (S index) ). simpl in IHe.
      rewrite flatten_exp_exp'_relate in l2'def. symmetry in l2'def. apply IHe in l2'def. tauto.
    * intros. remember_destruct (rev (fst (flatten_exp' (S index) e))) l2' l2'def.
      + repeat empty_lists. empty_flatten.
      + simpl in H2. list_head_equal. subst. apply induct_bound_system_exp. clear H. clear H0. clear H1. 
        reassociate_list_in. rewrite l2'def in H2. symmetry in l2'def.
        rewrite flatten_exp_exp'_relate in l2'def. assert (bound_system_exp (snd a) [] = true) by (apply (IHe a [] l2' (S index)) in l2'def; tauto).
        
        
  - admit. (*looks like above*)

Admitted.


Definition next_index (index : nat) (l : list (prod nat flat_exp)) :=
  match l with
    | (n,_)::_ => S n
    | _ => S index
  end.


Fixpoint declare_everything (index : nat) (l : (list (prod nat flat_exp))) (c : flat_com)  : (prod nat flat_com) :=
  ((next_index index l),
  match l return flat_com with
    | ((var,exp)::rest) => Flat_Declaration (System var) exp (snd (declare_everything index rest c))
    | [] => c
  end).


Definition index_from_var (v : flat_var) : nat :=
  match v with
    | System n => n
    | User n => n
  end.
  
Fixpoint flatten' (index : nat) (c : com) : (prod nat flat_com) :=
  match c with
    | Return e => let (lst,ref) := flatten_exp index e in
                  declare_everything (index_from_var ref) lst (Flat_Return ref)
    | Assign_var y e => let (lst,ref) := flatten_exp index e in
                        declare_everything (index_from_var ref) lst (Flat_Assign_var (User y) ref)
    | Assign_ptr y e => let (lst,ref) := flatten_exp index e in
                        let index' := match ref with | System x => S x | User _ => index end in
                        let (lst2,ref2) := flatten_exp index' y in
                        declare_everything (index_from_var ref2) lst
                                           (snd (declare_everything (index_from_var ref) lst2 (Flat_Assign_ptr ref2 ref)))
    | Declaration x e s => let (lst,ref) := flatten_exp index e in
                           let next_ind := next_index index lst in
                           let (_,body) := (flatten' next_ind s) in
                           declare_everything (index_from_var ref) lst (Flat_Declaration (User x) (Flat_Var ref) body )
      (*recursively calls flatten'*)
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

Fixpoint collect_declared_vars_com (c:com) : list surface_var :=
  match c with
    | Declaration x e rest => x::collect_declared_vars_com rest
    | _ => []
  end.

Fixpoint collect_declared_vars_flatcom (c:flat_com) : list flat_var :=
  match c with
    | Flat_Declaration x e rest => x::collect_declared_vars_flatcom rest
    | _ => []
  end.


Definition unique_decl_com (c:com): Prop :=
  NoDup (collect_declared_vars_com c).
Definition unique_decl_flat (c:flat_com): Prop :=
  NoDup (collect_declared_vars_flatcom c).

Lemma declare_everything_is_union:
forall (x index:nat) (l : (list (prod nat flat_exp)))(c:flat_com),

In (System x)
       (collect_declared_vars_flatcom
          (snd (declare_everything index l c)))->(~ In x (map fst l))->
(In (System x) (collect_declared_vars_flatcom c)).
Proof. induction l; mycrush. Qed.

Lemma declare_everything_unique: forall (index : nat) (l : (list (prod nat flat_exp))) (c : flat_com), 
NoDup (map fst l)->unique_decl_flat c -> (forall x, In x (map fst l)-> ~In (System x) (collect_declared_vars_flatcom c))->
unique_decl_flat (snd (declare_everything index l c)).
Proof. induction l; crush. unfold unique_decl_flat.
  unfold collect_declared_vars_flatcom. fold collect_declared_vars_flatcom.
  apply NoDup_cons. 
  - crush. apply H1 with (x:=a0). auto. unfold not.
    rename l into l0. rename index into index0.
    apply declare_everything_is_union with (index:=index0)(l:=l0);auto.
    rewrite NoDup_cons_iff in H; crush.
    
  - apply IHl.
    Focus 3. intros. assert(a0 = x \/ In x (map fst l)). crush.
    apply H1 in H4. auto. auto.
  rewrite NoDup_cons_iff in H. crush. auto.
Qed. 

Lemma collect_declare_everything: 
 forall (index : nat) (l : (list (prod nat flat_exp))) (c : flat_com),
  collect_declared_vars_flatcom (snd (declare_everything index l c))
  = (map (fun x=> System x) (map fst l) ) ++ collect_declared_vars_flatcom c.
Proof. induction l; mycrush.
Qed.




Lemma flatten'_index_increase: forall c x index, 
  In (System x) (collect_declared_vars_flatcom (snd (flatten' index c)))
  -> index <= x.

Proof. induction c; mycrush.
- rewrite collect_declare_everything in H. apply in_app_or in H.
  unfold collect_declared_vars_flatcom in H.  admit.
- rewrite collect_declare_everything in H. apply in_app_or in H.
  unfold collect_declared_vars_flatcom in H.
  fold collect_declared_vars_flatcom in H.
Admitted. 


Lemma sequential_is_seq: forall l a, is_sequential (a::l)
-> seq a (length (a::l)) = a::l.
Proof. induction l; crush.
Qed.


Lemma sequential_nodup: forall l, is_sequential l -> NoDup l.
Proof. Hint Constructors NoDup. destruct l. intro; auto.
      intro. apply sequential_is_seq in H. rewrite <- H.
      apply seq_NoDup.
Qed.
  

Lemma flatten_unique : forall (c : com)(index:nat), (unique_decl_com c) -> unique_decl_flat (snd (flatten' index c)).
Hint Constructors NoDup.
Proof. induction c; mycrush; try (unfold unique_decl_flat; mycrush; tauto). 
  - apply declare_everything_unique.
    + admit. (*follows from sequential*)
    + unfold unique_decl_flat.
      unfold collect_declared_vars_flatcom. auto .
    + unfold collect_declared_vars_flatcom. intros. auto.
  -  
    apply declare_everything_unique.
    + admit.
    + unfold unique_decl_flat. unfold collect_declared_vars_flatcom.
    fold collect_declared_vars_flatcom. 
    unfold unique_decl_com in H. 
    unfold flatten in IHc. unfold unique_decl_com in IHc.
    (*need: user variables are the same before and after flatten*)
    admit.
  +
  unfold collect_declared_vars_flatcom.
  fold collect_declared_vars_flatcom.
  intros. unfold not. intro H2. destruct H2. congruence.
  apply flatten'_index_increase in H1.
  (*flatten_exp property*) admit. 
  - apply declare_everything_unique.
    + admit.
    + unfold unique_decl_flat.
      unfold collect_declared_vars_flatcom. auto.
    + unfold  collect_declared_vars_flatcom. intros. auto.
  - apply declare_everything_unique.
    + admit.
    + apply declare_everything_unique.
      * admit.
      * unfold unique_decl_flat.
        unfold collect_declared_vars_flatcom. auto.
      * unfold  collect_declared_vars_flatcom. intros. auto.
    + unfold collect_declared_vars_flatcom.
  fold collect_declared_vars_flatcom.
  intros. unfold not. intro. rewrite collect_declare_everything in H1. admit. (*need statement about flatten_exp*)
  - apply declare_everything_unique.
    + admit.
    + unfold unique_decl_flat.
      unfold collect_declared_vars_flatcom. auto.
    +  unfold  collect_declared_vars_flatcom. intros. auto.
  - apply declare_everything_unique.
    + admit.
    + unfold unique_decl_flat.
      unfold collect_declared_vars_flatcom. auto.
    + unfold  collect_declared_vars_flatcom. intros. auto.
Admitted.


Fixpoint eval_flat_exp (e:flat_exp) (s:state) : answer := 
  match e with 
    | Flat_Const n => ret (Nat_value n)
    | Flat_Var x => match (get_flat x s) with
                      | Some e => ret e
                      | None => TypeError
                    end
    | Flat_Deref x =>
      match (get_flat x s) with
        | Some (Remote_value x) =>
          match (get_flat x s) with | None => TypeError
                            | Some a => ret a
          end
        | _ => TypeError
      end
    | Flat_Binop e1 b e2 =>
      match (get_flat e1 s) with
        | Some (Nat_value _fst) =>
          match (get_flat e2 s) with
            | Some (Nat_value _snd) => ret (Nat_value ((eval_binop b) _fst _snd))
            | _ => TypeError
          end
        | _ => TypeError
      end
    | Flat_Tt => ret (Bool_value true)
    | Flat_Ff => ret (Bool_value false)
    | Flat_Not b =>
      match (get_flat b s) with
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
    | Flat_Return x => match (get_flat x s) with
                         | Some ans => Some (Flat_Skip, s, Some ans)
                         | None => None
                       end
    | Flat_Declaration x e next =>
      match (is_declared_flat x s) with
        | true => None
        | false =>
          match (eval_flat_exp e s) with
            | Value ans => Some (next , (set_flat x ans s), None)
            | TypeError => None
          end
      end
    | Flat_Assign_var x y =>
      match (get_flat x s) with
        | None => None
        | Some ans => 
          if (is_declared_flat x s)
          then
            match (get_flat y s) with
              | Some ans => Some (Flat_Skip , (set_local_flat x ans s), None)
              | None => None
            end
          else None
      end
    | Flat_If condition thn els =>
      match (get_flat condition s) with
        | Some (Bool_value true) => Some (thn, s, None)
        | Some (Bool_value false) => Some (els, s, None)
        | _ => None
      end
    | Flat_While condition thn => Some ((Flat_If condition (Flat_Seq thn cmd) Flat_Skip), s, None)
    | Flat_Assign_ptr x' e => match (get_flat x' s) with
                                | Some (Remote_value x) =>
                                  if (is_declared_flat x s)
                                  then
                                    match (get_flat e s) with
                                      | Some ans => Some (Flat_Skip , (set_remote_flat x ans s), None)
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
