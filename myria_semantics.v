
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

Definition hd_exists {A : Type} (l : list A) (pf : 1 <= length l ) : (exists (a : A), (hd_error l = Some a)).
  induction l; crush.
  destruct l; crush; exists a; crush.
  Qed. 

Definition hd_pf {A : Type} (l : list A) {pf : 1 <= length l } : A. 
Proof.
  refine (match l with
            | hd :: tl => hd
            | [] => _
         end). 
  induction l; crush.
Qed. 

Eval compute in (hd_pf ([0]) ) + 4. 

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

Lemma last_drop_head: forall {A:Type}(l: list A)(a n0 n:A),
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
                        | [H : fst (flatten_exp' ?n ?e) = [] |- _] =>
                          symmetry in H; apply flatten_exp'_never_empty in H
                        | [H : [] = fst (flatten_exp' ?n ?e) |- _] =>
                          apply flatten_exp'_never_empty in H
                        | [H : [] = map fst (fst (flatten_exp' ?n ?e)) |- _] =>
                          apply flatten_exp'_never_empty' in H
                        | [H : map fst (fst (flatten_exp' ?n ?e)) = [] |- _] =>
                          symmetry in H; 
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

Definition immediate_variables (e : flat_exp) := 
  match e with
    | Flat_Const _ => []
    | Flat_Tt => []
    | Flat_Ff => []
    | Flat_Var var => [var]
    | Flat_Not var => [var]
    | Flat_Deref var => [var]
    | Flat_Binop var1 op var2 => [var1;var2]
  end.

Lemma system_bound_in_is_in : forall v l, ((system_bound_in v l) = true) <-> (In v (map (fun x => System (fst x)) l) ).

  Admitted. 

  Lemma bound_system_exp_in: forall e l, ((bound_system_exp e l) = true) <->
                                         (forall v, (In v (immediate_variables e)) -> (In v (map (fun x => System (fst x)) l) )).
    Admitted. 

Lemma destruct_system_bound_in: forall f (l1 : list (nat * flat_exp)) (hd : nat * flat_exp),
                                  system_bound_in f [hd] || system_bound_in f l1 = system_bound_in f (hd :: l1).
  destruct f.
  - crush.
  - induction l1.
    * crush; tauto.
    * intros. simpl. remember_destruct hd hd' hd'eq. remember_destruct a a' a'eq. remember_destruct' (n =? n0); tauto.
Qed.

Lemma system_bound_in_user_tautology : forall n (l : list (nat * flat_exp)), ((system_bound_in (User n) l) = true).
  induction l; crush.
Qed.

Lemma system_bound_in_reorder : forall v l hd, (system_bound_in v (hd :: l) = system_bound_in v (l ++ [hd])).
  destruct v.
  - intros. repeat rewrite system_bound_in_user_tautology. tauto.
  - induction l.
    * crush; tauto.
    * intros. simpl. crush. remember_destruct' (n =? a); remember_destruct' (n =? a0).
    + tauto.
    + simpl. specialize (IHl (a,b0)). simpl in IHl. rewrite <- Heqtmpname in IHl. crush.
    + simpl. tauto.
    + simpl. specialize (IHl (a,b0)). simpl in IHl. rewrite <- Heqtmpname in IHl. simpl in IHl. crush. 
Qed.


Ltac reflexive_nateq_left := apply orb_true_intro; left; symmetry; apply beq_nat_refl. 

Lemma system_bound_in_itself : forall l1 l2 p, system_bound_in (System (fst p)) (l1 ++ p :: l2) = true.
  induction l1; mycrush; reflexive_nateq_left.
Qed.

Lemma system_bound_in_itself' : forall l1 l2 pl pr, system_bound_in (System pl) (l1 ++ (pl,pr) :: l2) = true.
  induction l1; mycrush; reflexive_nateq_left.
Qed.

Lemma destruct_system_bound_in_rev: forall f (l1 : list (nat * flat_exp)) (tl : nat * flat_exp),
                                  system_bound_in f [tl] || system_bound_in f l1 = system_bound_in f (l1 ++ [tl]).
  intros. rewrite <- system_bound_in_reorder. apply destruct_system_bound_in. 
Qed.

Lemma destruct_system_bound_in': forall f (l1 : list (nat * flat_exp)) (hd : nat * flat_exp),
                                  (system_bound_in f [hd] && system_bound_in f l1 = true ) -> (system_bound_in f (hd :: l1) = true).
  intros. rewrite <- destruct_system_bound_in. apply andb_true_iff in H. destruct H; rewrite H; rewrite H0; tauto.
Qed. 

Ltac bool_identity := simpl; repeat match goal with
                              | [|- context [true && ?e] ] => replace (true && e) with e by crush
                              | [|- context [?e && true] ] => replace (e && true) with (e) by (rewrite andb_comm; crush; tauto)
                              | [|- context [false || ?e] ] => replace (false || e) with e by crush
                              | [|- context [?e || false] ] => replace (e || false) with (e) by (rewrite orb_comm; crush; tauto)
                              | [|- context [false && ?e] ] => replace (true && e) with false by crush
                              | [|- context [?e && false] ] => replace (e && false) with (false) by (rewrite andb_comm; crush; tauto)
                              | [|- context [true || ?e] ] => replace (true || e) with true by crush
                              | [|- context [?e || true] ] => replace (e || true) with (true) by (rewrite orb_comm; crush; tauto)
                                    end.

Lemma system_bound_in_strong_reorder : forall v l1 l2, (system_bound_in v (l1 ++ l2) = system_bound_in v (l2 ++ l1)).
  destruct v.
  - intros. repeat rewrite system_bound_in_user_tautology. tauto.
  - induction l1; induction l2; mycrush.
    * destruct a. replace (l2 ++ (n0, f) :: l1) with ((l2 ++ [(n0, f)]) ++ l1) by crush.
      rewrite <- (IHl1 (l2 ++ [(n0,f)])). rewrite app_assoc. rewrite <- system_bound_in_reorder.
      rewrite <- destruct_system_bound_in. mycrush. bool_identity. repeat rewrite orb_assoc.
      replace ((n =? n0) || (n =? a1)) with ((n =? a1) || (n =? n0)). tauto.
      rewrite orb_comm. tauto.
Qed.

Lemma induct_bound_system_exp: forall e hd l1, ((bound_system_exp e l1) = true) -> ((bound_system_exp e (hd :: l1)) = true).
  induction e; intros; try (simpl; tauto);
  try (specialize (destruct_system_bound_in f l1 hd); crush; tauto);
  intros; unfold bound_system_exp; unfold bound_system_exp in H; 
  try (rewrite <- destruct_system_bound_in; rewrite H; rewrite orb_true_r; tauto).
  - symmetry in H. apply andb_true_eq in H. destruct H. rewrite <- destruct_system_bound_in. rewrite andb_comm. rewrite <- destruct_system_bound_in.
    rewrite <- H. rewrite <- H0. bool_identity. tauto.
Qed.

Lemma bound_system_exp_reorder : forall e a l1, (bound_system_exp e (a :: l1)) = (bound_system_exp e (l1 ++ [a])).
  induction e; try (mycrush; tauto); intros;
  destruct f; mycrush; try (rewrite system_bound_in_user_tautology; tauto); repeat rewrite <- system_bound_in_reorder; mycrush.
Qed. 
  
Lemma bound_system_exp_strong_reorder : forall e l1 l2, (bound_system_exp e (l1 ++ l2)) = (bound_system_exp e (l2 ++ l1)).
  induction e; mycrush;
  try (destruct f; mycrush; try (repeat rewrite system_bound_in_user_tautology; tauto); rewrite <- system_bound_in_strong_reorder; tauto).
  - destruct f; destruct f0; repeat rewrite system_bound_in_user_tautology.
    * tauto.
    * rewrite <- system_bound_in_strong_reorder; tauto.
    * rewrite <- system_bound_in_strong_reorder; tauto.
    * rewrite <- system_bound_in_strong_reorder.
      replace (system_bound_in (System n0) (l2 ++ l1)) with (system_bound_in (System n0) (l1 ++ l2)).
    + tauto.
    + rewrite system_bound_in_strong_reorder. tauto.
Qed. 

Lemma strong_induct_bound_system_exp: forall e l1 l2, ((bound_system_exp e l1) = true) -> ((bound_system_exp e (l1 ++ l2)) = true).
  induction l1 using rev_ind; induction l2 using rev_ind; mycrush.
  - rewrite <- bound_system_exp_reorder. apply induct_bound_system_exp; crush.
  - replace (l1 ++ x::l2 ++ [(a,b)]) with ((l1 ++ x::l2) ++ [(a,b)]) by crush. rewrite <- bound_system_exp_reorder. apply induct_bound_system_exp; crush.
Qed.

Fixpoint bound_exp (env : list surface_var) (e : exp) : Prop := 
match e with 
| Const _ => True
| Var v => In v env
| Binop e1 _ e2 => (bound_exp env e1) /\ (bound_exp env e2)
| Tt => True
| Ff => True
| Not e => (bound_exp env e)
| Deref e=> (bound_exp env e)
end.


Fixpoint bound_com' (env : list surface_var) c := 
match c with 
| Skip => True
| Return e => (bound_exp env e)
| Declaration v e c => (bound_exp env e) /\ (bound_com' (v::env) c)
| Assign_var v e => (In v env) /\ (bound_exp env e)
| Assign_ptr v e=> (bound_exp env v) /\ (bound_exp env e)
| Seq c1 c2 => (bound_com' env c1) /\ (bound_com' env c2)
| If c t e => (bound_exp env c) /\ (bound_com' env t) /\ (bound_com' env e)
| While c t => (bound_exp env c) /\ (bound_com' env t)
end.

Definition bound_com c := bound_com' [] c.

Fixpoint bound_flat_exp (env : list flat_var) (e : flat_exp) : Prop := 
match e with 
| Flat_Const _ => True 
| Flat_Var v => In v env
| Flat_Binop e1 _ e2 => (In e1 env) /\ (In e2 env)
| Flat_Tt => True
| Flat_Ff => True
| Flat_Not e => (In e env)
| Flat_Deref e => (In e env)
end.

Fixpoint bound_flat_com' (env : list flat_var) c :=
  match c with 
    | Flat_Skip => True 
    | Flat_Return v => (In v env)
    | Flat_Declaration v e s => (bound_flat_exp env e) /\ (bound_flat_com' (v::env) s)
    | Flat_Assign_var v1 v2 => (In v1 env) /\ (In v2 env)
    | Flat_Assign_ptr v1 v2 => (In v1 env) /\ (In v2 env)
    | Flat_Seq c1 c2 => (bound_flat_com' env c1) /\ (bound_flat_com' env c2)
    | Flat_If c t e => (In c env) /\ (bound_flat_com' env t) /\ (bound_flat_com' env e)
    | Flat_While c t => (In c env) /\ (bound_flat_com' env t)
  end.

Fixpoint bound_flat_com c := bound_flat_com' [] c.

Lemma list_sizes_match' : forall {A: Type} (l hd tl : A) (mid : list A), [l] = hd :: mid ++ [tl] -> False.
  induction mid; crush.
Qed.

Lemma mid_cons_nonempty : forall {A : Type} (a c: list A) (b : A), ([] = a ++ b :: c) -> False.
  induction a; crush.
Qed.
                                                  
Lemma empty_lists : forall {A : Type} (pre post : list A) (lft mid : A), ([lft] = (pre ++ mid :: post)) -> ([] = pre) /\ ([] = post) /\ (lft = mid).
  intro A. specialize (@mid_cons_nonempty A). 
  induction pre; crush.
Qed.

Lemma empty_rev : forall {A : Type} (l : list A) , ([] = rev l) <-> ([] = l).
  split; try (crush; tauto). destruct l.
  - tauto.
  - intros. simpl in H. apply mid_cons_nonempty in H. exfalso; tauto.
Qed.

Ltac empty_lists := repeat
                       match goal with
                         | [H : ?l1 ++ ?e :: ?l2 = [?a] |- _] => symmetry in H
                         | [H : ?e :: ?l2 = [?a] |- _] => symmetry in H
                         | [H : ?l1 ++ [?e] = [?a] |- _] => symmetry in H
                         | [H : _ = [] |- _] => symmetry in H
                      | [H : [?a] = ?l1 ++ ?e :: ?l2 |- _] =>
                        assert ([] = l1) by (apply empty_lists in H; tauto); subst;
                        assert ([] = l2) by (apply empty_lists in H; tauto); subst;
                        assert (a = e) by (apply empty_lists in H; tauto); subst;
                        clear H
                      | [H : [?a] = ?e :: ?l2 |- _] =>
                          assert (l2 = []) by (apply (empty_lists []) in H; crush; tauto); subst;
                          assert (a = e) by (apply (empty_lists []) in H; crush; tauto); subst;
                          clear H
                      | [H : [?a] = ?l1 ++ [?e] |- _] =>
                        assert (l1 = []) by (apply empty_lists in H; tauto); subst;
                        assert (a = e) by (apply empty_lists in H; tauto); subst;
                        clear H
                      | [H : context [[] ++ ?e] |- _] => rewrite app_nil_l in H
                      | [H : context [?e ++ []] |- _] => rewrite app_nil_r in H
                      | [H : [] = rev ?l |- _] => apply (empty_rev l) in H
                    end.

Ltac split_context_pair := match goal with
                             | [H : (?a,?b) = (?a',?b') |- _] => assert (a = a') by crush; assert (b = b') by crush; clear H
                           end.
Ltac clear_reflexives := match goal with | [H : ?e = ?e |- _] => clear H end.
Ltac generalize4 b a index l2 := generalize dependent b; generalize dependent a; generalize dependent index; generalize dependent l2.
Ltac lift_into_rev := match goal with
                        | [H : context [rev ?a ++ [?b]] |- _] => replace (rev a ++ [b]) with (rev (b::a)) in H by crush
                        | [H : context [_ :: rev _] |- _] => rewrite <- rev_unit in H
                      end.

Ltac normalize_list_in := match goal with [H : context [(?a :: ?b) ++ ?c] |- _] => replace ((a :: b) ++ c) with (a::b ++ c) in H by crush end.
Ltac list_size_contradiction := repeat empty_lists; repeat normalize_list_in; try empty_flatten;
                                try match goal with
                                  | [H : ?a :: ?b ++ [?c] = [?d] |- _] => symmetry in H
                                  | [H : _ = [] |- _ ] => symmetry in H
                                end;
                                match goal with
                                  | [H : ?a :: ?b ++ [?c] = [?d] |- _] => symmetry in H; apply list_sizes_match' in H
                                  | [H : [?d] = ?a :: ?b ++ [?c] |- _] => apply list_sizes_match' in H
                                  | [H : [] = ?a ++ ?b :: ?c |- _ ] => apply (mid_cons_nonempty a c b) in H
                                  | [H : [] = ?b :: ?c  |- _ ] => apply (mid_cons_nonempty [] c b) in H
                                  | [H : [] = ?a ++ [?b]  |- _ ] => apply (mid_cons_nonempty a [] b) in H
                                end; auto; exfalso; tauto.

Lemma flatten_exp_exp'_relate : forall index e, (rev (fst (flatten_exp' index e)) = fst (flatten_exp index e)).
  intros. unfold flatten_exp. mycrush. Qed.

Lemma rev_injective : forall {A : Type} (l1 l2 : list A), (rev l1 = rev l2) -> (l1 = l2).
  induction l1; induction l2;
  try tauto;
  try (intros; simpl in H; list_size_contradiction; tauto).
  crush. apply app_inj_tail in H. destruct H; apply IHl1 in H; crush. 
Qed.

Ltac list_head_equal := match goal with | [H : ?hd::?tl = ?hd'::?tl' |- _] => assert (hd = hd') by crush; assert (tl = tl') by crush end.

Lemma rev_injective' : forall {A : Type} (l1 l2 : list A),  (l1 = l2) -> (rev l1 = rev l2).
  induction l1; induction l2;
  try tauto;
  try (intros; simpl in H; list_size_contradiction; tauto). 
  intros. list_head_equal. crush. 
Qed.

Lemma rev_ctor : forall {A : Type} (l1 l2 : list A),  (l1 = l2) <-> (rev l1 = rev l2).
  split. apply rev_injective'; tauto. apply rev_injective; tauto.
Qed.

Ltac swap_revs H1 := apply rev_injective' in H1; repeat rewrite rev_involutive in H1; simpl in H1; repeat rewrite rev_unit in H1; simpl in H1. 

Lemma revs_swap : forall {A : Type} (l1 l2 : list A), (rev l1 = l2) <-> (rev l2 = l1).
  split; intros; swap_revs H; crush.
Qed.

Ltac make_tail := match goal with
                       | [H : context [?a :: ?b ++ [?tl] ] |- _] => replace (a :: b ++ [tl]) with ((a :: b) ++ [tl]) in H by crush
                       | [H : context [?a ++ [?b; ?tl] ] |- _] => replace (a ++  [b; tl]) with ((a ++  [b] ) ++ [tl]) in H by crush
                       | [H : context [?a ++ ?b ++ [?tl]] |- _] => replace (a ++ b ++ [tl]) with ((a ++ b) ++ [tl]) in H by crush
                  end.

Ltac rev_extract_head :=
  repeat make_tail; match goal with
    | [H : rev (?hd :: ?tl) =  [?hd'] |- _] => simpl in H; symmetry in H; empty_lists
    | [H : rev (?hd :: ?tl) = ?tl' ++ [?hd'] |- _] => 
      swap_revs H; repeat normalize_list_in; list_head_equal; subst; lift_into_rev;
      match goal with
        | [H2 : tl = rev tl' |- _] => apply rev_injective' in H2; rewrite rev_involutive in H2
      end
  end.

Lemma rev_head : forall {A : Type} (hd hd' : A) (tl tl' : list A), (rev (hd :: tl) = tl' ++ [hd']) -> (hd = hd') /\ ((rev tl) = tl').
  intros. rewrite revs_swap in H. rewrite rev_unit in H. list_head_equal; crush. rewrite rev_involutive. tauto.
Qed.

Lemma middle_in_somewhere: forall {A : Type} (l r l1 l2 : list A) (x : A), l ++ r = l1 ++ x ::l2 -> (In x l \/ In x r).
  intros. assert (In x (l1 ++ x :: l2)) by crush. rewrite <- H in H0. apply in_app_iff in H0. tauto.
Qed.
Hint Constructors NoDup. 

 Lemma nodup_app_split : forall {A : Type} (l r : list A), (NoDup (l ++ r)) -> (NoDup l /\ NoDup r).
Proof. induction l; crush.
  -
 rewrite NoDup_cons_iff in *; destruct H; split.
  +
  rewrite in_app_iff in H.
  unfold not in *. intro. apply H. left. auto.
  + 
  apply IHl in H0. destruct H0. auto.
  - rewrite NoDup_cons_iff in H. destruct H. apply IHl in H0. destruct H0; auto.
Qed.

Lemma nodup_snoc_iff : forall {A : Type} (a : A) (l : list A), NoDup (l ++ [a]) <-> ~ In a l /\ NoDup l.
Proof. split. 
  - intro. apply (NoDup_remove l nil a) in H. rewrite app_nil_r in H. tauto.
  - generalize dependent a.
  induction l; crush. rewrite NoDup_cons_iff in *. split.
  + unfold not; intro.
  apply in_app_or in H0. destruct H0. destruct H1. congruence. simpl in H0. apply H. destruct H0. auto. exfalso; auto.
  + apply IHl. destruct H1. split. auto. auto. 
Qed.
  
Lemma nodup_rev : forall {A : Type} (l : list A), NoDup l -> (NoDup (rev l)).
  induction l using rev_ind; crush. apply nodup_snoc_iff in H. destruct H. apply IHl in H0.
  rewrite rev_app_distr. crush. apply NoDup_cons_iff. crush. apply in_rev in H1. crush.
Qed.

Lemma unique_nth_len : forall {A : Type} (hd tl : list A) (mid : A), exists n : nat, (length hd) = n /\ nth n (hd ++ mid :: tl) mid = mid.
  intros.
  induction hd; crush. 
  exists 0. crush.
  exists (S (length hd)). crush.
Qed.

  Lemma firstn_app n:
    forall {A : Type} (l1 l2 : list A),
    firstn n (l1 ++ l2) = (firstn n l1) ++ (firstn (n - length l1) l2).

    Lemma firstn_app_2 n:
      forall {A : Type} (l1 l2 : list A),
    firstn ((length l1) + n) (l1 ++ l2) = l1 ++ firstn n l2.

Lemma firstn_app_3 : forall {A : Type} (n : nat) (l1 l2 : list A), n <= length l1 -> firstn n (l1 ++ l2) = firstn n l1.
  intros.
  pose proof (firstn_app n l1 l2) as Hfnapp. rewrite -> Hfnapp. assert ((n - (length l1)) = 0) as Hn0. omega. rewrite -> Hn0. simpl. crush.
Qed.

Lemma firstn_app_4 :  forall {A : Type} (n : nat) (l1 l2 : list A), n = length l1 -> firstn n (l1 ++ l2) = l1.
  intros.
  pose proof (firstn_app_3 n l1 l2). assert (n <= length l1). crush. apply H0 in H1. rewrite -> H1. subst. apply firstn_all.
Qed.



Lemma unique_split_eq : forall {A : Type} (l r hd tl : list A) (mid : A),
                       NoDup (hd ++ mid :: tl) ->  (l ++ mid :: r = hd ++ mid :: tl) -> ((l = hd) /\ (r = tl)).
  intros.
  assert (Hlen : length (l ++ [mid]) = length (hd ++ [mid])).
  assert (NoDup (l ++ mid :: r)) as Hndl. rewrite H0. assumption. pose proof (unique_nth_len l r mid) as Hnl.
  pose proof (unique_nth_len hd tl mid) as Hnr. destruct Hnl as [nl [Hlenl Hnthl]]. destruct Hnr as [nr [Hlenr Hnthr]].
      assert (nl = nr). rewrite -> NoDup_nth in Hndl. 
      apply Hndl.
      rewrite -> app_length. crush.
      rewrite -> H0. rewrite -> app_length. subst. crush.
      rewrite Hnthl. rewrite -> H0. rewrite -> Hnthr. reflexivity.
      subst. repeat rewrite -> app_length. rewrite -> H1. reflexivity.
      assert (firstn (length l) (l ++ mid :: r) = l). apply firstn_app_4. reflexivity.
      assert (firstn (length hd) (hd ++ mid :: tl) = hd). apply firstn_app_4. reflexivity.
      assert ((length l) = (length hd)) as Hlen' by (repeat rewrite -> app_length in Hlen; crush).
      rewrite <- Hlen' in H2. rewrite <- H0 in H2. rewrite -> H2 in H1. subst. split; auto.
      apply app_inv_head in H0. inversion H0. reflexivity.
Qed.
  


Lemma app_cons_app : forall {A : Type} (l r : list A) (mid : A), l ++ mid :: r = (l ++ [mid]) ++ r.
  intros. crush.
Qed.

Lemma firstn_eq : forall {A : Type} (n : nat) (l1 r1 l2 r2: list A) , n <= length l1 -> n <= length l2 -> (firstn n l1) ++ r1 = (firstn n l2) ++ r2 -> (firstn n l1) = (firstn n l2).
  induction n.
    reflexivity.
    intros. destruct l1.
      inversion H.
      destruct l2.
        inversion H0.
        repeat rewrite -> firstn_cons in *. simpl in H1. inversion H1. subst. rewrite -> (IHn l1 r1 l2 r2); crush.
Qed.

Lemma middle_is_somewhere: forall {A : Type} (l r hd tl : list A) (mid : A),
                            (l ++ r = hd ++ mid :: tl) -> (exists l1 l2, (l = hd ++ mid::l1 /\ tl = (l1 ++ l2))
                                                                                             \/ (r = l2 ++ mid::tl /\ hd = (l1 ++ l2))) .
  intros.
  destruct (le_lt_dec (length (hd ++ [mid])) (length l)).
    exists (skipn (length (hd ++ [mid])) l). exists r. left. assert (Hfn : (hd ++ [mid]) = firstn (length (hd ++ [mid])) (l ++ r)). rewrite -> app_cons_app in H. rewrite -> H. symmetry. apply firstn_app_4. reflexivity. split.
      rewrite -> app_cons_app. rewrite -> Hfn. rewrite -> firstn_app_3; try assumption. rewrite -> firstn_length_le; try assumption. symmetry. apply firstn_skipn.
      rewrite -> app_cons_app in H. rewrite -> Hfn in H. rewrite -> firstn_app_3 in H; try assumption. rewrite <- (firstn_skipn (length (hd ++ [mid])) l) in H at 1. symmetry. rewrite <- app_assoc in H. apply app_inv_head in H. assumption.
    exists l. exists (skipn (length l) hd). right. assert (Hlen : length l <= length hd) by (rewrite -> app_length in l0; crush). rewrite <- (firstn_skipn (length l) hd) in H. rewrite <- (firstn_all l) in H at 1. rewrite <- app_assoc in H. assert (Hfn: firstn (length l) l = firstn (length l) hd). apply firstn_eq with r (skipn (length l) hd ++ mid :: tl); auto. rewrite -> Hfn in H. split. 
      apply app_inv_head in H. assumption.
      rewrite -> firstn_all in Hfn. rewrite -> Hfn at 1. symmetry. apply firstn_skipn.
Qed.

      
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
                        let index' := next_index index lst in
                        let (lst2,ref2) := flatten_exp index' y in
                        declare_everything (index_from_var ref2) lst2
                                           (snd (declare_everything (index_from_var ref) lst (Flat_Assign_ptr ref2 ref)))
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

Eval compute in (flatten (While (Binop Tt And Tt) (Return (Binop Ff And Ff)))).

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



Lemma sequential_is_seq: forall l a, is_sequential (a::l)
-> seq a (length (a::l)) = a::l.
Proof. induction l; crush.
Qed.


Lemma sequential_nodup: forall l, is_sequential l -> NoDup l.
Proof. Hint Constructors NoDup. destruct l. intro; auto.
      intro. apply sequential_is_seq in H. rewrite <- H.
      apply seq_NoDup.
Qed.


Lemma first_smallest_sequential : forall l a x,
is_sequential (a::l) -> In x (a::l) -> a <= x.
Proof. intros. apply sequential_is_seq in H.
rewrite <- H in H0. rewrite in_seq in H0. omega.
Qed.


Lemma flatten_exp_exp':
forall index e,
  fst (flatten_exp index e)= rev (fst (flatten_exp' index e)).
Proof. intros.  unfold flatten_exp. unfold fst. mycrush.
Qed.

Lemma map_fst_rev_commute:
forall {A B:Type}(l:list (prod A B)),
map fst (rev l) = rev (map fst l).
Proof. induction l; crush. normalize_map. simpl. crush.
Qed.

Lemma nodup_flatten_exp: forall e index,
NoDup (map fst (fst (flatten_exp index e))).
Proof. intros.  rewrite flatten_exp_exp'.
  rewrite map_fst_rev_commute.
  assert (NoDup (map fst (fst (flatten_exp' index e)))).
  assert (is_sequential (map fst (fst (flatten_exp' index e))))
    by apply flatten_exp'_sequential.
  apply sequential_nodup in H; auto.
  apply nodup_rev; auto.
Qed.

Lemma in_tuple_helper: forall {A B:Type}(l: list (prod A B)) n x,
In (n,x) l -> In n (map fst l).
Proof. induction l; crush. assert (In n (map fst l)). apply IHl with (x:=x).
  auto. auto.
Qed.
Lemma map_rev_commute: forall {A B:Type}(l: list (prod A B)), map fst (rev l) = rev (map fst l).
Proof.  induction l; crush.
  rewrite map_app. crush. 
Qed.

Lemma flatten_exp_index_cmp: forall e index x,
In x (map fst (fst (flatten_exp index e))) -> index <= x.
Proof.
  intros. rewrite flatten_exp_exp' in H.
  rewrite map_rev_commute in H.
  apply in_rev in H.
  remember  (map fst (fst (flatten_exp' index e))) as l.
  destruct l. contradict H.
  assert (is_sequential (n::l)) by (rewrite Heql; apply 
flatten_exp'_sequential).
  apply first_is_index in Heql. subst. 
  apply (first_smallest_sequential (l)); auto.
Qed.
  
 Lemma index_lt_next_index:  forall e index,
 index < (next_index index (fst (flatten_exp index e))).
  Proof. intros.
  unfold next_index.
  remember ( (fst (flatten_exp index e))) as l.
  destruct l. auto. destruct p.
  
  assert (In n (map fst (fst (flatten_exp index e)))).
  apply in_tuple_helper with (x:=f). rewrite <- Heql. 
  apply in_eq.
  apply flatten_exp_index_cmp in H. omega.
Qed.
  
Lemma last_helper: forall {A:Type} (l:list A) d, ~(l=[])->
   In (last l d) l.
   induction l. intros. congruence.
   intros. 
   destruct l. compute; auto. rewrite last_drop_head.
   assert (In (last (a0 :: l) d) (a0 :: l)). apply IHl. 
   crush.
   crush. Qed.


Lemma helper: forall l a,  (*change this horrible name*)
   In (System a) (map (fun x: nat=>System x) l)->
   In a l. induction l; crush. Qed.

Print next_index.


Lemma last_in_seq: forall len  start  d,
len > 0 -> last (seq start len) d = start+len-1.
Proof.
  induction len; crush.
  remember (seq (S start) len) as l.
  destruct l. unfold seq in Heql. destruct len. omega. congruence.  
  rewrite Heql. replace (start + S len - 1) with (S start + len - 1) by omega.
  apply IHlen. destruct len. unfold seq in Heql; congruence. omega.
Qed.


Lemma last_rev_is_first: forall {A:Type} (l:list A) n a l' d, 
rev (a::l) = n::l' ->
n =last  (a::l) d .
Proof. induction l; crush. destruct l; auto.
  crush. eapply IHl.
  assert (l'<>[]).
  unfold not; intro. subst. destruct (rev (a1::l)).
  crush. rewrite <- app_comm_cons  in H. 
  destruct l0; crush.
  apply app_removelast_last with (d:=d) in H0.
  rewrite H0 in H.
  replace ( rev (a1 :: l) ++ [a; a0] ) with
   ( (rev (a1::l) ++[a])++[a0]) in H.
  replace (n :: removelast l' ++ [last l' d])
  with ((n :: removelast l') ++ [last l' d]) in H.
 apply app_inj_tail in H. destruct H. apply H.
  apply app_comm_cons.
  rewrite <- app_assoc. auto.
Qed.

Lemma next_index_bigger : forall e index x,
In x (map fst (fst (flatten_exp index e) )) -> x <
next_index index (fst (flatten_exp index e)).
Proof.
  intros. rewrite flatten_exp_exp' in H .
  rewrite map_rev_commute in H.
  rewrite <- in_rev in H.
  unfold next_index. rewrite flatten_exp_exp'.
  assert (is_sequential (map fst (fst (flatten_exp' index e)))) by
  apply flatten_exp'_sequential.
  remember ( fst (flatten_exp' index e) )as l.
  destruct l. contradict H. 
  destruct (rev (p:: l)) eqn: Q. 
  replace  (rev (p::l)) with (rev l ++[p]) in Q by auto.	 symmetry in Q.
  apply app_cons_not_nil in Q. exfalso; auto.
  destruct p0.
  assert (map fst (rev (p::l)) = map fst ((n,f)::l0)) by (rewrite Q; auto).
  rewrite map_rev_commute in H1. 
  replace (map fst (p::l)) with ((fst p)::(map fst l)) in * by auto.
  apply sequential_is_seq in H0.
  replace (map fst ((n ,f)::l0)) with (n::(map fst l0)) in H1 by auto.
  assert (n = last (fst p :: map fst l) 0).
  eapply last_rev_is_first. apply H1.
  rewrite H2. rewrite <- H0.
  rewrite <- H0 in H. apply in_seq in H. rewrite last_in_seq.
  omega. omega.
Qed.

Ltac uvstac := match goal with
  | [H: In ?a (?l1 ++ ?l2) |- _] => apply in_app_or in H; destruct H
  | [H: In ?b (?a::?l) |- _] => apply in_inv in H; destruct H
  | [H: context[?l++[]] |- _] => rewrite app_nil_r in H
  end.

 Lemma next_index_gt_index: forall e index,
index < next_index index (fst (flatten_exp index e)).
   Proof. intros. unfold next_index.
  destruct (fst (flatten_exp index e)) eqn: Q. auto.
  destruct p.
  unfold flatten_exp in Q; destruct_things; subst; simpl.
  unfold fst in Q.
  destruct_things ; subst; simpl.
  destruct (fst (flatten_exp' index e)) eqn:P.
  symmetry in P. apply flatten_exp'_never_empty in P. exfalso; auto.
  

  assert (map fst (rev (fst (flatten_exp' index e))) = n:: (map fst l)) by crush.
  rewrite map_rev_commute in H.
  assert (In n (rev (map fst (fst (flatten_exp' index e))))) by crush.
  rewrite <- in_rev in H0.
  assert (is_sequential (map fst (fst (flatten_exp' index e))))
  by (apply flatten_exp'_sequential).
  Check sequential_is_seq. Check first_is_index.
   destruct (map fst (fst (flatten_exp' index e))) eqn:QQ.
  contradict H0. symmetry in QQ.
  apply first_is_index in QQ.
  apply first_smallest_sequential with(x:=n) in H1. subst. omega. auto.
Qed.
Lemma flatten'_index_increase: forall c x index, 
  
  In (System x) (collect_declared_vars_flatcom (snd (flatten' index c)))
  -> index <= x.
 Ltac unfold_def := match goal with
    | [H: context[unique_decl_com _] |- _ ] => unfold unique_decl_com in H
    | [H: context [unique_decl_flat _] |- _] => unfold unique_decl_flat in H
    
    | [|- context [unique_decl_flat _] ] => unfold unique_decl_flat 
    |[H: context [collect_declared_vars_flatcom _ ]|-_]=>
        (unfold collect_declared_vars_flatcom in H; auto;
         try fold collect_declared_vars_flatcom in H)
    | [|- context [collect_declared_vars_flatcom _ ]]=>
        (unfold collect_declared_vars_flatcom ; auto;
         try fold collect_declared_vars_flatcom)
end.

Ltac peel:= match goal with
      | [H: In (System ?x0)
      (map (fun x : nat => System x)
         (map fst (fst (flatten_exp ?index ?e0)))) |- _]
        => 
    assert (In x0  (map fst (fst (flatten_exp index e0)))  ) as H0
   by (apply helper; auto) ; apply flatten_exp_index_cmp with (e:=e0) in H0; auto 
       end.
Proof. induction c; mycrush;  repeat rewrite collect_declare_everything in H;
  repeat unfold_def; uvstac; try peel; try (contradict H; tauto). - crush. 
 apply IHc in H0; auto; auto. 
  assert (index < (next_index index (fst (flatten_exp index e)))).
  apply index_lt_next_index. omega.
 -  assert (index < (next_index index (fst (flatten_exp index e0)))).
  apply index_lt_next_index. omega.
 - apply in_app_or in H. destruct H.
   peel. contradict H.
Qed.




Lemma user_not_in_system: forall l x, In (User x) 
 (map (fun x : nat => System x) l) -> False.
Proof. induction l; crush. apply IHl in H0. auto. Qed.
Lemma user_var_same: forall c index x,
In (User x) (collect_declared_vars_flatcom (snd (flatten' index c)))
-> In x (collect_declared_vars_com c).
Proof. 
Hint Resolve user_not_in_system.
   induction c; mycrush; (try rewrite collect_declare_everything in *).
   - uvstac. eauto.
unfold collect_declared_vars_flatcom in H.  auto.
   - uvstac.
     + apply user_not_in_system in H; auto; exfalso; auto.
     +   unfold collect_declared_vars_flatcom in H.
     fold collect_declared_vars_flatcom in H.
     uvstac.
       * crush.
       * apply IHc in H. auto.
   - uvstac.
     + eauto. 
     + unfold collect_declared_vars_flatcom in H. auto.
   - uvstac.
     + eauto.
     + rewrite collect_declare_everything in H.
     unfold collect_declared_vars_flatcom in H. uvstac. 
     eauto. auto.
  - uvstac. eauto. unfold collect_declared_vars_flatcom in H. auto.
  - uvstac. eauto. unfold collect_declared_vars_flatcom in H. auto.
Qed.

Lemma flatten_system_exp_all_bound' : forall e l1 l2 interim index, (fst((flatten_exp index e)) = (l1 ++ interim ::l2)) ->  ((bound_system_exp (snd interim) l1) = true).
  Ltac rev_flatten_exp'_extract_head :=
    repeat make_tail;
    match goal with
      | [H : rev (fst (flatten_exp' _ _)) ++ [_] = [_] |- _] => lift_into_rev; apply (rev_head _ _ _ []) in H; crush; list_size_contradiction; tauto
      | [H : rev (fst (flatten_exp' ?a ?b)) ++ [?hd] = ?tl' ++ [?hd'] |- _] =>
        lift_into_rev; apply (rev_head hd hd' (fst (flatten_exp' a b)) tl') in H; crush;
        match goal with
          | [H : rev (fst (flatten_exp' _ _)) = _ |- _] => rewrite flatten_exp_exp'_relate in H
        end
    end.

  Ltac match_flatten_exp'_bound_structure :=
    match goal with
      | [H : context [?l1 ++ ?x :: ?y :: ?l2] |- _ ] => replace (l1 ++ x :: y :: l2) with ((l1 ++ [x]) ++ y :: l2) in H by crush
      | [H : context [?y :: ?l2] |- _ ] => replace (y :: l2) with ([] ++ y :: l2) in H by crush
    end.

  Ltac kill_hd_stupid name name_eq := match goal with
                                        | [|- context [hd (stupid _) ?e] ] => remember_destruct e name name_eq;
                                            [list_size_contradiction; tauto | idtac]
                                      end.

  Ltac kill_hd_stupid_rev name := match goal with
                                        | [|- context [hd (stupid _) ?e] ] => remember e as name; 
                                            induction name using rev_ind; 
                                            [list_size_contradiction; tauto | idtac]
                                      end.
  
  induction e;
    (*trivial case*) try (mycrush; empty_lists; split_context_pair; subst; auto; tauto);
  (*single-arg ones*)
  try (induction l1 using rev_ind; 
       induction l2 using rev_ind; mycrush; rev_flatten_exp'_extract_head;
       (* inductive case*)
       try (match_flatten_exp'_bound_structure; apply IHe in H1; crush; tauto);
       (* complex base case *)
       try (mycrush;
            rewrite <- destruct_system_bound_in_rev;
            rewrite flatten_exp'_returns_right_nat; bool_identity; rewrite <- flatten_exp_exp'_relate in H1; swap_revs H1;
            rewrite H1; reflexive_nateq_left; tauto); tauto).
  - intros. rewrite <- flatten_exp_exp'_relate in H. mycrush. lift_into_rev.
    generalize dependent index. generalize dependent interim. generalize dependent l1. 
    induction l2 using rev_ind; mycrush.
    * lift_into_rev. apply rev_head in H. mycrush. repeat rewrite flatten_exp'_returns_right_nat.
      apply andb_true_intro; split.
    + remember (fst
                  (flatten_exp'
                     (next_index' (S a) (map fst (fst (flatten_exp' (S a) e2)))) e1)) as lend. induction lend using rev_ind. list_size_contradiction.
      repeat rewrite rev_app_distr. crush. remember_destruct' x. mycrush.
      remember_destruct' (fst
                            (flatten_exp'
                               (next_index' (S a) (map fst (fst (flatten_exp' (S a) e2)))) e1)). list_size_contradiction.
      mycrush. clear IHlend. remember_destruct lend hope hope_eq. (empty_lists; reflexive_nateq_left; tauto).
      crush. apply orb_true_intro; right. apply system_bound_in_itself. 
    + remember (rev
       (fst (flatten_exp' (S a) e2) ++
        fst
          (flatten_exp'
             (next_index' (S a) (map fst (fst (flatten_exp' (S a) e2)))) e1))) as lend. induction lend using rev_ind. 
      empty_lists; symmetry in Heqlend; apply app_eq_nil in Heqlend; destruct Heqlend; list_size_contradiction; tauto. 
      repeat rewrite rev_app_distr. crush. remember_destruct' x. mycrush.
      remember_destruct' (fst (flatten_exp' (S a) e2)). list_size_contradiction. mycrush.
      repeat rewrite rev_app_distr. rewrite <- system_bound_in_reorder. apply (system_bound_in_itself [] ).
    * lift_into_rev. repeat make_tail. apply rev_head in H. mycrush.
      repeat rewrite rev_app_distr in H1. repeat rewrite flatten_exp_exp'_relate in H1.
      apply middle_is_somewhere in H1. destruct H1. destruct H; destruct H; destruct H.  
    + apply IHe1 in H. crush.
    + apply IHe2 in H. crush. rewrite bound_system_exp_strong_reorder. apply strong_induct_bound_system_exp. tauto. 
Qed.

Lemma flatten_bound :  forall c, (bound_com c) -> (bound_flat_com (flatten c)).
  induction c; crush.
  unfold flatten. crush. mycrush. 
Admitted.

Definition lift_env e := map (fun x => User x) e.

Fixpoint used_vars_flat c : (list flat_var) :=
  match c with
    | Flat_Skip => []
    | _ => []
  end.

Lemma declare_everything_bound : forall c l index1 index2 e, (l = flatten_exp index1 e) -> (All_In (used_vars_flat c) l) ->
                                                     (bound_flat_com (snd (declare_everything index2 c l)) ).

Ltac unfold_def2 := match goal with
    | [H: context[unique_decl_com _] |- _ ] => unfold unique_decl_com in H
    | [H: context [unique_decl_flat _] |- _] => unfold unique_decl_flat in H
    
    | [|- context [unique_decl_flat _] ] => unfold unique_decl_flat 

    | [|- context [collect_declared_vars_flatcom _ ]]=>
        (unfold collect_declared_vars_flatcom ; auto;
         try fold collect_declared_vars_flatcom)
end.

Lemma flatten_unique : forall (c : com)(index:nat), (unique_decl_com c) -> unique_decl_flat (snd (flatten' index c)).
Hint Constructors NoDup.
Hint Resolve nodup_flatten_exp.
Proof. 

induction c; mycrush; try (unfold unique_decl_flat; mycrush; tauto);
   try (apply declare_everything_unique; auto); 
   repeat (unfold_def2; auto).
   - unfold collect_declared_vars_com in H;
     fold collect_declared_vars_com in H.
     rewrite NoDup_cons_iff in *. destruct H. split.
     unfold not; intro. apply user_var_same in H1. auto.
     apply IHc with (index:=(next_index index (fst (flatten_exp index e)))) in H0.
     auto.
   - intros; unfold not; intro H2. destruct H2. congruence.
     apply flatten'_index_increase in H1. 
     apply next_index_bigger in H0. omega.
   - apply declare_everything_unique; auto; repeat (unfold_def).
   -intros; unfold not; intro. rewrite collect_declare_everything in H1. 
     uvstac. apply helper in H1.
    apply flatten_exp_index_cmp in H0.
    apply next_index_bigger in H1. omega.
    unfold_def. 
Qed.

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
Admitted.

(* note: we need to change the environments to split user + system variables into their own heaps or else this flatten_correct is impossible*)
(* note: we need a theorem that says "system variable represents computation".  This is a flatten_exp theorem *)
