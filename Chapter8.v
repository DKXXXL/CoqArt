Require Import List.

Inductive last(A : Set) : list A -> A -> Prop :=
  single : forall a : A, last A (a :: nil) a
| compound : forall (l : list A)(a b : A), last A l a -> last A (b :: l) a.

Fixpoint last_fun(A : Set)(l : list A) : option A :=
  match l with
  | nil => None
  | a :: nil => Some a
  | a :: b => last_fun A b
  end.

Goal forall(A : Set)(l : list A)(a : A), last A l a -> last_fun A l = Some a.
  intros.
  elim H.
  reflexivity.
  intros.
  rewrite <- H1.
  simpl.
  destruct l0.
  inversion H1.
  reflexivity.
Qed.

Inductive permutation(A : Set) : list A -> list A -> Prop :=
  transpose : 
    forall (l r : A)(lis : list A),
      permutation A (l :: r :: lis) (r :: l :: lis)
| trans : forall a b c, permutation A a b -> permutation A b c -> permutation A a c
| id : forall a, permutation A a a.

Require Import Relations.

Theorem equiv_perm : forall A : Set, equiv _ (permutation A).
  intros.
  repeat split.
  unfold reflexive.
  constructor.
  unfold transitive.
  intros.
  apply (trans A x y z);assumption.
  unfold symmetric.
  intros.
  elim H.
  intros.
  constructor.
  intros.
  econstructor.
  eassumption.
  assumption.
  constructor.
Qed.

Require Import JMeq.
Require Import Arith.

Lemma plus_assoc_JM : 
  forall n p q:nat,
    JMeq (n+(p+q)) (n+p+q).
  intros.
  rewrite plus_assoc.
  constructor.
Qed.

Inductive even : nat -> Prop :=
| O_even : even 0
| plus_2_even : forall n:nat, even n -> even (S (S n)).

Hint Resolve O_even plus_2_even.

Fixpoint mult2 (n:nat) : nat :=
  match n with
  | O => 0
  | S p => S (S (mult2 p))
  end.

Goal forall n, even (n * 2).
  intros.
  induction n.
  auto.
  rewrite mult_succ_l.
  rewrite plus_comm.
  simpl.
  auto.
Qed.

Goal forall n, even n -> exists x, x * 2 = n.
  intros.
  induction H.
  exists 0.
  auto.
  destruct IHeven.
  exists (S x).
  rewrite mult_succ_l.
  rewrite plus_comm.
  simpl.
  auto with arith.
Qed.

Lemma even_plus : forall n m, even n -> even m -> even (n + m).
  intros.
  induction H.
  auto.
  simpl.
  auto.
Qed.

Goal forall n, even n -> even (n * n).
  intros.
  induction H.
  auto.
  repeat rewrite mult_succ_l.
  repeat rewrite mult_succ_r.
  repeat apply even_plus;auto.
Qed.

Theorem lt_le : forall n p:nat, n < p -> n <= p.
  intros n p H.
  apply (le_ind (S n)).
  repeat constructor.
  intros.
  constructor.
  assumption.
  assumption. 
Qed.

Definition my_le (n p:nat) :=
  forall P:nat->Prop,
    P n ->
      (forall q:nat, P q -> P (S q)) ->
        P p.

Lemma my_le_n : forall n:nat, my_le n n.
  unfold my_le.
  intros.
  assumption.
Qed.

Lemma my_le_S : forall n p:nat, my_le n p -> my_le n (S p).
  unfold my_le.
  intros.
  apply H.
  auto.
  intros.
  auto.
Qed.

Lemma my_le_inv : forall n p:nat, my_le n p -> n=p \/ my_le (S n) p.
  unfold my_le.
  intros.
  apply H.
  left.
  auto.
  intros.
  destruct H0.
  right.
  intros.
  rewrite <- H0.
  auto.
  right.
  intros.
  apply H2.
  apply H0;
  auto.
Qed.

Lemma my_le_inv2 :
  forall n p:nat, my_le (S n) p ->
    exists q, p=(S q) /\ my_le n q.
  unfold my_le.
  intros.
  apply H.
  exists n.
  split;
  auto.
  intros.
  destruct H0.
  destruct H0.
  exists (S x).
  split.
  auto with arith.
  intros.
  apply H3.
  apply H1;
  auto.
Qed.

Lemma my_le_n_O : forall n:nat, my_le n 0 -> n = 0.
  intros.
  destruct n.
  auto.
  ecase my_le_inv2.
  eassumption.
  intros.
  destruct H0.
  discriminate H0.
Qed.

Lemma my_le_le : forall n p:nat, my_le n p -> le n p.
  intros.
  apply H;
  auto.
Qed.

Lemma le_my_le : forall n p:nat, le n p -> my_le n p.
  unfold my_le.
  intros.
  induction H;
  auto.
Qed.
Require Export Program.
Inductive par := open | close.
Inductive wp : list par -> Prop :=
| wp_nil : wp []
| wp_par l : wp l -> wp (open :: (l ++ [close]))
| wp_app l r : wp l -> wp r -> wp (l ++ r).
Hint Constructors wp.

Theorem cons_app { A } (l : A) r : l :: r = [l] ++ r.
  trivial.
Qed.

Theorem wp_oc : wp [open;close].
  rewrite (cons_app open); repeat constructor.
Qed.

Theorem wp_o_head_c l1 l2 : wp l1 -> wp l2 -> wp (open :: l1 ++ close :: l2).
  intros; rewrite (cons_app open), (cons_app close).
  rewrite !app_assoc; apply wp_app; simpl; auto.
Qed.

Theorem wp_o_tail_c l1 l2 : wp l1 -> wp l2 -> wp (l1 ++ open :: l2 ++ [close]).
  intros; rewrite (cons_app open).
  apply wp_app; simpl; auto.
Qed.

Fixpoint recognize n (l : list par) : bool :=
  match l, n with
  | [], 0 => true
  | open :: l', _ => recognize (S n) l'
  | close :: l', S n' => recognize n' l'
  | _, _ => false
  end.

Theorem repeat_shift { A } (e : A) n : repeat e n ++ [e] = e :: repeat e n.
  induction n; simpl in *; f_equal; auto.
Qed.

Theorem get_last { A } (l : list A) : l = [] \/ exists l' e, l = l' ++ [e].
  induction l; intuition idtac; program_simpl.
  right; exists (@nil A) a; trivial.
  right; exists (a :: H) H0; trivial.
Qed.
Hint Resolve wp_oc.

Inductive wp' : list par -> Prop :=
| wp'_nil : wp' []
| wp'_cons l r : wp' l -> wp' r -> wp' (open :: l ++ close :: r).
Hint Constructors wp'.
Theorem wp'_app l r : wp' l -> wp' r -> wp' (l ++ r).
  intros HL HR; induction HL; simpl in *; auto.
  rewrite <- app_assoc, <- app_comm_cons; auto.
Qed.
Hint Resolve wp'_app.
Theorem wp_wp' l : wp l -> wp' l.
  induction 1; simpl in *; auto.
Qed.

Theorem wp'_wp l : wp' l -> wp l.
  induction 1; auto.
  replace (open :: l ++ close :: r) with ((open :: l ++ [close]) ++ r); auto.
  simpl; f_equal; rewrite <- app_assoc; trivial.
Qed.

Hint Resolve wp_wp' wp'_wp.

Require Export Omega.

Theorem wp_close_false l : wp (close :: l) -> False.
  intros H; dependent induction H.
  destruct l0; inversion x; simpl in *; subst; eauto.
Qed.

Theorem wp_open_false l : wp (l ++ [open]) -> False.
  intros H; dependent induction H; destruct l; program_simpl.
  destruct l0; program_simpl.
  apply app_inj_tail in H2; intuition congruence.
  destruct l0, r; program_simpl.
  specialize(IHwp2 []); program_simpl.
  destruct l0; specialize(IHwp1 []); program_simpl.
  destruct l0, p0; program_simpl.
  destruct (get_last r); program_simpl; rewrite ?app_nil_r in *; subst; eauto.
  rewrite app_assoc in *; apply app_inj_tail in x; intuition; program_simpl; eauto.
Qed.

Hint Resolve wp_close_false wp_open_false.

Theorem wp_app_inv n l : length l < n -> wp (open :: close :: l) -> wp l.
  revert l; induction n; intros; [omega|].
  apply wp_wp' in H0; inversion H0; clear H0; simpl in *.
  destruct l0; simpl in *; program_simpl.
  apply wp'_wp in H2; exfalso; eauto.
Qed.

Ltac invcs s := inversion s; clear s; subst.
Theorem par_destruct_aux n l : length l < n -> head l = Some open -> 
  (exists n, l = repeat open n) \/ (exists n li, l = repeat open n ++ close :: li).
  revert l; induction n; intros; simpl in *; [omega|].
  destruct l as [|[]]; simpl in *; invcs H0.
  destruct l as [|[]]; simpl in *.
  left; exists 1; trivial.
  destruct (IHn (open :: l)) as [[]|[? []]]; simpl in *; omega || trivial;
  destruct x; simpl in *; invcs H0.
  left; exists (S (S x)); trivial.
  right; exists (S (S x)) x0; trivial.
  right; exists 1 l; trivial.
Qed.

Theorem par_destruct l :
  (exists n, l = repeat open n) \/ (exists n li, l = repeat open n ++ close :: li).
  destruct l as [|[]].
  left; exists 0; trivial.
  destruct (par_destruct_aux (S (S (length l))) (open :: l)); 
  simpl in *; program_simpl; omega || trivial.
  destruct H; invcs H0.
  left; exists (S H); trivial.
  destruct H; simpl in *; invcs H1.
  right; exists (S H) H0; trivial.
  right; exists 0 l; trivial.
Qed.

Theorem length_eq { A } { l r : list A } (H : l = r) : length l = length r.
  subst; trivial.
Qed.

Theorem app_eq { A } { ll lr rl rr : list A } : 
  ll ++ lr = rl ++ rr -> exists l, ll = rl ++ l \/ rl = ll ++ l.
  revert lr rl rr.
  induction ll; program_simpl; eauto.
  destruct rl; simpl in *; invcs H; eauto.
  specialize(IHll _ _ _ H2); program_simpl; intuition idtac; subst; eauto.
Qed.

Theorem wp_remove_aux n : forall l r, length l + length r < n ->
  wp (l ++ [open; close] ++ r) -> wp (l ++ r).
  induction n; simpl in *; intros; [omega|].
  apply wp_wp' in H0; invcs H0.
  destruct l; simpl in *; congruence.
  destruct l; simpl in *; invcs H1.
  destruct l0; simpl in *; invcs H4; eauto with *.
  destruct (app_eq H5) as [? []]; subst;
  rewrite <- app_assoc in *;
  apply app_inv_head in H5.
  destruct x; invcs H5.
  destruct x; invcs H4; try solve [exfalso; eauto].
  apply wp'_wp in H2; eapply IHn in H2; 
  repeat (simpl in *; rewrite ?app_length in *); try omega.
  replace 
    (open :: l ++ x ++ close :: r0) with 
    ((open :: l ++ x ++ [close]) ++ r0) by
    (simpl; f_equal; rewrite <- app_assoc; f_equal; rewrite <- app_assoc; trivial).
  apply wp_app; auto.
  rewrite app_assoc; auto.
  destruct x; simpl in *; invcs H5.
  replace 
    (open :: l0 ++ close :: x ++ r) with 
    ((open :: l0 ++ [close]) ++ x ++ r) by
    (simpl; f_equal; rewrite <- app_assoc; f_equal).
  apply wp_app; auto.
  eapply IHn; repeat (simpl in *; rewrite ?app_length in *); omega || auto.
Qed.

Theorem wp_remove l r : wp (l ++ open :: close :: r) -> wp (l ++ r).
  intros; eapply wp_remove_aux; auto.
Qed.

Theorem recognize_complete_aux l : wp l -> forall n l', recognize n (l ++ l') = recognize n l'.
  induction 1; intros; simpl in *; rewrite <- ?app_assoc, ?IHwp, ?IHwp1, ?IHwp2; trivial.
Qed.

Theorem recognize_complete l : wp l -> recognize 0 l = true.
  induction 1; simpl in *; rewrite ?recognize_complete_aux; trivial.
Qed.

Theorem wp_destruct l : wp l -> 
  l = [] \/ 
  (exists l1 l2, l = l1 ++ l2 /\ wp l1 /\ wp l2 /\ l1 <> [] /\ l2 <> []) \/ 
  (exists l1, l = open :: l1 ++ [close] /\ wp l1).
  induction 1; intros; try solve [intuition idtac].
  right; right; exists l; intuition.
  destruct IHwp1; program_simpl; simpl in *; trivial.
  destruct IHwp2; program_simpl; simpl in *; rewrite ?app_nil_r in *; eauto.
  right; left; exists l r; intuition idtac; program_simpl;
  match goal with H : ?X ++ ?Y = [] |- _ => destruct X; simpl in *; congruence end.
Qed.

Theorem wp_insert : forall n a b c, 
  length a + length b + length c < n -> wp (a ++ c) -> wp b -> wp (a ++ b ++ c).
  induction n; intros; simpl in *; [omega|].
  apply wp_destruct in H0; intuition idtac; program_simpl.
  + destruct a, c; simpl in *; rewrite ?app_nil_r; congruence.
  + destruct (app_eq H3); intuition idtac; subst; rewrite <- app_assoc in *;
    apply app_inv_head in H3; subst; repeat (simpl in *; rewrite ?app_length in *).
    - apply wp_app; eauto.
      eapply IHn; eauto.
      destruct H0; simpl in *; congruence || omega.
    - rewrite !app_assoc; apply wp_app; eauto.
      rewrite <- app_assoc; eapply IHn; eauto.
      destruct H2; simpl in *; congruence || omega.
  + destruct a; simpl in *; invcs H2; eauto.
    destruct (get_last c); program_simpl;
    repeat (rewrite ?app_nil_r, ?app_length, <- ?plus_n_O in *; subst; simpl in *).
    - rewrite app_comm_cons; eauto.
    - rewrite app_assoc in H6; apply app_inj_tail in H6; intuition idtac; subst.
      rewrite !app_assoc; apply wp_par; rewrite <- app_assoc; eapply IHn; eauto; omega.
Qed.

Theorem recognize_sound n l : recognize n l = true -> wp ((repeat open n) ++ l).
  revert n; induction l; intros; simpl in *.
  destruct n; simpl; congruence || auto.
  destruct a, n; simpl in *; try specialize (IHl _ H); simpl in *; congruence || auto.
  rewrite (cons_app _ l), app_assoc, repeat_shift; simpl; trivial.
  rewrite app_comm_cons, <- repeat_shift, <- app_assoc, (cons_app _ l), (app_assoc _ _ l).
  eapply wp_insert; eauto.
Qed.