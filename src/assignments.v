Require Import List Nat.
Require Import misc.
Require Import definitions.

Definition forall_assignments
    (C: nat)
    (aa: list Activity)
    (A: list nat -> list (Activity*nat) -> Type)
:=
  forall (starts: list nat),
    length starts = length aa ->
    let assignment := combine aa starts in
    aa_valid assignment /\ aa_fit C assignment ->
    A starts assignment.

Definition equallyAssignable (C: nat) (aa: list Activity) (bb: list Activity)
  : Prop
:=
  length aa = length bb ->
  forall starts, length starts = length aa ->
    let assignment_a := combine aa starts in
    let assignment_b := combine bb starts in
    (aa_valid assignment_a /\ aa_fit C assignment_a) <->
    (aa_valid assignment_b /\ aa_fit C assignment_b).

Definition unassignable (C: nat) (aa: list Activity) :=
  forall starts, let assignment := combine aa starts in
    length aa = length starts /\ aa_valid assignment /\ aa_fit C assignment -> False.

Definition unassignableByEnergy (C: nat) (aa: list Activity) :=
  ((lct aa) - (est aa)) * C < energy aa.

Definition aa_uses
  (assignment: list (Activity * nat))
  (samples: list nat) :=
    mapfold add (aa_use assignment) samples.

Definition aa_fit_weak
  (C: nat)
  (assignment: list (Activity * nat))
  (samples: list nat) :=
    aa_uses assignment samples <= (length samples) * C.

Theorem aa_fit_weak_easy
  (C: nat)
  (assignment: list (Activity * nat))
  (ok : aa_fit C assignment)
  (samples: list nat)
:
  aa_fit_weak C assignment samples.
Proof.
  induction samples.
  - unfold aa_fit_weak in *. auto.
  - unfold aa_fit_weak in *. simpl.
    apply Arith.Plus.plus_le_compat.
    apply (ok a).
    apply IHsamples.
Qed.

Require Import Omega.

Theorem sum_pair_sums {A} (l: list A) (f g: A -> nat) :
  mapfold add f l +
  mapfold add g l =
  mapfold add (fun x => f x + g x) l.
Proof.
  induction l.
  - auto.
  - unfold mapfold in *. simpl.
    rewrite <- IHl.
    omega.
Qed.

Theorem add_inner
  {A B}
  (outer: list A)
  (inner: list B)
  (b: B)
  (f: A -> B -> nat) :
    mapfold add (fun x => mapfold add (f x) inner) outer
  + mapfold add (fun x => mapfold add (f x) (cons b nil)) outer
  = mapfold add (fun x => mapfold add (f x) (b :: inner)) outer.
Proof.
  unfold mapfold in *.
  simpl in *.
  replace
    (map (fun x : A => f x b + 0) outer)
  with
    (map (fun x : A => f x b) outer).
  induction outer.
  subst; auto.
  simpl.
  remember (fold_right add 0) as sum.
  remember (sum (map (fun x => f x b) outer)) as FOB.
  remember (sum (map (fun x => sum (map (f x) inner)) outer)) as FOI.
  remember (sum (map (fun x => f x b + sum (map (f x) inner)) outer)) as FOB_FOI.
  assert (FOB + FOI = FOB_FOI) as H.
  subst.
  apply sum_pair_sums.
  rewrite <- H.
  omega.

  induction outer.
  auto.
  simpl.
  rewrite <- IHouter.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.


Theorem mapfold_step
  {A}
  k
  (f: A -> nat)
  (h: A)
  (l: list A)
:
  mapfold k f (h::l) = k (f h) (mapfold k f l).
Proof.
  auto.
Qed.

Theorem mapfold_f
  {A}
  k
  (f: A -> nat)
  (g: A -> nat)
  (fg: forall a, f a = g a)
  (l: list A) :
  mapfold k f l = mapfold k g l.
Proof.
  intros.
  induction l.
  auto.
  rewrite mapfold_step.
  rewrite mapfold_step.
  f_equal.
  apply (fg a).
  apply IHl.
Qed.

Theorem transpose_addition
  {A B}
  (aa: list A)
  (bb: list B)
  (f: A -> B -> nat)
:
  mapfold add (fun x => mapfold add (f x) bb) aa
    =
  mapfold add (fun y => mapfold add (fun x => f x y) aa) bb.
Proof.
  induction aa.
  - induction bb. auto. auto.
  - rewrite <- (add_inner bb aa a (fun x y => f y x)).
    unfold mapfold at 6.
    simpl.
    rewrite mapfold_step.
    rewrite IHaa.
    clear IHaa.
    replace (mapfold add (fun x : B => f a x + 0) bb)
      with (mapfold add (f a) bb).
    omega.
    induction bb.
    auto.
    rewrite mapfold_step.
    rewrite mapfold_step.
    rewrite IHbb.
    omega.
Qed.


Theorem transpose_aa_uses
  (assignment: list (Activity * nat))
  (samples: list nat) :
    aa_uses assignment samples =
    mapfold add (fun a => mapfold add (a_use (fst a) (snd a)) samples)
      assignment.
Proof.
  unfold aa_uses.
  rewrite <- (transpose_addition samples assignment).
  apply mapfold_f. intro.
  unfold aa_use.
  apply mapfold_f. intro.
  reflexivity.
Qed.


Theorem contained_activity (a: Activity) (s: nat) (start stop: nat) :
  start <= est a /\ lct a <= stop ->
  mapfold add (a_use a s) (range start stop) = energy a.
Proof.
Admitted.

(* single activity, no samples, no cost *)
Theorem aa_use_nil x : aa_use nil x = 0.
Proof.
  destruct x; auto.
Qed.

(* single activity, sum of costs = cost of that one activity *)
Theorem aa_use_unit a x : aa_use (cons a nil) x = a_use (fst a) (snd a) x.
Proof.
  unfold aa_use.
  rewrite mapfold_step.
  auto.
Qed.

(* no activity, any samples, no cost *)
Theorem aa_uses_nil_r x : aa_uses nil x = 0.
Proof.
  induction x. auto.
  unfold aa_uses.
  unfold mapfold in *.
  simpl.
  assumption.
Qed.

(* any activities, no samples, no cost *)
Theorem aa_uses_nil_l x : aa_uses x nil = 0.
Proof.
  destruct x; auto.
Qed.

Theorem aa_uses_unit a x : aa_uses (cons a nil) x =
  mapfold add (a_use (fst a) (snd a)) x.
Proof.
  induction x.
  auto.
  unfold aa_uses in *.
  rewrite mapfold_step.
  rewrite IHx.
  clear IHx.
  rewrite aa_use_unit.
  rewrite mapfold_step.
  reflexivity.
Qed.

Theorem aa_energy_step
    (a: Activity*nat)
    (aa: list (Activity*nat))
:
  energy (cons a aa) = energy (fst a) + energy aa.
Proof.
  simpl.
  unfold mapfold.
  auto.
Qed.

Theorem contained_activities
    (aa: list (Activity*nat))
    (start stop: nat) :
  Forall (fun a => start <= est (fst a) /\ lct (fst a) <= stop) aa ->
  aa_uses aa (range start stop) = energy aa.
Proof.
  intros.
  rewrite transpose_aa_uses.
  induction H.
  auto.
  rewrite mapfold_step.
  rewrite IHForall.
  rewrite aa_energy_step.
  f_equal.
  apply contained_activity.
  apply H.
Qed.

Theorem Forall_weaken {A} (P Q: A->Prop) (aa: list A) :
  (forall a, P a -> Q a) -> Forall P aa -> Forall Q aa.
Proof.
  intros.
  induction aa.
  + constructor.
  + constructor.
    - inversion H0.
      apply (H a H3).
    - apply IHaa.
      inversion H0.
      apply H4.
Qed.

Theorem Forall_bound_weaken start1 stop1 start2 stop2 (x: list (Activity*nat)) :
  start2 <= start1 -> stop1 <= stop2 ->
  Forall (fun a => start1 <= est (fst a) /\ lct (fst a) <= stop1) x ->
  Forall (fun a => start2 <= est (fst a) /\ lct (fst a) <= stop2) x.
Proof.
  intros R S.
  apply (Forall_weaken _ _ x).
  intros a [t u].
  omega.
Qed.

Theorem aa_uses_between_est_lct_is_energy
  (aa: list (Activity*nat)) :
  aa_uses aa (range (est aa) (lct aa)) = energy aa.
Proof.
  apply contained_activities.
  induction aa.
  constructor.
  apply Forall_cons.
  constructor.
  apply Nat.le_min_l.
  apply Nat.le_max_l.
  apply (Forall_bound_weaken (est aa) (lct aa)).
  apply Nat.le_min_r.
  apply Nat.le_max_r.
  auto.
Qed.

Theorem aa_uses_between_est_lct_is_energy_2
  (aa: list Activity)
  (starts: list nat) :
  length aa = length starts ->
  aa_uses (combine aa starts) (range (est aa) (lct aa)) = energy aa.
Proof.
  intro.
  assert (length aa <= length starts).
  rewrite H.
  apply le_n.
  replace (est aa) with (est (combine aa starts)).
  replace (lct aa) with (lct (combine aa starts)).
  replace (energy aa) with (energy (combine aa starts)).
  apply aa_uses_between_est_lct_is_energy.
  simpl. unfold mapfold. rewrite urgh; auto.
  simpl. unfold mapfold. rewrite urgh; auto.
  simpl. unfold mapfold. rewrite urgh; auto.
Qed.


Theorem aa_fit_weak_th (C: nat) (* _easy in reverse *)
  (assignment: list (Activity * nat))
  (samples: list nat) :
  ((aa_fit_weak C assignment samples) -> False) ->
  ((aa_fit C assignment) -> False).
Proof.
  intros.
  apply H. clear H.
  apply aa_fit_weak_easy.
  apply H0.
Qed.

Theorem unassignableByEnergy_th (C: nat) (aa: list Activity) :
  unassignableByEnergy C aa -> unassignable C aa.
Proof.
  unfold unassignableByEnergy.
  unfold unassignable.
  intros UnaByE starts [Lenm [ValidBcA FitBcA]].

  refine (aa_fit_weak_th C (combine aa starts)
    (range (est aa) (lct aa)) _ FitBcA).
  intro FitWeak.

  unfold aa_fit_weak in FitWeak.
  rewrite (aa_uses_between_est_lct_is_energy_2 aa) in FitWeak.
  rewrite length_range in FitWeak.

  assert (forall a b, a<=b /\ b<a -> False).
  intros.
  omega.
  apply (H (energy aa) (((lct aa)-(est aa))*C)).
  split; assumption.
  assumption.
Qed.
