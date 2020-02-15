Require Import List PeanoNat.
Require Import misc.
Require Import definitions.
Require Import assignments.

Definition ends_before (C: nat) (aa: list Activity) (a b: nat)
  (LA: a < length aa)
  (LB: b < length aa) :=
  forall (starts: list nat),
    length starts = length aa ->
    let assignment := combine aa starts in
    aa_valid assignment /\ aa_fit C assignment ->
    let end_a := nth a starts 0 + (a_p (nthi a aa LA)) in
    let end_b := nth b starts 0 + (a_p (nthi b aa LB)) in
    end_a < end_b.

Definition ends_before_time_task (C: nat) (aa: list Activity) (end_a: nat) (b: nat)
  (LB: b < length aa) :=
  forall_assignments C aa (fun starts assignment =>
    let end_b := nth b starts 0 + (a_p (nthi b aa LB)) in
    end_a < end_b).

Definition ends_before_task_time (C: nat) (aa: list Activity) (a: nat) (end_b: nat)
  (LA: a < length aa) :=
  forall_assignments C aa (fun starts assignment =>
    let end_a := nth a starts 0 + (a_p (nthi a aa LA)) in
    end_a < end_b).

Theorem ends_before_transitive_task_time_task
  {C: nat} {aa: list Activity}
  {a: nat} {end_b: nat} {c: nat} {LA: a < length aa} {LC: c < length aa}
  (lhs: ends_before_task_time C aa a end_b LA)
  (rhs: ends_before_time_task C aa end_b c LC) :
  ends_before C aa a c LA LC.
Proof.
  unfold ends_before.
  intros starts AllAssignH0 AllAssignH1.
  specialize (lhs starts AllAssignH0 AllAssignH1).
  specialize (rhs starts AllAssignH0 AllAssignH1).
  simpl in *.
  clear AllAssignH0 AllAssignH1.
  intuition.
Qed.

Theorem ends_before_transitive_task_time_time
  {C: nat} {aa: list Activity} {a: nat} (x: nat) {y: nat} {LA: a < length aa} :
  x <= y ->
  ends_before_task_time C aa a x LA ->
  ends_before_task_time C aa a y LA.
Proof.
  intros.
  intro.
  intros.
  specialize (X starts H0 H1).
  simpl in X.
  remember (nth a starts 0 + a_p (nthi a aa LA)).
  clear Heqn.
  subst end_a.
  clear C LA aa starts assignment H0 H1.
  intuition.
Qed.

Theorem ends_before_task_time_lct
  {C: nat} {aa: list Activity} {a: nat} {LA: a < length aa} :
  ends_before_task_time C aa a (S (lct (nthi a aa LA))) LA.
Proof.
  intro.
  intros.
  cut (a < length assignment). intro LAS.
  cut (a < length starts). intro LS.
  subst end_a.
  destruct H0.
  clear H1.
  unfold aa_valid in H0.

  pose proof (fold_and_pick a LAS H0). clear H0.
  simpl in H1.
  replace (fst (nthi a assignment LAS)) with (nthi a aa LA) in *.
  replace (snd (nthi a assignment LAS)) with (nthi a starts LS) in *.
  unfold a_valid in H1.
  destruct H1.
  replace (nth a starts 0) with (nthi a starts LS).
  simpl in *.
  intuition.
  rewrite (nthinth a starts 0).
  reflexivity.
  subst assignment.
  rewrite (nthi_combine a aa starts LA LS).
  reflexivity.
  auto.
  rewrite (nthi_combine a aa starts LA LS).
  reflexivity.
  auto.
  rewrite H.
  auto.
  subst assignment.
  rewrite List.combine_length.
  rewrite H.
  rewrite Nat.min_id.
  auto.
Qed.

Theorem ends_before_transitive_task_lct_time
  {C: nat} {aa: list Activity} {a: nat} {LA: a < length aa} {plct} :
  (S (lct (nthi a aa LA))) <= plct ->
  ends_before_task_time C aa a plct LA.
Proof.
  intros.
  apply (ends_before_transitive_task_time_time (S (lct (nthi a aa LA)))).
  apply H.
  apply ends_before_task_time_lct.
Qed.

(*
    for a1,a2,a3 of LCut(plct)
    end a1 <
    end a2 < end b
    end a3 <
*)
Definition precEntry (C: nat) (aa: list Activity) (plct: nat) (b: nat)
  (LB: b < length aa)
  :=
  forall (LCut_a: nat) (LA: LCut_a < length aa)
    (a_in_LCut: lct (nthi LCut_a aa LA) < plct),
      ends_before C aa LCut_a b LA LB.

(*
    for a1,a2,a3 of LCut(plct)
    end task1 <
    end task2 < plct <= end b
    end task3 <
*)
Theorem precEntryBuild {C: nat} {aa: list Activity} (plct: nat) (b: nat)
  (LB: b < length aa) :
  (forall a (LA: a < length aa) (a_in_LCut: lct (nthi a aa LA) < plct),
    ends_before_task_time C aa a plct LA) ->
  ends_before_time_task C aa plct b LB ->
  precEntry C aa plct b LB.
Proof.
  intros.
  unfold precEntry.
  intros.
  eapply (@ends_before_transitive_task_time_task).
  apply X.
  apply a_in_LCut.
  apply X0.
Qed.

Fixpoint maxOverSubsets {A} (l: list A) (f: list A -> nat) {struct l} :=
  match l with | nil => f nil | cons x xs =>
    max
      (maxOverSubsets xs f)
      (maxOverSubsets xs (fun r => f (cons x r)))
  end.

Theorem maxOverSubsetsFirst {A} (a: A) (l: list A) (f: list A -> nat) :
  maxOverSubsets (cons a l) f =
  max
    (f (cons a nil))
    (maxOverSubsets (cons a l) f).
Proof.
  induction l.
  - simpl.
    rewrite Nat.max_comm at 2.
    rewrite Nat.max_assoc.
    rewrite Nat.max_id.
    rewrite Nat.max_comm.
    reflexivity.
  - simpl in *.
    rewrite maxShuffle.
    rewrite IHl at 1.
    rewrite <- Nat.max_assoc.
    reflexivity.
Qed.

Theorem maxOverSubsetsRel_allRel_useless
  {A} (l: list A) (f: list A -> nat) (x: nat) :
  maxOverSubsets l f <= x -> Forall (fun a => (f (cons a nil)) <= x) l.
Proof.
  induction l. constructor.
  intro mOS.
  constructor.
  - rewrite maxOverSubsetsFirst in mOS.
    apply Nat.max_lub_l in mOS.
    apply mOS.
  - apply IHl. clear IHl.
    simpl in mOS.
    apply Nat.max_lub_l in mOS.
    apply mOS.
Qed.

Theorem maxOverSubsetsRel_allRel
  {A} (l: list A) (f: list A -> nat) (g: list A -> nat) (x: nat) :
  maxOverSubsets l f <= x -> Forall (fun a => (f (cons a nil)) <= x) l.
Proof.
  induction l. constructor.
  intro mOS.
  constructor.
  - rewrite maxOverSubsetsFirst in mOS.
    apply Nat.max_lub_l in mOS.
    apply mOS.
  - apply IHl. clear IHl.
    simpl in mOS.
    apply Nat.max_lub_l in mOS.
    apply mOS.
Qed.

Fixpoint envelope (C: nat) (aa: list Activity) :=
  maxOverSubsets aa (fun aa => C * (est aa) + (energy aa)).

Definition LCut (aa: list Activity) (plct: nat) :=
  filter (fun a => lct a <=? plct) aa.

Definition edgeFindingOne :=
  forall (C: nat) (aa: list Activity) (plct: nat) (b: nat) (LB: b < length aa),
    let ba := nthi b aa LB in

    plct < lct ba ->
    envelope C (cons ba (LCut aa plct)) > C * plct ->
    precEntry C aa plct b LB.
(*
    plct < lct ba ->
    envelope C (cons ba (LCut aa plct)) > C * plct ->
  forall a
    lct (nth a aa dummyActivity) < plct ->
    ends_before C aa a b LA LB.
*)

Theorem edgeFindingOneTh : edgeFindingOne.
Proof.
  unfold edgeFindingOne.
  intros.
  apply precEntryBuild.
  (* everything ending before or at plct ends before plct *)
    intros.
    intros.
    (* end task <= lct task <= plct*)
    apply ends_before_transitive_task_lct_time.
    intuition.
  (* and b ends afterwards *)
    admit.
Admitted.