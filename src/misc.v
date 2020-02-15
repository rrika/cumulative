Require Import Coq.Program.Tactics.
Require Import List Arith.

Program Fixpoint nthi {A: Type} (i: nat) (l: list A) (in_bound: i < length l) : A :=
  match l with
  | nil => _
  | cons head tail =>
    match i with
    | 0   => head
    | S n => nthi n tail _
    end
  end.
Next Obligation.
  exfalso.
  inversion in_bound.
Defined.
Next Obligation.
  intuition.
Defined.

Theorem nthinth {A: Type} (i: nat) (l: list A) (def: A) {in_bound: i < length l} :
  nthi i l in_bound = nth i l def.
Proof.
  generalize dependent i.
  induction l.
  inversion in_bound.
  intros.
  destruct i.
  reflexivity.
  simpl.
  apply (IHl i).
Qed.

Theorem nthi_map {A B: Type} (i: nat) (l: list A) (f: A->B)
  (LI: i < length l) (FI: i < length (map f l)) :
  f (nthi i l LI) = (nthi i (map f l) FI).
Proof.
  generalize dependent l.
  induction i.
  destruct l.
  inversion LI.
  reflexivity.
  intros.
  destruct l.
  inversion LI.
  simpl.
  apply IHi.
Qed.

Theorem combine_length {A B} (aa: list A) (b: B) (bb: list B) :
  length aa <= length bb ->
  combine aa bb = combine aa (cons b bb).
Proof.
Admitted.

Theorem combine_length2 {A B} (a: A) (aa: list A) (bb: list B) :
  length bb <= length aa ->
  combine aa bb = combine (cons a aa) bb.
Proof.
Admitted.

Theorem urgh {A B} (aa: list A) (bb: list B) :
  length aa <= length bb -> map fst (combine aa bb) = aa.
Proof.
  intro.
  induction aa, bb; auto.
  inversion H.
  simpl.
  f_equal.
  rewrite (combine_length aa b).
  apply IHaa.
  apply le_Sn_le.
  apply H.
  apply le_S_n.
  apply H.
Qed.


Theorem urgh2 {A B} (aa: list A) (bb: list B) :
  length bb <= length aa -> map snd (combine aa bb) = bb.
Proof.
  intro.
  induction bb, aa; auto.
  inversion H.
  rename a into b.
  rename a0 into a.
  simpl.
  f_equal.
  rewrite (combine_length2 a aa).
  apply IHbb.
  apply le_Sn_le.
  apply H.
  apply le_S_n.
  apply H.
Qed.

Theorem nthi_combine {A B: Type} (i: nat) (l: list A) (m: list B) :
  forall
  (LI: i < length l) (MI: i < length m) (LMI: i < length (combine l m ))
  (LM: length l = length m),
  nthi i (combine l m) LMI = (nthi i l LI, nthi i m MI).
Proof.
  intros.
  enough (fst (nthi i (combine l m) LMI) = nthi i l LI).
  enough (snd (nthi i (combine l m) LMI) = nthi i m MI).
  destruct (nthi i (combine l m) LMI) eqn:Z.
  rewrite <- H.
  rewrite <- H0.
  reflexivity.

  clear H.
  pose proof (@nthi_map (A*B) B i (combine l m) snd LMI).
  replace (map snd (combine l m)) with (m) in H.
  specialize (H MI).
  assumption.
  rewrite urgh2.
  reflexivity.
  rewrite LM.
  constructor.
  pose proof (@nthi_map (A*B) A i (combine l m) fst LMI).
  replace (map fst (combine l m)) with (l) in H.
  specialize (H LI).
  assumption.
  rewrite urgh.
  reflexivity.
  rewrite LM.
  constructor.
Qed.

Fixpoint range0 (up: nat) (dn: nat) : list nat :=
  match dn with | 0 => nil | S x => (cons up (range0 (S up) x)) end.

Definition range (start stop: nat) : list nat :=
  map (fun x => x+start) (range0 0 (stop-start)).

Theorem length_map (A B: Type) (f: A->B) (aa: list A) :
  length (map f aa) = length aa.
Proof.
  induction aa; simpl; auto.
Qed.

Theorem length_range0 (n: nat) : length (range0 0 n) = n.
Proof.
  generalize 0.
  induction n.
  auto.
  intro xx.
  simpl.
  pose proof (IHn (S xx)).
  auto.
Qed.

Theorem length_range (start stop: nat) : length (range start stop) = stop-start.
Proof.
  unfold range.
  rewrite -> length_map.
  rewrite -> length_range0.
  reflexivity.
Qed.

Theorem stupid_addition_theorem_I_can_find_in_the_stdlib (x a b c d: nat) :
  a+b = c+d -> x+a+b = x+c+d.
Proof.
  induction x.
  auto.
  intro.
  simpl in *.
  pose proof (IHx H).
  auto.
Qed.

Theorem fold_and_pick {A} {F} {l: list A} (i: nat) (LI: i < length l):
  fold_right and True (map F l) ->
  F (nthi i l LI).
Proof.
  generalize dependent l.
  induction i.
  destruct l.
  (* empty list not possible, index witnesses at least one element *)
  inversion LI.
  intros.
  (* non empty list, either we found our element (index=0) *)
  unfold nthi.
  destruct H.
  apply H.
  (* or it's further along (index = i+1) *)
  intros.
  simpl.
  destruct l.
  (* this list has zero elements *)
    (* that's not possible *)
    inversion LI.
  (* this list has more elements *)
    intros.
    (* IHi takes a (LI: i < length l), which is a big eq_ind
       expression in the goal, instead of typing it out, apply
       will pick it up automatically *)
    apply IHi.
    destruct H.
    apply H0.
Qed.

Theorem maxShuffle a b c d : max (max a b) (max c d) = max (max a c) (max b d).
Proof.
  rewrite Nat.max_assoc.
  rewrite Nat.max_assoc.
  f_equal.
  rewrite <- Nat.max_assoc.
  rewrite <- Nat.max_assoc.
  f_equal.
  apply Nat.max_comm.
Qed.
