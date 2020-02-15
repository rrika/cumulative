Require Import List Nat PeanoNat Bool.

Definition mapfold k {A} (f: A->nat) l := fold_right k 0 (map f l).

Class Work (A: Type) :=
  {
    est      : A -> nat; (* earliest start time *)
    lct      : A -> nat; (* latest completion time *)
    energy   : A -> nat; (* resource units times time units *)
  }.

Structure Activity : Type := mkActivity
  {
    a_est : nat;
    a_lct : nat;
    a_c : nat;
    a_p : nat
    (*;a_ok : (a_lct-a_est >= a_p)*)
  }.

Instance : Work Activity :=
  {
    est := a_est;
    lct := a_lct;
    energy w := (a_c w) * (a_p w)
  }.

Instance : Work (list Activity) :=
  {
    est    := mapfold min est;
    lct    := mapfold max lct;
    energy := mapfold add energy
  }.

Instance : Work (list (Activity*nat)) :=
  {
    est    l := est (map fst l);
    lct    l := lct (map fst l);
    energy l := energy (map fst l)
  }.

Definition envelope_unit (C: nat) (activity: Activity) : nat :=
  C * est activity + energy activity.

Definition a_valid (a: Activity) (start: nat) : Prop :=
  start >= (a_est a) /\ start + (a_p a) <= (a_lct a).

Definition a_use (a: Activity) (start: nat) (sample: nat) :=
  if (start <=? sample) && (sample <? start + (a_p a))
    then a_c a
    else 0.

Definition aa_valid (assignment: list (Activity * nat)) :=
  fold_right and True (map
    (fun x => a_valid (fst x) (snd x))
    assignment).

Definition aa_use (assignment: list (Activity * nat)) (sample: nat) :=
  mapfold add (fun x => a_use (fst x) (snd x) sample) assignment.

Definition aa_fit (C: nat) (assignment: list (Activity * nat)) :=
  forall (sample: nat), aa_use assignment sample <= C.
