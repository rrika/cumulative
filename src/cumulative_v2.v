Require Import Coq.Program.Equality.
Require Import Lia.

Structure Activity : Type := mkActivity
  {
    a_est : nat;
    a_lct : nat;
    a_c : nat;
    a_p : nat
  }.

Definition A := Activity.
Definition AA := list A.

Inductive Update (c p: nat) (oe ol: nat) (ne nl: nat) : AA -> AA -> Type :=
| u1 a xs ys : Update c p oe ol ne nl xs ys ->
               Update c p oe ol ne nl (cons a xs) (cons a ys)
| u0 s       : Update c p oe ol ne nl 
                  (cons (mkActivity oe ol c p) s)
                  (cons (mkActivity ne nl c p) s).

Fixpoint l_complement (X Y: AA) {c p oe ol ne nl}
  (u: Update c p oe ol ne nl X Y) : AA
:=
  match u with
  | u1 _ _ _ _ _ _ a xs ys u' => cons a (l_complement xs ys u')
  | u0 _ _ _ _ _ _ s => cons (mkActivity oe (ne + p - 1) c p) s
  end.

Definition u_l_complement (X Y: AA) {c p oe ol ne nl} (u: Update c p oe ol ne nl X Y)
  : Update c p oe ol oe (ne + p - 1) X (l_complement X Y u).
Proof.
  induction u.
  - apply u1.
    fold l_complement.
    apply IHu.
  - apply u0.
Qed.

Require Import List Nat PeanoNat Bool.

Definition mapfold k {A} (f: A->nat) l := fold_right k 0 (map f l).

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

Theorem sum_pair_sums {A} (l: list A) (f g: A -> nat) :
  mapfold add f l +
  mapfold add g l =
  mapfold add (fun x => f x + g x) l.
Proof.
  induction l.
  - auto.
  - unfold mapfold in *. simpl.
    rewrite <- IHl.
    lia.
Qed.

(* Definition load_accurate  (aa: AA) (est: nat) (lct: nat) : nat :=
  mapfold add (fun a => (a_c a) * min
    ((a_lct a) - (a_est a))
    (min
      (a_p a + lct - a_lct a)
      (a_p a + a_est a - est)
  )) aa. *)

Definition load1 (est: nat) (lct: nat) (a: A) : nat :=
  if est <=? a_est a then
    if a_lct a <=? lct then
      (a_c a) * (a_p a)
    else 0
  else 0.

Definition load (aa: AA) (est: nat) (lct: nat) : nat :=
  mapfold add (load1 est lct) aa.

Fixpoint load_sample (aa: AA) (ss: list nat) (sample: nat) : nat :=
  match (aa, ss) with
  | (nil, nil) => 0
  | ((cons a aa'), (cons s ss')) => (a_use a s sample) + (load_sample aa' ss' sample)
  | ((cons _ _), nil) => 0
  | (nil, (cons _ _)) => 0
  end.

Inductive ProofStep (C: nat) (X: AA) (c p: nat) (oe ne l: nat) : Type :=
| ps_tighten_est_plain :
    load X oe (ne + p - 1) + c*p > C * (ne + p - 1 - oe) ->
    ne + p <= l -> (* could extract this from InBounds *)
    ProofStep C X c p oe ne l
| ps_tighten_est_partial xe xl nep :
    S nep = ne ->
    xe <= oe ->
    xl <  oe + p ->
    oe <= ne -> (* could extract this from InBounds *)
    ne + p <= l -> (* could extract this from InBounds *)
    load X xe xl + c * (xl - nep) > C * (xl - xe) ->
    ProofStep C X c p oe ne l.

Inductive Proof (C: nat) : AA -> AA -> Type :=
| p_id X : Proof C X X
| p_step X Y Z c p oe ne l:
  Proof C X Y ->
  Update c p oe l ne l Y Z -> ProofStep C Y c p oe ne l ->
  Proof C X Z.

Theorem load_sample_equ X Y {c p oe ol ne nl} : Update c p oe ol ne nl X Y -> forall ss t, load_sample X ss t = load_sample Y ss t.
Proof.
  intro u.
  induction u; intros.
  simpl.
  destruct ss.
  reflexivity.
  rewrite (IHu ss).
  reflexivity.
  reflexivity.
Qed.

Theorem load_sample_eqp C X Y : Proof C X Y -> forall ss t, load_sample X ss t = load_sample Y ss t.
Proof.
  intro p.
  induction p; intros.
  reflexivity.
  rewrite (IHp ss).
  apply (load_sample_equ Y Z u).
Qed.

Inductive InBounds : AA -> list nat -> Type :=
| ib1 a aa s ss :
  InBounds aa ss ->
  a_est a <= s ->
  s + a_p a <= a_lct a ->
  InBounds (cons a aa) (cons s ss)
| ib0 : InBounds nil nil.

Theorem InBoundsC (a: A) (aa: AA) (s: nat) (ss: list nat) :
  InBounds (cons a aa) (cons s ss) -> InBounds aa ss.
Proof.
  intro.
  inversion H.
  auto.
Qed.

Theorem InBounds_same_length {aa ss} (I: InBounds aa ss) : length aa = length ss.
Proof.
  induction I.
  simpl.
  f_equal.
  assumption.
  auto.
Qed.


Inductive SelectWithStartTimes : A -> nat -> AA -> list nat -> Type :=
| sws1 xa xs a s aa ss :
  SelectWithStartTimes xa xs aa ss ->
  a_est a <= s ->
  s + a_p a <= a_lct a ->
  SelectWithStartTimes xa xs (cons a aa) (cons s ss)
| sws0 a s aa ss :
  a_est a <= s ->
  s + a_p a <= a_lct a ->
  InBounds aa ss ->
  SelectWithStartTimes a s (cons a aa) (cons s ss).

Theorem split_InBounds (X Y: AA) {c p oe ne l}
  (u: Update c p oe l ne l X Y) (ss: list nat)
  (BX: InBounds X ss) :
    (InBounds Y ss) +
    (InBounds (l_complement X Y u) ss).
Proof.
  dependent induction u.
  - (* u1, current item is same, differences later *)
    (* ss must be at least as long *)
    destruct ss.
    (* so reject ss = nil case *)
    inversion BX.
    (* further down, are we on left or right path *)
    destruct (IHu ss); clear IHu.
    inversion BX; auto.
    + left. (* stay left *)
      inversion BX.
      subst.
      apply ib1.
      assumption.
      assumption.
      assumption.
    + right. (* stay right *)
      inversion BX.
      subst.
      apply ib1.
      assumption.
      assumption.
      assumption.
  - (* u0, this is the differing item, decides between left or right *)
    (* again, pick a starting time from the non-empty list ss *)
    destruct ss; inversion BX.
    simpl in *.
    (* the two scenarios, s < ne or ne <= s *)
    destruct (ne <=? s0) eqn:C.
    apply Nat.leb_le in C. (* new est < s *)
    left.
    apply ib1.
    assumption.
    simpl.
    subst.
    assumption.
    simpl.
    assumption.
    apply Nat.leb_gt in C. (* s <= new est *)
    right.
    apply ib1.
    assumption.
    simpl.
    assumption.
    simpl.
    subst.
    clear H3.
    lia.
Qed.

Fixpoint summap {A} (f: A->nat) (aa: list A) := match aa with
| nil => 0
| cons a aa' => (f a) + summap f aa'
end.

Theorem summap_mapfold {A} f l :
  mapfold add f l = @summap A f l.
Proof.
  unfold mapfold.
  induction l.
  auto.
  simpl.
  f_equal.
  assumption.
Qed.

Definition update_diff (f: A->nat) (X Y: AA)
  {c p oe ol ne nl} (u: @Update c p oe ol ne nl X Y) :
  { n : nat |
    summap f X = n + (f (mkActivity oe ol c p)) /\
    summap f Y = n + (f (mkActivity ne nl c p))
  }.
Proof.
  induction u.
  destruct IHu.
  (* n shall be the sum of all f of items except the changed one,
     up to the current one.
     x which was split out of IHu is that sum up to the previous element.
     n shall be x plus what this item adds (as it is not the changed one) *)
  exists (f a + x).
  destruct a0.
  constructor; simpl; lia.
  (* everything below here is the same *)
  exists (summap f s).
  simpl.
  lia.
Qed.

Definition update_relate
  (f g h: A->nat)
  (_X Y: AA)
  {c p oe ol ne nl} (u: @Update c p oe ol ne nl _X Y)
  (Hfh: forall i, f i < h i)
  (Hgh: forall i,
    a_est i = ne ->
    a_lct i = nl ->
    a_c i = c ->
    a_p i = p ->
    f i + g i < h i)
:
  summap f Y + (g (mkActivity ne nl c p)) <= summap h Y.
Proof.
  induction u; simpl in *.
  - specialize (Hfh a).
    lia.
  - specialize (Hgh {| a_est := ne; a_lct := nl; a_c := c; a_p := p |}).
    simpl in *.
    repeat specialize (Hgh eq_refl).
    remember ({| a_est := ne; a_lct := nl; a_c := c; a_p := p |}) as a.
    enough (summap f s <= summap h s).
    lia.
    clear c p oe ol ne nl a Heqa Hgh.
    induction s.
    auto.
    simpl.
    specialize (Hfh a).
    lia.
Qed.

Definition update_relate_2
  (f g: A->nat) (h: A->nat->nat)
  {a: A} {s: nat}
  {X: AA} {ss: list nat}
  (u: SelectWithStartTimes a s X ss)
  (Hfh: forall i s,
    InBounds (cons i nil) (cons s nil) ->
    f i <= h i s)
  (Hgh: f a + g a <= h a s)
:
  summap f X + (g a) <= summap (fun a_s => h (fst a_s) (snd a_s)) (combine X ss).
Proof.
  induction u; simpl in *.
  - specialize (Hfh a s).
    assert (InBounds (a :: nil) (s :: nil)).
    apply ib1.
    apply ib0.
    assumption.
    assumption.
    specialize (Hfh H).
    lia.
  - enough (
      summap f aa <=
      summap (fun a_s : A * nat => h (fst a_s) (snd a_s)) (combine aa ss)
    ).
    lia.
    clear Hgh.
    induction i.
    + simpl.
      specialize (Hfh a0 s0).
      assert (InBounds (a0 :: nil) (s0 :: nil)).
      apply ib1.
      apply ib0.
      assumption.
      assumption.
      specialize (Hfh H).
      lia.
    + simpl.
      auto.
Qed.

(* see aa_uses *)
Fixpoint load_sample_sum (X: AA) (ss: list nat) (t: nat) (n: nat) :=
  match n with
  | 0 => 0
  | S n' => (load_sample X ss t) + (load_sample_sum X ss (S t) n')
  end.

(* integrate step function between t and t+n
   a : _____|¯¯¯|______
            s   s+(a_p a)
          ^^^^^^^^^
          t       t+n
*)
Fixpoint load1_sample_sum (a: A) (s: nat) (t: nat) (n: nat) :=
  match n with
  | 0 => 0
  | S n' => (a_use a s t) + (load1_sample_sum a s (S t) n')
  end.

Definition load1_sample_sum_abs (a: A) (s: nat) (t: nat) (u: nat) :=
  load1_sample_sum a s t (u-t).

Theorem load_sample_sum_0 (t: nat) (n: nat) :
  load_sample_sum nil nil t n = 0.
Proof.
  generalize dependent t.
  induction n.
  auto.
  intro.
  simpl.
  apply IHn.
Qed.

(* see contained_activity *)
Theorem load_sample_sum_upper_bound a s est n
:
  load_sample_sum (a::nil) (s::nil) est n <= n * (a_c a).
Proof.
  generalize dependent est.
  dependent induction n.
  simpl.
  lia.
  intro.
  simpl.
  rewrite Nat.add_0_r.
  pose proof (IHn (S est)); clear IHn.
  remember (load_sample_sum (a::nil) (s::nil) (S est) n) as X.
  enough (a_use a s est <= a_c a).
  lia.
  clear H HeqX X.
  unfold a_use.
  destruct ((s <=? est) && (est <? s + a_p a)).
  lia.
  lia.
Qed.

(* split integration over time into two parts *)
(* (version for multiple activities) *)
(*    0   n   n+m *)
(*    ^^^^        *)
(* +      ^^^^    *)
(* =  ^^^^^^^^    *)
Theorem load_sample_sum_split aa ss a n m :
  load_sample_sum aa ss a (n+m) =
  load_sample_sum aa ss a n + load_sample_sum aa ss (a+n) m.
Proof.
  generalize dependent a.
  dependent induction n.
  simpl.
  intro.
  rewrite Nat.add_0_r.
  reflexivity.
  intros.
  pose proof (IHn m (S a)); clear IHn.
  rewrite <- Plus.plus_Snm_nSm.
  simpl in *.
  rewrite <- Nat.add_assoc.
  f_equal.
  assumption.
Qed.

Theorem load1n_sample_sum a s t n:
  load_sample_sum (a :: nil) (s :: nil) t n =
  load1_sample_sum a s t n.
Proof.
  generalize dependent t.
  dependent induction n.
  reflexivity.
  intros.
  simpl in *.
  f_equal.
  auto.
  apply IHn.
Qed.

(* split integration over time into two parts *)
(* (version for single activity) *)
(*    0   n   n+m *)
(*    ^^^^        *)
(* +      ^^^^    *)
(* =  ^^^^^^^^    *)
Theorem load1_sample_sum_split a s t n m :
  load1_sample_sum a s t (n+m) =
  load1_sample_sum a s t n + load1_sample_sum a s (t+n) m.
Proof.
  generalize dependent t.
  dependent induction n.
  simpl.
  intro.
  rewrite Nat.add_0_r.
  reflexivity.
  intros.
  pose proof (IHn m (S t)); clear IHn.
  rewrite <- Plus.plus_Snm_nSm.
  simpl in *.
  rewrite <- Nat.add_assoc.
  f_equal.
  assumption.
Qed.

Theorem load1_sample_sum_split_abs a s t n m :
  m >= n ->
  load1_sample_sum a s t m =
  load1_sample_sum a s t n + load1_sample_sum a s (t+n) (m-n).
Proof.
  intro.
  rewrite <- load1_sample_sum_split.
  replace (n + (m-n)) with m.
  reflexivity.
  lia.
Qed.

Theorem load1_sample_sum_abs_split_abs a s t u v :
  t <= u -> u <= v ->
  load1_sample_sum_abs a s t v =
  load1_sample_sum_abs a s t u + load1_sample_sum_abs a s u v.
Proof.
  intros.
  unfold load1_sample_sum_abs.
  rewrite (load1_sample_sum_split_abs a s t (u-t) (v-t)).
  f_equal.
  replace (t+(u-t)) with u by lia.
  replace (v-t-(u-t)) with (v-u) by lia.
  reflexivity.
  lia.
Qed.

(*         s    s+p        *)
(* ________|¯¯¯¯|____      *)
(*   ^^^^^                 *)
(*   t   t+n               *)
(* integration over t..t+n *)
(* always gives zero       *)

Theorem load1_sample_sum_prior a s t n:
  t+n <= s ->
  0 = load1_sample_sum a s t n.
Proof.
  intros.
  generalize dependent t.
  induction n.
  auto.
  intros.
  simpl.
  unfold a_use.
  destruct (s <=? t) eqn:J.
  destruct (t <? s + a_p a) eqn:K.
  apply Nat.leb_le in J.
  lia.
  simpl.
  apply (IHn (S t)).
  lia.
  simpl.
  apply (IHn (S t)).
  lia.
Qed.

(*     s    s+p            *)
(* ____|¯¯¯¯|_________     *)
(*            ^^^^^        *)
(*            t   t+n      *)
(* integration over t..t+n *)
(* always gives zero       *)

Theorem load1_sample_sum_past a s t n:
  t >= s + a_p a ->
  0 = load1_sample_sum a s t n.
Proof.
  intros.
  generalize dependent t.
  induction n.
  auto.
  intros.
  simpl.
  unfold a_use.
  destruct (s <=? t) eqn:J.
  destruct (t <? s + a_p a) eqn:K.
  apply Nat.ltb_lt in K.
  lia.
  simpl.
  apply (IHn (S t)).
  lia.
  apply Nat.leb_gt in J.
  lia.
Qed.

(*     s        s+p        *)
(* ____|¯¯¯¯¯¯¯¯|____      *)
(*       ^^^^^^            *)
(*       t   t+n           *)
(* integration over t..t+n *)
(* always gives c*n        *)

Theorem load1_sample_sum_aligned_ a s t n:
  t >= s ->
  t + n <= s + a_p a ->
  n * a_c a <= load1_sample_sum a s t n.
Proof.
  intros.
  generalize dependent t.
  induction n.
  auto.
  intros.
  simpl.
  unfold a_use.
  destruct (s <=? t) eqn:J.
  destruct (t <? s + a_p a) eqn:K.
  simpl.
  pose proof (IHn (S t)).
  apply Plus.plus_le_compat_l.
  apply H1.
  lia.
  lia.
  apply Nat.ltb_ge in K.
  lia.
  apply Nat.leb_gt in J.
  lia.
Qed.

(*     s        s+p        *)
(* ____|¯¯¯¯¯¯¯¯|____      *)
(*     ^^^^^^^^^^          *)
(*     t=s      t+n=s+p    *)
(* integration over t..t+n *)
(* always gives c*p=c*n    *)
Theorem load1_sample_sum_aligned a s : 
  a_p a * a_c a <= load1_sample_sum a s s (a_p a).
Proof.
  apply load1_sample_sum_aligned_.
  lia.
  lia.
Qed.

(* UPDATE: the thing (I think?) I *)
(* should've been proving is about*)
(* these scenarios:               *)
(*                       v        *)
(*    ---|         :     |--      *)
(* 10 ___|¯¯¯¯¯¯¯¯¯|________  10  *)
(* 12 _____|¯¯¯¯¯¯¯:¯|______   8  *)
(* 14 _______|¯¯¯¯¯:¯¯¯|____   6  *)
(* 16 _________|¯¯¯:¯¯¯¯¯|__   4  *)
(*                                *)
(* characterized by lct-p <= mid  *)
(* in this case the integral is   *)
(* no longer piecewise linear in  *)
(* s but on the whole domain      *)
(* /UPDATE                        *)

(* s  est=10   mid=20 lct=26 f(s) *)
(*                       v        *)
(*    ---|         :     |--      *)
(* 10 ___|¯¯¯¯¯|___:________  6   *)
(* 12 _____|¯¯¯¯¯|_:________  6   *)
(* 14 _______|¯¯¯¯¯|________  6   *)
(* 16 _________|¯¯¯:¯|______  4   *)
(* 18 ___________|¯:¯¯¯|____  2   *)
(* 20 _____________|¯¯¯¯¯|__  0   *)
(*       ^^^^^^^^^^^          |   *)
(*          minimum of f -----´   *)
(*          is 0                  *)

(* s  est=10  mid=20 lct=22  f(s) *)
(*                   v            *)
(*    ---|         : |------      *)
(* 10 ___|¯¯¯¯¯|___:________  6   *)
(* 12 _____|¯¯¯¯¯|_:________  6   *)
(* 14 _______|¯¯¯¯¯|________  6   *)
(* 16 _________|¯¯¯:¯|______  4   *)
(*       ^^^^^^^^^^^          |   *)
(*            minimum of -----´   *)
(*            is 4                *)

(* the closed form of this minimum is *)
(*   l = max(mid + p - lct, 0) *)

(* 1. show f(s) >= f(s+1)         *)
(*                    ... ___ 6 ^ *)
(*        monotonic   ... ___ 6 ^ *)
(*                    ... ___ 4 ^ *)
(*                    ... ___ 2 ^ *)

(* 2. for the highest allowed s = lct-p: *)
(*    f(lct-p) = l *)
(*                  lct           *)
(*                   v            *)
(*    ---|         : |------      *)
(* 16 _________|¯¯¯:¯|______  4   *)
(*                   ^            *)
(*             aligned at end     *)

(* 3. induction on the s, but from lct-p downwards?  *)
(*    InBounds object gives guarantee that s will be *)
(*    no higher or lower that est/lct                *)

Ltac especialize H2 :=
  match goal with
  | H2 : ?a -> ?b |- _ =>
      let H := fresh in
      assert (H: a); [|specialize (H2 H); clear H]
  end.

Ltac post_relb_to_rel_cleanup H :=
  match goal with
  | H : ?a /\ ?b |- _ => destruct H
  | _ => idtac
  end.

(* this should be a hints database shouldn't it? *)
Ltac relb_to_rel :=
  match goal with
  | H : (?a <=? ?b) = true  |- _ => apply Nat.leb_le in H; post_relb_to_rel_cleanup H
  | H : (?a <=? ?b) = false |- _ => apply Nat.leb_gt in H; post_relb_to_rel_cleanup H
  | H : (?a <? ?b)  = true  |- _ => apply Nat.ltb_lt in H; post_relb_to_rel_cleanup H
  | H : (?a <? ?b)  = false |- _ => apply Nat.ltb_ge in H; post_relb_to_rel_cleanup H
  | H : (?a && ?b) = true  |- _ => apply andb_true_iff in H; post_relb_to_rel_cleanup H
  | H : (?a && ?b) = false |- _ => apply andb_false_iff in H; post_relb_to_rel_cleanup H
  | H : (?a || ?b) = true  |- _ => apply orb_true_iff in H; post_relb_to_rel_cleanup H
  | H : (?a || ?b) = false |- _ => apply orb_false_iff in H; post_relb_to_rel_cleanup H
  | H : true = ?x          |- _ => symmetry in H; post_relb_to_rel_cleanup H
  | H : false = ?x         |- _ => symmetry in H; post_relb_to_rel_cleanup H
  end.

Ltac destroy_one_bool :=
  let B := fresh in
  match goal with
  | [ |- context [?a]] =>
    match a with
    | true => fail 1
    | false => fail 1
    | _ =>
      match type of a with
      | bool => destruct a eqn:B
      end
    end
  end.

Ltac destroy_bools_on_sight :=
  repeat destroy_one_bool; repeat relb_to_rel.


Theorem load1_sample_sum_cost_bound_by_time a s t n :
  load1_sample_sum a s t n <= n * a_c a.
Proof.
  generalize dependent t.
  induction n.
  reflexivity.
  intro t.
  specialize (IHn (S t)).
  simpl.
  enough (a_use a s t <= a_c a).
  lia.
  clear IHn.
  unfold a_use.
  destroy_bools_on_sight; lia.
Qed.

Theorem load1_sample_sum_aligned_sandwich a s :
  load1_sample_sum a s s (a_p a) = (a_p a) * a_c a.
Proof.
  pose proof (load1_sample_sum_cost_bound_by_time a s s (a_p a)).
  pose proof (load1_sample_sum_aligned a s).
  lia.
Qed.
(*
Theorem load1_sample_sum_sub (a: A) (s: nat) (t: nat) (n: nat) (offset: nat) :
  s >= offset ->
  t >= offset ->
  load1_sample_sum a s t n = 
  load1_sample_sum a (s-offset) (t-offset) n.
Proof.
  intros.
  generalize dependent t.
  induction n.
  reflexivity.
  intros.
  simpl.
  f_equal.

  unfold a_use.
  replace (s - offset <=? t - offset) with (s <=? t).
  replace (t - offset <? s - offset + a_p a) with (t <? s + a_p a).
  reflexivity.
  destroy_bools_on_sight; [reflexivity|lia|lia|reflexivity].
  destroy_bools_on_sight; [reflexivity|lia|lia|reflexivity].

  replace (S (t-offset)) with (S t-offset) by lia.
  apply IHn; clear IHn.
  lia.
Qed.
*)

Theorem load1_sample_sum_contained_eq (a:A) (s t n: nat) :
  t <= s ->
  t + n >= s + a_p a ->
  a_c a * a_p a = load1_sample_sum_abs a s t (t+n).
Proof.
  intros.
  rewrite (load1_sample_sum_abs_split_abs a s t s (t+n)) by lia.
  rewrite (load1_sample_sum_abs_split_abs a s s (s+a_p a) (t+n)) by lia.
  replace (load1_sample_sum_abs a s t s) with 0.
  replace (load1_sample_sum_abs a s (s + a_p a) (t + n)) with 0.
  assert (forall i, 0+(i+0) = i) by lia; rewrite H1; clear H1.
  unfold load1_sample_sum_abs.
  replace (s + a_p a - s) with (a_p a) by lia.
  rewrite (load1_sample_sum_aligned_sandwich).
  lia.
  apply (load1_sample_sum_past); lia.
  apply (load1_sample_sum_prior); lia.
Qed.

Theorem nat_rec_reverse
  (P : nat -> Type)
  (last: nat)
  (Pbeyond:    forall n, last < n -> P n)
  (Pboundary:  P last)
  (Pinduction: forall n, n < last -> P (S n) -> P n)
:
  forall n : nat, P n.
Proof.
  intro.
  destruct (last <? n) eqn:J; relb_to_rel.
  apply (Pbeyond n J).

  clear Pbeyond.
  remember (last-n) as i.
  dependent induction i generalizing n J.
  replace n with last by lia.
  apply Pboundary.
  assert (n < last) by lia. clear J.
  apply Pinduction.
  apply H.
  apply IHi.
  lia.
  lia.
Qed.

Theorem load1_sample_sum_right_truncated_monotonic (a:A) (s t n: nat) :
  t + n < s + a_p a ->
  load1_sample_sum a s t n >= load1_sample_sum a (S s) t n.
Proof.
  intro.
  generalize dependent t.
  dependent induction n.
  auto.

  intros.
  specialize (IHn (S t)).
  especialize IHn; try lia.

  (* IHn:  load[s,t+1,n] >= load[s+1,t+1,n] *)
  (* s   t+1 n       [####]    3  ^ *)
  (* s+1 t+1 n       [ ###]##  2  ^ *)

  (* goal: load[s,t,n+1] >= load[s+1,t+1,n] *)
  (* s   t   n+1   [ #####]    3  ^ *)
  (* s+1 t   n+1   [   ###]##  2  ^ *)

  (* build goal from IHn and this intermediate step *)
  (* s   t   1     []######    0  ^ *)
  (* s+1 t   1     []  ######  0  ^ *)

  (* which can be shown at all t except *)
  (* s   s+p 1       ######[]  0  v *)
  (* s+1 s+p 1         ####[]  1  v *)

  simpl.
  enough (a_use a s t >= a_use a (S s) t).
  lia.
  clear IHn.
  unfold a_use.
  destroy_bools_on_sight; try lia.
  destruct H0; relb_to_rel; lia.
Qed.

Theorem load1_sample_sum_right_truncated a s
  (BX : InBounds (a :: nil) (s :: nil))
  (t m: nat)
:
  (* |------m-----| *)
  (* |--n--|------| *)

  let n := (min (m) (a_lct a - a_p a - t)) in
  t     <= a_est a ->
  t + m <= a_lct a ->
  a_c a * (m-n) <= load1_sample_sum a s t m.
Proof.
  intros.
  inversion BX; subst; clear BX H5.
  assert (a_lct a - a_p a >= t) by lia.
  assert (n <= m) by lia.
  assert (n + (m - n) = m) by lia.
  assert (m-n <= a_p a).
    unfold n.
    destruct (Nat.min_spec m (a_lct a - a_p a - t)) as [[A B]|[A B]].
    rewrite B.
    lia.
    rewrite B.
    lia.
  (* show the base case *)
  assert (a_c a * (m-n) <= load1_sample_sum a (a_lct a - a_p a) t m) as base_case.
  - rewrite (load1_sample_sum_split_abs a (a_lct a - a_p a) t n m).

    assert (t + n <= a_lct a - a_p a).
    lia.

    rewrite <- load1_sample_sum_prior. (* needs t + n <= a_lct a - a_p a *)
    simpl.
    rewrite Nat.mul_comm.
    + destruct (n <? m) eqn:J; relb_to_rel.
      * simpl.

        apply (load1_sample_sum_aligned_ a (a_lct a - a_p a) (t + n) (m - n)).
        unfold n.
        destruct (Nat.min_spec m (a_lct a - a_p a - t)) as [[A B]|[A B]].
        rewrite B.
        exfalso. lia.
        lia.
        lia.

      * assert (n=m).
        lia.
        replace (m-n) with 0.
        simpl.
        auto.
        lia.
    + assumption.
    + lia.
  (* induction *)
  - clear H3.
    apply (nat_rec_reverse
      (fun s =>
        s         >= a_est a ->
        s + a_p a <= a_lct a ->
        a_c a * (m - n) <= load1_sample_sum a s t m)
      (a_lct a - a_p a)); intros.
    + (*beyond case*)
      lia.
    + (*boundary case*)
      apply base_case.
    + (*inductive step (reverse)*)
      clear base_case s H6 H7.
      rename n0 into s.
      rename H5 into IBleft.
      rename H8 into IBright.

      especialize H4. lia.
      especialize H4. lia.

      destruct (t + m <? s + a_p a) eqn:J; relb_to_rel.
      (* activity a touches the right end of t..t+m*)
      enough (load1_sample_sum a s t m >= load1_sample_sum a (S s) t m).
      lia.
      apply load1_sample_sum_right_truncated_monotonic.
      apply J.
      (* activity is contained *)
      replace (load1_sample_sum _ _ _ _) with (a_c a * a_p a).
      apply Mult.mult_le_compat_l.
      assumption.
      clear n H2 H4 IBleft.
      pose proof (load1_sample_sum_contained_eq a s t m).
      unfold load1_sample_sum_abs in H2.
      replace (t+m-t) with m in H2 by lia.
      apply H2; lia.
    + assumption.
    + assumption.
Qed.

Theorem load1_underestimates_load1_sample_sum a s
  (BX : InBounds (a :: nil) (s :: nil))
  (est lct: nat)
:
  load1 est lct a <= load1_sample_sum a s est (lct - est).
Proof.
  inversion BX.
  subst.
  clear H3 BX.

  unfold load1.
  destruct (est <=? a_est a) eqn:J.
  destruct (a_lct a <=? lct) eqn:K.
  - apply Nat.leb_le in J.
    apply Nat.leb_le in K.
    assert (est <= s).         lia. clear J H4.
    assert (s + a_p a <= lct). lia. clear K H5.
    replace (lct-est) with (s - est + (lct - s)).
    rewrite (load1_sample_sum_split _ _ est (s - est) (lct - s)).
    replace (load1_sample_sum a s est (s - est)) with 0.
    simpl.
    replace (est + (s - est)) with s.
    replace (lct-s) with (a_p a + (lct - (s + a_p a))).
    rewrite (load1_sample_sum_split _ _ s (a_p a) (lct - (s + a_p a))).
    replace (load1_sample_sum a s (s + a_p a) (lct - (s + a_p a))) with 0.
    rewrite Nat.add_0_r.
    rewrite Nat.mul_comm.
    apply load1_sample_sum_aligned; lia.
    apply load1_sample_sum_past; lia.
    lia.
    lia.
    apply load1_sample_sum_prior; lia.
    lia.
  - lia.
  - lia.
Qed.

Theorem load1_underestimates_load_sample_sum a s
  (BX : InBounds (a :: nil) (s :: nil))
  (est lct: nat)
:
  load1 est lct a <= load_sample_sum (a :: nil) (s :: nil) est (lct - est).
Proof.
    rewrite load1n_sample_sum.
    apply load1_underestimates_load1_sample_sum.
    apply BX.
Qed.
(*
  inversion BX.
  subst.
  clear H3 BX.
  unfold load1.
  destruct (est <=? a_est a) eqn:J.
  destruct (a_lct a <=? lct) eqn:K.
  - apply Nat.leb_le in J.
    apply Nat.leb_le in K.
    assert (est <= s).         lia. clear J H4.
    assert (s + a_p a <= lct). lia. clear K H5.
    replace (lct-est) with (s - est + (lct - s)).
    rewrite (load_sample_sum_split _ _ est (s - est) (lct - s)).
    replace (load_sample_sum (a :: nil) (s :: nil) est (s - est)) with 0.
    simpl.
    replace (est + (s - est)) with s.
    replace (lct-s) with (a_p a + (lct - (s + a_p a))).
    rewrite (load_sample_sum_split _ _ s (a_p a) (lct - (s + a_p a))).
    replace (load_sample_sum (a :: nil) (s :: nil) (s + a_p a) (lct - a_p a)) with 0.
    admit.
    admit.
    admit.
    lia.
    admit.
    lia.
  - lia.
  - lia.
Admitted.
*)

Theorem load_underestimates_load_sample X ss
  (BX : InBounds X ss)
  (est lct: nat)
:
  load X est lct <= load_sample_sum X ss est (lct - est).
Proof.
  dependent induction X.
  - inversion BX.
    rewrite load_sample_sum_0.
    auto.
  - destruct ss.
    inversion BX.
    (*enough (forall t : nat, load_sample X ss t <= C).*)
    inversion BX.
    subst.
    pose proof (IHX ss H3 est lct); clear IHX.

    replace (load (a :: X) est lct) with ((load1 est lct a) + load X est lct).
    replace (load_sample_sum (a :: X)   (n :: ss) est (lct - est))
      with ((load_sample_sum (a :: nil) (n :: nil) est (lct - est))
          + (load_sample_sum X          ss         est (lct - est))).
    enough (load1 est lct a <= load_sample_sum (a :: nil) (n :: nil) est (lct - est)).
    clear BX.
    lia.
    + (* load1 < load_sample_sum <single item> *)
      apply load1_underestimates_load_sample_sum.
      constructor.
      constructor.
      assumption.
      assumption.
    + (* split load_sample_sum *)
      remember (lct-est) as m.
      clear H5 H4 H3 H Heqm lct BX.
      generalize dependent est.
      dependent induction m.
      auto.
      intro.
      simpl in *.
      rewrite Nat.add_0_r.
      rewrite <- Nat.add_assoc.
      rewrite <- Nat.add_assoc.
      f_equal.
      pose proof (IHm (S est)); clear IHm.
      lia.
    + (* split load -> load1 + load*)
      unfold load.
      unfold mapfold.
      simpl.
      reflexivity.
Qed.

(*Fixpoint WithStartTimes_from_lists
  (aa: list Activity) (ss: list nat) (H: length aa = length ss)
:
  WithStartTimes aa ss
.
  destruct aa; destruct ss.
  apply ws0.
  inversion H.
  inversion H.
  apply ws1.
  apply WithStartTimes_from_lists.
  simpl in H.
  inversion H.
  reflexivity.
Qed.*)

Fixpoint SelectWithStartTimes_from_Update_X
  {X Y c p oe ol ne nl} (u: Update c p oe ol ne nl X Y) {ss} (I: InBounds X ss)
:
  { s:nat & SelectWithStartTimes (mkActivity oe ol c p) s X ss }
.
  generalize dependent ss.
  induction u.
  - specialize (SelectWithStartTimes_from_Update_X
      xs ys c p oe ol ne nl u).
    intros.
    inversion I.
    subst.
    specialize (SelectWithStartTimes_from_Update_X ss0 H1).
    destruct SelectWithStartTimes_from_Update_X.
    exists x.
    apply sws1.
    apply s0.
    assumption.
    assumption.

  - intros.
    destruct ss.
    inversion I.
    exists n.
    inversion I; subst.
    apply sws0; simpl in *.
    assumption.
    assumption.
    assumption.
Qed.

Theorem update_transfer_bounds
  {X Y c p oe ol ne nl} (u: Update c p oe ol ne nl X Y)
  {ss} (BX : InBounds X ss)
:
  oe + p <= ol.
Proof.
  generalize dependent Y.
  induction BX; intros.
  inversion u; subst.
  apply (IHBX ys).
  assumption.
  simpl in *.
  lia.
  inversion u.
Qed.

Theorem transpose {X ss} (BX : InBounds X ss) (est n: nat) :
  load_sample_sum X ss est n =
  summap
    (fun x_ss => load1_sample_sum (fst x_ss) (snd x_ss) est n)
    (combine X ss).
Proof.
  generalize dependent est.
  induction n.
  induction BX.
  simpl.
  clear IHBX.
  induction (combine aa ss).
  reflexivity.
  simpl.
  assumption.
  simpl.
  reflexivity.

  intros.
  simpl.
  rewrite <- summap_mapfold.
  rewrite <- sum_pair_sums.
  f_equal.
  rewrite summap_mapfold.

  clear IHn.
  induction BX.
  simpl.
  f_equal.
  apply IHBX.
  reflexivity.
  specialize (IHn (S est)).
  rewrite summap_mapfold.
  apply IHn.
Qed.

(* if load_underestimates_load_sample was so good, why didn't they make *)
Theorem load_underestimates_load_sample_2_impl
  a s aa ss (sws : SelectWithStartTimes a s aa ss) est lct rrr
:
  est <= lct ->
  est <= (a_est a) ->
  lct <  (a_lct a) ->
  (a_est a) + (a_p a) > lct ->
  rrr <= ((lct - est)-(min (lct-est) ((a_lct a)-(a_p a)-est))) ->
  load1 est lct a + (a_c a) * rrr <= load1_sample_sum a s est (lct - est).
Proof.
  intros.
  induction sws.
  apply IHsws.
  assumption.
  assumption.
  assumption.
  assumption.
  replace (load1 _ _ _) with 0; simpl.
  pose proof (load1_sample_sum_right_truncated a s) as T.
  especialize T.
  constructor.
  constructor.
  assumption.
  assumption.
  specialize (T est (lct-est) H0).
  especialize T.
  replace (est+(lct-est)) with lct.
  lia.
  lia.
  assert (a_c a * rrr <= a_c a * (lct - est - min (lct - est) (a_lct a - a_p a - est))).
  apply Mult.mult_le_compat_l.
  assumption.
  lia.

  unfold load1.
  destruct (est <=? a_est a) eqn:J.
  destruct (a_lct a <=? lct) eqn:K.
  relb_to_rel.
  exfalso.
  lia.
  reflexivity.
  reflexivity.
Qed.

(* if load_underestimates_load_sample was so good, why didn't they make *)
Theorem load_underestimates_load_sample_2
  X Y c {p oe ol ne nl} (u: Update c p oe ol ne nl X Y) ss
  (BX : InBounds X ss)
  (est lct rrr: nat)
:
  est <= oe ->
  lct <  ol ->
  oe + p > lct ->
  rrr <= ((lct - est)-(min (lct-est) (ol-p-est))) ->
  load X est lct + c * rrr <= load_sample_sum X ss est (lct - est).

Proof.
  intros U V W F.
  rewrite (transpose BX); try assumption.
  unfold load.
  rewrite summap_mapfold.

  pose proof (SelectWithStartTimes_from_Update_X u BX).
  destruct H.

      destruct (lct <? est) eqn:R.
      relb_to_rel.
      assert (lct-est = 0) by lia.
      rewrite H.
      rewrite H in F; simpl in F; inversion F; clear F.
      simpl.
      rewrite Nat.mul_0_r.
      rewrite Nat.add_0_r.
      
      clear u BX.
      induction s.

      simpl.
      replace (load1 est lct a) with 0.
      lia.
      unfold load1.
      destroy_bools_on_sight.
      exfalso.
      lia.
      reflexivity.
      reflexivity.

      simpl.
      replace (load1 est lct a) with 0.
      simpl.
      induction i.
      simpl.
      replace (load1 est lct a0) with 0.
      simpl.
      apply IHi.

      unfold load1.
      destroy_bools_on_sight.
      exfalso.
      lia.
      reflexivity.
      reflexivity.
      reflexivity.

      unfold load1.
      destroy_bools_on_sight.
      exfalso.
      lia.
      reflexivity.
      reflexivity.

  remember ({| a_est := oe; a_lct := ol; a_c := c; a_p := p |}) as a.
  eapply (update_relate_2

    (* relate lower bound consisting of *)
    (* - f: other tasks:  the usual approximation (load1)    *)
    (* - g: current task: the slighter better approximation  *)
    (* and the exact load *)
    (* - h: based on concrete start times (load1_sample_sum) *)

    (*f*) (load1 est lct)
    (*g*) (fun a => _)
    (*h*) (fun x s => load1_sample_sum x s est (lct - est))
    s
  ).
  intros.
  apply load1_underestimates_load1_sample_sum.
  assumption.

  replace c with (a_c a). all: swap 1 2. subst; auto.
  apply (load_underestimates_load_sample_2_impl a x X ss s); subst; auto.
  relb_to_rel.
  assumption.
Qed.

Theorem load_sample_sum_limit C X ss
  (LX : forall t : nat, load_sample X ss t <= C)
  (BX : InBounds X ss)
  (est n: nat)
:
  load_sample_sum X ss est n <= n * C.
Proof.
  generalize dependent est.
  dependent induction n.
  simpl.
  lia.
  simpl.
  intro.
  pose proof (LX est).
  pose proof (IHn (S est)).
  lia.
Qed.

Definition tr1 (C: nat) (X Y: AA) {c p oe ne l}
  (u: Update c p oe l ne l X Y)
  (ps: ProofStep C X c p oe ne l)

  (ss: list nat) (*lens*)
  (ibx: InBounds X ss)
  (lcx: forall t, load_sample X ss t <= C) :
    InBounds Y ss.
Proof.
  (*      X                       *)
  (*    /   \                     *)
  (*   Y     Z = complement X Y   *)

  (* all tasks except one have the same bounds in all there of these *)

  (*     oe          ne         l  *)
  (* X:  |####------------------|  *)
  (* Y:              |####------|  *)
  (* Z:  |-----------####|         *)
  (*     `--overloaded--´          *)

  (* Z will be shown to only have overloaded start time assignments 
     within the range oe..(ne+p-1) *)

  destruct ps.
  - pose proof (split_InBounds X Y u ss ibx) as J.
    (* a concrete start position can either *)
    destruct J. (* valid in Y *)
    assumption. (*   easy then *)
    exfalso.    (* or valid in Z *)
                (*   in which case we'll show the contradiction *)

    (* split ∑(t of X) load1 _ _ t
         and ∑(t of Z) load1 _ _ t
       which differ in one item kX/kZ
        into load1 _ _ kX + common
         and load1 _ _ kZ + common
       where common = ∑(t of tasksX \ kX) load1 _ _ t
                    = ∑(t of tasksZ \ kZ) load1 _ _ t
       because tasksX\kX and tasksZ\kZ are the same set
    *)
    pose proof (update_diff (load1 oe (ne + p - 1)) X
      (l_complement X Y u)
      (u_l_complement X Y u)).
    destruct H as [common [H H0]].

    (* reexpress the sum as an application of 'load'.
       we have theorems that can work with that later on,
       eg. load_underestimates_load_sample.
    *)
    rewrite <- summap_mapfold in H.
    rewrite <- summap_mapfold in H0.
    fold (load X oe (ne + p - 1)) in H.
    fold (load (l_complement X Y u) oe (ne + p - 1)) in H0.

    (* focusing on the differing part of the two sums,
       the lower capacity use bound of k, they can both
       be written in simpler terms.

       The measurement range is chosen so that
       there exist start position of k within X
         for which it doesn't fully contains k, and
       for every start position of k within complement X Y
         it fully contains k *)

    (* In Z the lower bound of k within the range
       is its entire duration p times its resource usage c
         load1 _ _ kZ = c*p  *)
    replace (load1 oe (ne + p - 1)
       {| a_est := oe; a_lct := ne + p - 1; a_c := c; a_p := p |})
    with (c * p) in H0.

    (* In X the lower bound of k within the range is zero
         load1 _ _ kX = 0  *)
    replace (load1 oe (ne + p - 1)
       {| a_est := oe; a_lct := l; a_c := c; a_p := p |})
    with 0 in H.

    (* rewrite
        ∑X ... = ∑X\kX ... + 0
        ∑Z ... = ∑Z\kZ ... + c*p
       as
        ∑Z = ∑X + c*p
    *)
    rewrite Nat.add_0_r in H.
    subst common.

    (* assumption lcx says that the start times will not cause overload, so *)
    (* show H: load_sample Z _ _ <= C *)
    assert (forall t : nat, load_sample (l_complement X Y u) ss t <= C).
    intro.
    rewrite <- (load_sample_equ X (l_complement X Y u) (u_l_complement X Y u)).
    apply (lcx t).


    (* show g: load X _ _ + c*p > overloadlevel *)
      (* was contained in the ProofStep *)

    (* show H1: load Z _ _ <= ∑t load_sample Z _ t *)
    clear lcx.
    pose proof (load_underestimates_load_sample (l_complement X Y u) ss i oe (ne + p - 1)).

    (* show H2: ∑t load_sample Z _ t <= overload *)
    pose proof (load_sample_sum_limit C (l_complement X Y u) ss H i oe (ne + p - 1 - oe)).

    (* combined *)
    (*   g:  overload < load X _ _ + c*p                                                 *)
    (*   H0:            load X _ _ + c*p = load Z _ _                                    *)
    (*   H1:                               load Z _ _ <= ∑t load_sample Z _ t            *)
    (*   H2:                                             ∑t load_sample Z _ t < overload *)
    lia.

    (* justify the replacements earlier *)
    (* load1 _ _ kX = 0 *)
    unfold load1.
    simpl.
    replace (oe <=? oe) with true.
    destruct p.
    destruct (l <=? ne + 0 - 1); auto.
    replace (l <=? ne + S p - 1) with false.
    reflexivity.
    symmetry.
    apply Nat.leb_gt.
    lia.
    symmetry.
    apply Nat.leb_le.
    constructor.

    (* load1 _ _ kZ = c*p  *)
    unfold load1.
    simpl.
    replace (oe <=? oe) with true.
    replace (ne + p - 1 <=? ne + p - 1) with true.
    reflexivity.
    symmetry.
    apply Nat.leb_le.
    constructor.
    symmetry.
    apply Nat.leb_le.
    constructor.

  - pose proof (split_InBounds X Y u ss ibx) as J.
    destruct J.
    assumption.
    (* detour, deal with oe = ne first *)
      destruct (oe=?ne) eqn:W.
      clear xe xl l1 l0 l3 l2 g lcx i.
      apply Nat.eqb_eq in W.
      subst.
      assert (X=Y).
      clear ss ibx.
      induction u.
      f_equal.
      assumption.
      reflexivity.
      subst.
      assumption.
    (* ok *)
    exfalso.
    apply Nat.eqb_neq in W.

    pose proof (update_diff (load1 xe xl) X
      (l_complement X Y u)
      (u_l_complement X Y u)).
    destruct H as [common [LX LZ]].

    rewrite <- summap_mapfold in LX.
    rewrite <- summap_mapfold in LZ.
    fold (load X xe xl) in LX.
    fold (load (l_complement X Y u) xe xl) in LZ.

    replace (load1 xe xl
       {| a_est := oe; a_lct := ne + p - 1; a_c := c; a_p := p |})
    with 0 in LZ.

    replace (load1 xe xl
       {| a_est := oe; a_lct := l; a_c := c; a_p := p |})
    with 0 in LX.

    (* rewrite
        ∑X ... = ∑X\kX ... + 0
        ∑Z ... = ∑Z\kZ ... + c*p
       as
        ∑Z = ∑X + c*p
    *)
    rewrite Nat.add_0_r in LX.
    subst common.

    (* assumption lcx says that the start times will not cause overload, so *)
    (* show H: load_sample Z _ _ <= C *)
    assert (forall t : nat, load_sample (l_complement X Y u) ss t <= C).
    intro.
    rewrite <- (load_sample_equ X (l_complement X Y u) (u_l_complement X Y u)).
    apply (lcx t).


    (* show g: load X xe xl + c*(xl-nep) > overloadlevel *)
      (* was contained in the ProofStep *)

    (* show h: load X xe xl + c*(xl-nep) <= ∑t load_sample X _ t *)
    enough (load X xe xl + c * (xl-nep) <= load_sample_sum X ss xe (xl - xe)).

    (* show j: ∑t load_sample X _ t <= overload *)
    pose proof (load_sample_sum_limit C X ss lcx ibx xe (xl - xe)) as j.

    (* combined *)
    (*   g:   overload < load X xexl + c*(xl-nep)                                    *)
    (*   h:              load X xexl              <= ∑t load_sample X _ t            *)
    (*   j:                                          ∑t load_sample X _ t < overload *)
    lia.

    (* move this up *)
    assert (oe+p <= ne+p) by lia.
    assert (xl < l) by lia.
    pose proof (load_underestimates_load_sample_2
      X Y c u ss ibx xe xl (xl - nep) l0 H1).
    especialize H2.
    lia.
    apply H2.

    clear C X Y u g ibx lcx i LZ H H2 ss.

    destruct (Nat.min_spec (xl - xe) (l - p - xe)) as [[A B]|[A B]]; rewrite B.
    enough (nep >= xl - xe - min (xl - xe) (l - p - xe)).
    lia.

    admit.
    admit.



    lia.


    (* justify the replacements earlier *)
    (* load1 xe..xl oe..l = 0 *)
    unfold load1.
    simpl.
    destroy_bools_on_sight; try reflexivity.
    lia.

    (* load1 _ _ kZ = 0  *)
    clear common LX LZ.
    unfold load1.
    simpl in *.
    replace (ne + p - 1 <=? xl) with false.
    destroy_bools_on_sight; reflexivity.
    symmetry.
    apply Nat.leb_gt.
    lia.
Admitted.

Definition trn (C: nat) (X Y: AA) (P: Proof C X Y)
  (ss: list nat) (*lens*)
  (ibx: InBounds X ss)
  (lcx: forall t, load_sample X ss t <= C) :
    InBounds Y ss.
Proof.
  induction P.
  - (* p_id *) assumption.
  - (* p_step *)
    apply (tr1 C Y Z u p0).
    (*
    apply IHP.
    apply ibx.
    apply lcx.
    *)
    auto.
    clear IHP.
    intro t.
    rewrite <- (load_sample_eqp C X Y).
    auto.
    auto.
Qed.


Example example1_0 : AA :=
(cons (mkActivity 0 5 3 1)
(cons (mkActivity 2 5 1 3)
(cons (mkActivity 2 5 2 2)
(cons (mkActivity 0 9 2 3)
nil)))).

Example example1_1 : AA :=
(cons (mkActivity 0 5 3 1)
(cons (mkActivity 2 5 1 3)
(cons (mkActivity 2 5 2 2)
(cons (mkActivity 3 9 2 3) (* est increased from 0 to 3 *)
nil)))).

Example example1_2 : AA :=
(cons (mkActivity 0 5 3 1)
(cons (mkActivity 2 5 1 3)
(cons (mkActivity 2 5 2 2)
(cons (mkActivity 4 9 2 3) (* est increased from 3 to 4 *)
nil)))).

Theorem example1_step_01 : ProofStep 3 example1_0 2 3 (*est*) 0 (*->*) 3 (*lct*) 9.
Proof.
  refine (ps_tighten_est_plain 3 example1_0 2 3 0 3 9 _ _).
  compute.
  lia.
  lia.
Qed.

Theorem example1_step_12 : ProofStep 3 example1_1 2 3 3 4 9.
Proof.
  refine (ps_tighten_est_partial 3 example1_1 2 3 3 4 9 2 5 3 _ _ _ _ _ _); try lia.
  compute.
  lia.
Qed.

Theorem example1_proof: Proof 3 example1_0 example1_2.
  eapply (p_step 3 example1_0 example1_1 example1_2).
  eapply (p_step 3 example1_0 example1_0 example1_1).
  apply p_id.
  apply u1.
  apply u1.
  apply u1.
  apply u0.
  apply example1_step_01.
  apply u1.
  apply u1.
  apply u1.
  apply u0.
  apply example1_step_12.
Qed.
