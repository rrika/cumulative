Require Import Coq.Program.Equality.
Require Import Lia.

Ltac especialize H2 :=
  match goal with
  | H2 : ?a -> ?b |- _ =>
      let H := fresh in
      assert (H: a); [|specialize (H2 H); clear H]
  end.

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

Transparent load.
Transparent mapfold.

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
    xe <= xl ->
    xe <= oe ->
    xl <  oe + p ->
    oe <= ne -> (* could extract this from InBounds *)
    ne + p <= l -> (* could extract this from InBounds *)
    ne + p >= xl ->
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

Inductive VV : AA -> Type :=
| vv1 a aa :
  VV aa -> a_est a + a_p a <= a_lct a ->
  VV (cons a aa)
| vv0 : VV nil.

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

Theorem VVIB {aa: AA} {ss: list nat} :
  InBounds aa ss -> VV aa.
Proof.
  intro.
  induction H.
  apply vv1.
  assumption.
  lia.
  apply vv0.
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

Theorem InBounds_complement_imply {X Y: AA} {c p oe ne l} (B: ne+p-1 <= l) :
  forall (u: Update c p oe l ne l X Y) (ss: list nat),
    InBounds (l_complement X Y u) ss -> InBounds X ss.
Proof.
  induction u; intros.

  destruct ss; inversion H; subst.
  specialize (IHu ss H4).
  constructor; assumption.

  destruct ss; inversion H; subst; clear H; simpl in *.
  constructor; simpl in *.
  assumption.
  assumption.
  lia.
Qed.

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

Definition sws_to_selb {a s aa ss} :
  SelectWithStartTimes a s aa ss ->
  InBounds (cons a nil) (cons s nil).
Proof.
  intro sws.
  induction sws.
  assumption.
  constructor.
  constructor.
  assumption.
  assumption.
Qed.

Inductive AgreeCP : AA -> AA -> Type :=
| acp0 : AgreeCP nil nil
| acp1 a b aa bb :
    AgreeCP aa bb ->
    a_c a = a_c b ->
    a_p a = a_p b ->
    AgreeCP (cons a aa) (cons b bb).

Definition update_relate_3
  (f g: A->nat) (h: A->nat->nat)
  {X Y: AA} {ss: list nat}
  (u: InBounds X ss)
  (Hfh: forall i s,
    InBounds (cons i nil) (cons s nil) ->
    f i <= h i s)
  (CP: AgreeCP X Y)
  (Z: forall a b,
    a_c a = a_c b ->
    a_p a = a_p b ->
    forall s, h a s = h b s)
:
  summap f X <= summap (fun a_s => h (fst a_s) (snd a_s)) (combine Y ss).
Proof.
  generalize dependent ss.
  induction CP; intros.
  simpl. auto.
  destruct ss.
  inversion u.
  inversion u; subst.
  simpl.
  specialize (IHCP ss H3).
  specialize (Hfh a n).
  rewrite (Z a b) in Hfh.
  especialize Hfh.
  constructor.
  constructor.
  assumption.
  assumption.
  lia.
  assumption.
  assumption.
Qed.

Definition update_relate_2
  (f g: A->nat) (h: A->nat->nat)
  {a: A} {s: nat}
  {X: AA} {ss: list nat}
  (u: SelectWithStartTimes a s X ss)
  (Hfh: forall i s,
    InBounds (cons i nil) (cons s nil) ->
    f i <= h i s)
  (Hgh:
    InBounds (cons a nil) (cons s nil) ->
    f a + g a <= h a s)
:
  summap f X + (g a) <= summap (fun a_s => h (fst a_s) (snd a_s)) (combine X ss).
Proof.
  especialize Hgh.
  apply (sws_to_selb u).
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

(* want to use this on 'a' past split into the overloaded branch    *)
(* so its a_lct is different, BX needs to be different too for this *)
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

Theorem load1_sample_sum_right_truncated_no_min a s
  (BX : InBounds (a :: nil) (s :: nil))
  (t m: nat)
:
  t     <= a_est a ->
  t + m <= a_lct a ->
  a_c a * (m-(a_lct a - a_p a - t)) <= load1_sample_sum a s t m.
Proof.
  intros.
  replace (m-(a_lct a - a_p a - t)) with
          (m-(min m (a_lct a - a_p a - t))).
  apply load1_sample_sum_right_truncated; assumption.
  lia.
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
  {X Y c p oe ol ne nl} {ss} (I: InBounds X ss) (u: Update c p oe ol ne nl X Y)
:
  { s:nat & SelectWithStartTimes (mkActivity oe ol c p) s X ss }
.
Proof.
  generalize dependent ss.
  induction u.
  - intros.
    specialize (SelectWithStartTimes_from_Update_X
      xs ys c p oe ol ne nl).
    intros.
    inversion I.
    subst.
    specialize (SelectWithStartTimes_from_Update_X ss0 H1 u).
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

Fixpoint SelectWithStartTimes_from_Update_Z
  {X Y c p oe ol ne nl} {ss} (u: Update c p oe ol ne nl X Y)
:
  forall (I: InBounds (l_complement X Y u) ss),
  { s:nat & SelectWithStartTimes (mkActivity oe (ne+p-1) c p) s (l_complement X Y u) ss }
.
Proof.
  generalize dependent ss.
  induction u.
  - specialize (SelectWithStartTimes_from_Update_Z
      xs ys c p oe ol ne nl).
    intros.
    inversion I.
    subst.
    specialize (SelectWithStartTimes_from_Update_Z ss0 u H1).
    destruct SelectWithStartTimes_from_Update_Z.
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

Theorem load_underestimates_load_sample_2_impl
  a s {aa ss} (sws : SelectWithStartTimes a s aa ss) est lct rrr
:
  (* a is from the Z branch *)
  (* xe <= e  <= l  *)
  (* xe <= xl <  l  *)
  (*       xl < e+p *)
  est <= lct ->
  est <= (a_est a) ->
  lct <  (a_lct a) ->
  (a_est a) + (a_p a) > lct ->
  rrr <= ((lct - est)-(min (lct-est) ((a_lct a)-(a_p a)-est))) ->
  (a_c a) * rrr <= load1_sample_sum a s est (lct - est).
Proof.
  intros.
  induction sws.
  apply IHsws.
  assumption.
  assumption.
  assumption.
  assumption.

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

Qed.

Theorem map_load1_zero_zero
  {X Q}
  (vv: VV X)
  {est lct: nat}
  (R : lct < est)
:
  summap (load1 est lct) X <= summap (fun _ : A * nat => 0) Q.
Proof.
  replace (summap (load1 est lct) X) with 0.
  replace (summap (fun _ : A * nat => 0) Q) with 0.
  auto.

  induction Q.
  auto.
  apply IHQ.

  induction X; intros.
  auto.
  inversion vv; subst.
  simpl.
  rewrite <- (IHX H1); clear IHX H1.
  rewrite Nat.add_0_r.
  unfold load1.
  destroy_bools_on_sight.
  exfalso.
  lia.
  reflexivity.
  reflexivity.
Qed.

(* if load_underestimates_load_sample was so good, why didn't they make *)
Theorem load_underestimates_load_sample_2
  X Y c {p oe ne l} (u: Update c p oe l ne l X Y) ss
  (BX : InBounds X ss)
  (BZ : InBounds (l_complement X Y u) ss)
  (est lct rrr: nat)
:
  est <= oe ->
  lct < l ->
  lct < ne + p - 1 ->
  oe + p > lct ->
  (*rrr <= ((lct - est)-(min (lct-est) (l-p-est))) ->*)
  rrr <= lct - est - min (lct - est) (ne + p - 1 - p - est) ->
  load (l_complement X Y u) est lct + c * rrr <= load_sample_sum (l_complement X Y u) ss est (lct - est).
Proof.
  intros U V T W F.
  rewrite (transpose BZ); try assumption.
  unfold load.
  rewrite summap_mapfold.

  pose proof (VVIB BX) as VVX.
  pose proof (VVIB BZ) as VVZ.

  pose proof (SelectWithStartTimes_from_Update_Z u BZ).
  destruct H.

  destruct (lct <? est) eqn:R.
  - relb_to_rel.
    assert (lct-est = 0) by lia.
    clear s.
    rewrite H.
    rewrite H in F; simpl in F; inversion F; clear F.
    simpl.
    rewrite Nat.mul_0_r.
    rewrite Nat.add_0_r.
    apply map_load1_zero_zero.
    assumption.
    assumption.

  - relb_to_rel.
  remember ({| a_est := oe; a_lct := ne+p-1; a_c := c; a_p := p |}) as a.
  eapply (@update_relate_2

    (* relate lower bound consisting of *)
    (* - f: other tasks:  the usual approximation (load1)    *)
    (* - g: current task: the slighter better approximation  *)
    (* and the exact load *)
    (* - h: based on concrete start times (load1_sample_sum) *)

    (*f*) (load1 est lct)
    (*g*) (fun a => _)
    (*h*) (fun x s => load1_sample_sum x s est (lct - est))
    a x (l_complement X Y u) ss s
  ).
  intros.
  apply load1_underestimates_load1_sample_sum.
  assumption.

  intro Q.
  replace c with (a_c a). all: swap 1 2. subst; auto.
  replace (load1 _ _ _) with 0; simpl.

  (* ... + [...] <= ... *)
  apply (load_underestimates_load_sample_2_impl a x s); subst; subst; simpl; auto.

  unfold load1.
  destruct (est <=? a_est a) eqn:J.
  destruct (a_lct a <=? lct) eqn:K. 
  repeat relb_to_rel.
  exfalso.
  replace (a_lct a) with (ne+p-1) in *.

  lia.
  subst.
  reflexivity.
  reflexivity.
  reflexivity.
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

(* by having tr1 return another InBounds object with an obligation to
   show that none of the Y have narrowed to an impossible range (less
   time than the task itself takes), it's hard for tr1 to show that
   reducing to 0 solutions is valid when its on a dead end of the
   search.
   side-stepping this by requiring the user to put these inequalities
   in the proofstep object, but it doesn't belong there.
*)
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
      clear xe xl l1 l0 l3 l2 g g0 lcx i.
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

    *

    (* rewrite
        ∑X ... = ∑X\kX ... + 0
        ∑Z ... = ∑Z\kZ ... + c*???
       as
        ∑Z = ∑X + c*???
    *)
    rewrite Nat.add_0_r in LX.
    rewrite Nat.add_0_r in LZ.
    subst common.

    (* assumption lcx says that the start times will not cause overload, so *)
    (* show H: load_sample Z _ _ <= C *)
    assert (forall t : nat, load_sample (l_complement X Y u) ss t <= C).
    intro.
    rewrite <- (load_sample_equ X (l_complement X Y u) (u_l_complement X Y u)).
    apply (lcx t).


    (* show g: load X xe xl + c*(xl-nep) > overloadlevel *)
      (* was contained in the ProofStep *)

    (* show h: load Z xe xl + c*(xl-nep) <= ∑t load_sample X _ t *)
    enough (load (l_complement X Y u)  xe xl + c * (xl-nep) <= load_sample_sum (l_complement X Y u) ss xe (xl - xe)) as h.

    (* show j: ∑t load_sample Z _ t <= overload *)
    pose proof (load_sample_sum_limit C (l_complement X Y u) ss H i xe (xl - xe)) as j.

    (* combined *)
    (*   g:   overload < load X xexl + c*(xl-nep)                                    *)
    (*   LZ:      load X xexl = load Z xexl                                          *)
    (*   h:              load Z xexl + c*(xl-nep) <= ∑t load_sample Z _ t            *)
    (*   j:                                          ∑t load_sample Z _ t < overload *)
    lia.

    (* move this up (h) *)
    assert (oe+p <= ne+p) by lia.
    assert (xl < l) by lia.
    pose proof (load_underestimates_load_sample_2
      X Y c u ss ibx i xe xl (xl - nep) l1 H1).
    especialize H2.
    lia.
    apply H2.
    lia.

    clear C X Y u g0 ibx lcx i LZ H H2 ss.
    replace (ne+p-1-p-xe) with (ne-1-xe) by lia.
    enough (ne > xe+min (xl-xe) (ne-1-xe)).
    clear l0 l1 l2 l3 l4 g W H0 H1.
    lia.
    replace (xe + min (xl - xe) (ne - 1 - xe))
       with (min xl (ne-1)) by lia.
    lia.

    (* justify the replacements earlier *)
    (* load1 xe..xl oe..l = 0 *)
    * unfold load1.
      simpl.
      destroy_bools_on_sight; try reflexivity.
      lia.

    (* load1 _ _ kZ = 0  *)
    * clear common LX LZ.
      unfold load1.
      simpl in *.
      replace (ne + p - 1 <=? xl) with false.
      destroy_bools_on_sight; try reflexivity.
      symmetry.
      apply Nat.leb_gt.
      lia.
Qed.

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
  refine (ps_tighten_est_partial 3 example1_1 2 3 3 4 9 2 5 3 _ _ _ _ _ _ _ _); try lia.
  compute.
  lia.
Qed.

Theorem example1_proof : Proof 3 example1_0 example1_2.
Proof.
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

(* ---------------- proofs above, algorithms below ---------------- *)

(* phase 1: find overloaded regions to produce ps_tighten_est_plain *)
(* phase 2: find overloaded regions to produce ps_tighten_est_partial *)

(* phase 1:

    go over tasks by decreasing latest completion time (lct)

             [  ####       ] T
                     [##  ]
          [    ####     ]
               [ #### ]

    for each, scan between its est and lct for a subrange U
             [                ] T
             `--->[      ]<---´ U
             ^^^^^^^^^^^^^
           est[T]      lct[U]

    whose fully included tasks U ∪ {T} would overload the range est[T] .. lct[U].

    The proper algorithm uses a binary tree for finding lct[U],
    but I want to build proof generically, so I can for a start
    use a linear search.

    So all the tasks are unvisited at first.

      UUUUUUUU

    Then from the back, they are visited.

      UUUUUUUV
      UUUUUUVV
      UUUUUVVV

    And whenever one finds a subrange they overload, they're eliminated

      UUUUUV V
      UUUUUV  
      UUUUU   

    Progression: Unvisited -> Visited -> Removed
*)
Print nil.

Require Import Coq.Sorting.Mergesort.
Require Import Orders.

Module TaskReverseLctOrder <: TotalLeBool.
  Definition t := Activity.
  Definition leb a b := (a_lct b) <=? (a_lct a).
  Theorem leb_total : forall a1 a2, (leb a1 a2) = true \/ (leb a2 a1) = true.
    intros.
    unfold leb.
    apply Coq.Sorting.Mergesort.NatOrder.leb_total.
  Qed.
End TaskReverseLctOrder.

Module TaskReverseLctSort := Mergesort.Sort TaskReverseLctOrder.

Definition olift (f: nat->nat->nat) (a b: option nat) := match (a, b) with
| (None, None) => None
| (Some a, None) => Some a
| (None, Some b) => Some b
| (Some a, Some b) => Some (f a b)
end.
Definition omin := olift min.
Definition omax := olift max.
Transparent olift.
Transparent omin.
Transparent omax.

Definition olt (a b: option nat) := match (a, b) with
| (Some a, Some b) => a < b
| _ => True
end.

Structure Env := envp { vcest: nat; vnrg: nat }.
Definition evalEnvelope (e: Env) : nat :=
  match e with envp a b => a+b end.
Coercion evalEnvelope : Env >-> nat.
Definition addToEnvelope (E: Env) (e: nat) :=
  envp (vcest E) (vnrg E + e).

Declare Scope env_scope.
Delimit Scope env_scope with e.
Notation "a + b" := (addToEnvelope a b) : env_scope.

Definition maxEnvelope (x y: Env) : Env :=
  if x <? y then y else x.

Definition maxEnvelope3 (x y z: Env) : Env :=
  maxEnvelope (maxEnvelope x y) z.

Record ThetaLambdaInner := mkTLInner {
  tl_teest      : option nat; (* earliest start of a theta task *)
  tl_tllct      : option nat; (* latest completion of a theta task *)
  tl_lelct      : option nat; (* earliest latest completion of a lambda task *)

  tl_energy    : nat; (* theta tasks only *)
  tl_envelope  : Env; (* theta tasks only *)
  tl_energyΛ   : nat; (* lambda tasks only *)
  tl_envelopeΛ : Env; (* theta tasks + a single lambda task *)
}.

Definition theta_lambda_leaf_theta (C: nat) (a: Activity) : ThetaLambdaInner :=
  let est := (a_est a) in
  let lct := (a_lct a) in
  let e := (a_c a * a_p a) in
  mkTLInner
    (* tl_teest     = *) (Some est)
    (* tl_tllct     = *) (Some lct)
    (* tl_lelct     = *) None
    (* tl_energy    = *) e
    (* tl_envelope  = *) (envp (C*est) e)
    (* tl_energyΛ   = *) 0
    (* tl_envelopeΛ = *) (envp 0 0).

Definition theta_lambda_leaf_lambda (C: nat) (a: Activity) : ThetaLambdaInner :=
  let est := (a_est a) in
  let lct := (a_lct a) in
  let e := (a_c a * a_p a) in
  mkTLInner
    (* tl_teest     = *) None
    (* tl_tllct     = *) None
    (* tl_lelct     = *) (Some lct)
    (* tl_energy    = *) 0
    (* tl_envelope  = *) (envp 0 0)
    (* tl_energyΛ   = *) e
    (* tl_envelopeΛ = *) (envp (C*est) e).

Definition theta_lambda_combine (l: ThetaLambdaInner) (r: ThetaLambdaInner) :=
  mkTLInner
    (* tl_teest     = *) (omin (tl_teest l) (tl_teest r))
    (* tl_tllct     = *) (omax (tl_tllct l) (tl_tllct r))
    (* tl_lelct     = *) (omin (tl_lelct l) (tl_lelct r))
    (* tl_energy    = *) ((tl_energy l) + (tl_energy r))
    (* tl_envelope  = *) (maxEnvelope (tl_envelope l) (tl_envelope r))
    (* tl_energyΛ   = *) ((tl_energyΛ l) + (tl_energyΛ r))
    (* tl_envelopeΛ = *) (maxEnvelope3
      ((tl_envelopeΛ l) + (tl_energy  r))
      ((tl_envelope  r) + (tl_energyΛ r))
      (tl_envelopeΛ r)
    )%e.

Inductive ThetaLambdaTree (C: nat) : ThetaLambdaInner -> Type :=
| tlt_theta (i: nat) (a: Activity) :
    ThetaLambdaTree C (theta_lambda_leaf_theta C a)
| tlt_lambda (i: nat) (a: Activity) :
    ThetaLambdaTree C (theta_lambda_leaf_lambda C a)
| tlt_node {li ri}
    (lhs: ThetaLambdaTree C li)
    (rhs: ThetaLambdaTree C ri) :
    ThetaLambdaTree C (theta_lambda_combine li ri).

Fixpoint tl_load_either {C n} (est lct: nat) (x: ThetaLambdaTree C n) :=
match x with
| tlt_theta  _ i a => load1 est lct a
| tlt_lambda _ i a => load1 est lct a
| tlt_node _ lhs rhs => (tl_load_either est lct lhs) + (tl_load_either est lct rhs)
end.

Fixpoint tl_load_theta {C n} (est lct: nat) (x: ThetaLambdaTree C n) :=
match x with
| tlt_theta  _ i a => load1 est lct a
| tlt_lambda _ i a => 0
| tlt_node _ lhs rhs => (tl_load_theta est lct lhs) + (tl_load_theta est lct rhs)
end.

Fixpoint tl_load_lambda {C n} (est lct: nat) (x: ThetaLambdaTree C n) :=
match x with
| tlt_theta  _ i a => 0
| tlt_lambda _ i a => load1 est lct a
| tlt_node _ lhs rhs => (tl_load_lambda est lct lhs) + (tl_load_lambda est lct rhs)
end.

Theorem tl_load_theta_eq {C n} (est lct: nat) (x: ThetaLambdaTree C n) :
  match tl_lelct n with
  | None => tl_load_theta est lct x = tl_load_either est lct x
  | _ => True
  end.
Proof.
  induction x; simpl.
  reflexivity.
  apply I.
  destruct (tl_lelct li); destruct (tl_lelct ri); simpl; try apply I.
  rewrite IHx1.
  rewrite IHx2.
  reflexivity.
Qed.

Theorem tl_load_lambda_eq {C n} (est lct: nat) (x: ThetaLambdaTree C n) :
  match tl_tllct n with
  | None => tl_load_lambda est lct x = tl_load_either est lct x
  | _ => True
  end.
Proof.
  induction x; simpl.
  apply I.
  reflexivity.
  destruct (tl_tllct li); destruct (tl_tllct ri); simpl; try apply I.
  rewrite IHx1.
  rewrite IHx2.
  reflexivity.
Qed.

Fixpoint tl_flip_max_lct {C n} (x: ThetaLambdaTree C n) :
  option {n : ThetaLambdaInner & ThetaLambdaTree C n } :=
match x with
| tlt_theta _ i a  => Some (existT _ _ (tlt_lambda C i a))
| tlt_lambda _ i a => None
| @tlt_node _ nl nr lhs rhs =>
  let xl :=
    match tl_flip_max_lct lhs with
    | Some (existT _ _ lhs2) => Some (existT _ _ (tlt_node C lhs2 rhs))
    | None => None
    end in
  let xr :=
    match tl_flip_max_lct rhs with
    | Some (existT _ _ rhs2) => Some (existT _ _ (tlt_node C lhs rhs2))
    | None => None
    end in
  match (tl_tllct nl, tl_tllct nr) with
  | (None,       None)       => None
  | (Some lllct, None)       => xl
  | (None,       Some rllct) => xr
  | (Some lllct, Some rllct) =>
    if rllct <? lllct then xl else xr
  end
end.

Fixpoint tl_pop_max_env {C n} (x: ThetaLambdaTree C n) :
  option (nat * A * option {n : ThetaLambdaInner & ThetaLambdaTree C n }) :=
match x with
| tlt_theta _ i a  => None
| tlt_lambda _ i a => Some (i, a, None)
| @tlt_node _ nl nr lhs rhs =>
  match (if (tl_envelopeΛ nr <? tl_envelopeΛ nl) then
    match tl_pop_max_env lhs with
    | None           => (None,        None, Some (existT _ _ rhs))
    | Some (i, a, k) => (Some (i, a), k,    Some (existT _ _ rhs))
    end
  else
    match tl_pop_max_env lhs with
    | None           => (None,        Some (existT _ _ lhs), None)
    | Some (i, a, k) => (Some (i, a), Some (existT _ _ lhs), k)
    end)
  with
  | (None,        _,             _            ) => None
  | (Some (i, a), None,          z            ) => Some (i, a, z)
  | (Some (i, a), y,             None         ) => Some (i, a, y)
  | (Some (i, a), Some y,        Some z       ) => Some (i, a, Some (
    existT _ _ (tlt_node C
      (projT2 y)
      (projT2 z)
    )))
  end
end.

Inductive Interleave {A} (*DropOk: A -> Prop*) : list A -> list A -> list A -> Type :=
| s_nil           : Interleave (*DropOk*) nil nil nil
| s_left  a x y z : Interleave (*DropOk*) x y z -> Interleave (*DropOk*) (a::x) y (a::z)
| s_right a x y z : Interleave (*DropOk*) x y z -> Interleave (*DropOk*) x (a::y) (a::z).
(* | s_drop  a x y z : Interleave (*DropOk*) x y z -> (*DropOk a ->*) Interleave (*DropOk*) x y (a::z). *)

Definition tl_llct_prop (tl: ThetaLambdaInner) (a:A) :=
  match (tl_tllct tl) with Some llct => a_lct a <= llct | _ => True end.

Inductive Sublist {A} : list A -> list A -> Type :=
| sl_nil        : Sublist nil nil
| sl_skip a b c : Sublist b c -> Sublist b (a::c)
| sl_cons a b c : Sublist b c -> Sublist (a::b) (a::c).

Inductive TLT2 {C} : AA -> forall {n}, ThetaLambdaTree C n -> Type :=
| tlt2_theta  i a : TLT2 (cons a nil) (tlt_theta  C i a)
| tlt2_lambda i a : TLT2 (cons a nil) (tlt_lambda C i a)
| tlt2_node {la ra a li ri}
  {lhs: ThetaLambdaTree C li}
  {rhs: ThetaLambdaTree C ri} :
  TLT2 la lhs ->
  TLT2 ra rhs ->
  Interleave (*tl_llct_prop (theta_lambda_combine li ri)*) la ra a ->
  olt (tl_tllct (theta_lambda_combine li ri)) (tl_lelct (theta_lambda_combine li ri)) ->
  TLT2 a (tlt_node C lhs rhs).

Theorem TLT2_tllct_lt_lelct {C aa n t} (tl2: @TLT2 C aa n t) :
  olt (tl_tllct n) (tl_lelct n).
Proof.
  destruct tl2.
  compute; apply I.
  compute; apply I.
  apply o.
Qed.

Theorem TLT2_nil {C n t} : @TLT2 C nil n t -> False.
Proof.
  intro.
  dependent induction H.
  inversion i.
  subst.
  apply IHTLT2_1.
  auto.
Qed.

Inductive InterleavePrefix (*D*) (x: AA) (y: AA) (zp: AA) :=
  mkIP (xs:AA) (xp:AA) (ys:AA) (yp:AA) :
    x = xs++xp -> y = ys++yp ->
      Interleave (*D*) xp yp zp ->
        InterleavePrefix (*D*) x y zp.

Definition interleave_drop_one (*{D}*) (x y: AA) (zs1: A) (zp: AA)
    (I: Interleave (*D*) x y (zs1::zp)) :
  InterleavePrefix (*D*) x y zp.
Proof.
  dependent induction I.
  - apply mkIP with (xs:=(zs1::nil)) (xp:=x) (ys:=nil) (yp:=y); auto.
  - apply mkIP with (xs:=nil) (xp:=x) (ys:=(zs1::nil)) (yp:=y); auto.
Qed.

Theorem InterleavePrefix_nil x y : InterleavePrefix x y nil.
Proof.
  apply (mkIP (*D*) _ _ nil x nil y nil).
  rewrite List.app_nil_r. auto.
  rewrite List.app_nil_r. auto.
  constructor.
Qed.

Definition interleave_prefix (*{D}*) (x y zs zp: AA) (I: Interleave (*D*) x y (zs++zp)) :
  InterleavePrefix (*D*) x y zp.
Proof.
  remember (zs++zp) as z.
  destruct zp as [|zm zp].
  apply InterleavePrefix_nil.
  generalize dependent zp.
  generalize dependent zm.
  generalize dependent zs.
  induction I; intros.
  - exfalso.
    apply (app_cons_not_nil _ _ _ Heqz).
  - destruct zs eqn:W.

    simpl in Heqz.
    clear IHI.
    rewrite <- Heqz.
    apply (mkIP (*D*) _ _ _ nil (a::x) nil y); auto.
    apply s_left.
    assumption.

    specialize (IHI a1 zm zp).
    simpl in Heqz.
    inversion Heqz.
    specialize (IHI H1).
    clear Heqz H0 H1.
    destruct IHI.
    apply (mkIP (*D*) _ _ _ (a0::xs) xp ys yp).
    simpl.
    subst.
    reflexivity.
    assumption.
    assumption.

  - destruct zs eqn:W.

    simpl in Heqz.
    clear IHI.
    rewrite <- Heqz.
    apply (mkIP (*D*) _ _ _ nil x nil (a::y)); auto.
    apply s_right.
    assumption.

    specialize (IHI a1 zm zp).
    simpl in Heqz.
    inversion Heqz.
    specialize (IHI H1).
    clear Heqz H0 H1.
    destruct IHI.
    apply (mkIP (*D*) _ _ _ xs xp (a0::ys) yp).
    simpl.
    subst.
    reflexivity.
    simpl.
    subst.
    reflexivity.
    assumption.
Qed.

(*Theorem tlt2_aa_sync {C a b c d}
  {e: TLT2 a c}
  {f: TLT2 b d}
  {g h}
  (I: TLT2 g (tlt_node C c d))
  (J: I = tlt2_node e f h) : g = h.*)

Theorem bleh {A} (a:A) b c d : (a::nil) = b++(c::d) -> a=c /\ b=nil /\ d=nil.
Proof.
  intro.
  destruct b; simpl.
  inversion H.
  auto.
  inversion H.
  destruct b; simpl.
  inversion H2.
  simpl in H2.
  inversion H2.
Qed.

Theorem interleave_right {A a b} : @Interleave A nil a b -> a=b.
Proof.
  intro.
  dependent induction a.
  inversion X.
  reflexivity.
  destruct b.
  inversion X.
  inversion X.
  subst.
  f_equal.
  apply IHa.
  apply X0.
Qed.

Theorem interleave_left {A a b} : @Interleave A a nil b -> a=b.
Proof.
  intro.
  dependent induction a.
  inversion X.
  reflexivity.
  destruct b.
  inversion X.
  inversion X.
  subst.
  f_equal.
  apply IHa.
  apply X0.
Qed.

(*Definition tlt2_interleave_prefix {C} (aa_rest aa_prefix: AA)
  {tli: ThetaLambdaInner} (tl: ThetaLambdaTree C tli) :
  TLT2 (aa_rest ++ aa_prefix) tl -> (aa_prefix <> nil) ->
  {tli: ThetaLambdaInner & {n: ThetaLambdaTree C tli & TLT2 aa_prefix n } }.
Proof.
  intro.
  remember (aa_rest ++ aa_prefix) as aa.
  generalize dependent aa_prefix.
  generalize dependent aa_rest.
  induction H eqn:W; intros.

  eexists _.
  exists (tlt_theta C i a).
  destruct aa_prefix eqn:X.
  exfalso.
  apply (H0 eq_refl).

  inversion Heqaa.
  destruct (bleh a aa_rest a0 a1 H2) as [aa0 [aa_rest_nil a1_nil]].
  subst aa_rest.
  subst a1.
  subst a0.
  assumption.

  eexists _.
  exists (tlt_lambda C i a).
  destruct aa_prefix eqn:X.
  exfalso.
  apply (H0 eq_refl).

  inversion Heqaa.
  destruct (bleh a aa_rest a0 a1 H2) as [aa0 [aa_rest_nil a1_nil]].
  subst aa_rest.
  subst a1.
  subst a0.
  assumption.

  specialize (IHt1 t1 eq_refl).
  specialize (IHt2 t2 eq_refl).
  pose proof (interleave_prefix la ra aa_rest aa_prefix) as Z.
  destruct Z.
  rewrite <- Heqaa.
  apply i.
  specialize (IHt1 xs xp e).
  specialize (IHt2 ys yp e0).

  destruct xp.
  destruct yp.

  (* impossible case *)
  exfalso.
  generalize H0 i0.
  clear; intros.
  inversion i0.
  symmetry in H2.
  apply (H0 H2).

  (* lhs empty *)
  clear IHt1.
  especialize IHt2.
  intro.
  inversion H1.
  destruct IHt2 as [nr [nrtl1 nrtl2]].
  exists nr.
  exists nrtl1.
  replace (aa_prefix) with (a0::yp).
  assumption.
  rewrite (interleave_right i0).
  reflexivity.

  destruct yp.
  (* rhs empty *)
  clear IHt2.
  especialize IHt1.
  intro.
  inversion H1.
  destruct IHt1 as [nl [nltl1 nltl2]].
  exists nl.
  exists nltl1.
  replace (aa_prefix) with (a0::xp).
  assumption.
  rewrite (interleave_left i0).
  reflexivity.

  (* both children *)
  especialize IHt1.
  intro.
  inversion H1.
  especialize IHt2.
  intro.
  inversion H1.
  generalize dependent H0.
  destruct IHt1 as [nl [nltl1 nltl2]].
  destruct IHt2 as [nr [nrtl1 nrtl2]].
  exists (theta_lambda_combine nl nr).
  exists (tlt_node C nltl1 nrtl1).
  apply (tlt2_node nltl2 nrtl2).
  apply i0.
Qed.*)


(*Definition tlt2_interleave_prefix {C} (aa_rest aa_prefix: AA)
  {tli: ThetaLambdaInner} (tl: ThetaLambdaTree C tli) :
  TLT2 (aa_rest ++ aa_prefix) tl -> (aa_prefix <> nil) ->
  {tli: ThetaLambdaInner & {n: ThetaLambdaTree C tli & TLT2 aa_prefix n } }. *)

Theorem interleave_load {la ra a} (i : Interleave la ra a) (est lct: nat) :
  (load la est lct) + (load ra est lct) = load a est lct.
Proof.
  induction i; simpl.
  auto.
  unfold load in *.
  unfold mapfold in *.
  simpl.
  rewrite <- IHi. clear IHi.
  lia.
  unfold load in *.
  unfold mapfold in *.
  simpl.
  rewrite <- IHi. clear IHi.
  lia.
Qed.

Theorem load_nil {est lct} : load nil est lct = 0.
Proof.
  unfold load.
  unfold mapfold.
  reflexivity.
Qed.

Theorem tl2_load_eq {C n aa} {x: ThetaLambdaTree C n}
  (est lct: nat)
  (t2: TLT2 aa x) :
  tl_load_either est lct x = load aa est lct. 
Proof.
  induction t2.
  - unfold load.
    unfold mapfold.
    simpl.
    rewrite Nat.add_0_r.
    reflexivity.
  - unfold load.
    unfold mapfold.
    simpl.
    rewrite Nat.add_0_r.
    reflexivity.
  - rewrite <- (interleave_load i).
    simpl.
    rewrite IHt2_1.
    rewrite IHt2_2.
      reflexivity.
Qed.

Require Import String.

Theorem interleave_forall {A} {X Y Z: list A} (i: Interleave X Y Z) {P} :
  Forall P X -> Forall P Y -> Forall P Z.
Proof.
  intros.
  induction i.
  auto.
  inversion H; subst.
  auto.
  inversion H0; subst.
  auto.
Qed.

Theorem bump_forall_lct {L} (n m: nat) : n <= m ->
  Forall (fun a : Activity => a_lct a <= n) L ->
  Forall (fun a : Activity => a_lct a <= m) L.
Proof.
  intros.
  induction L.
  auto.
  inversion H0; subst.
  constructor.
  clear -H H3.
  lia.
  apply IHL.
  assumption.
Qed.

Theorem bump_load_forall_lct {X} (est n m: nat) : n <= m ->
  Forall (fun a : Activity => a_lct a <= n) X ->
  load X est n = load X est m.
Proof.
  intros.
  induction X; simpl in *.
  auto.
  inversion H0; subst.
  clear H0.
  especialize IHX.
  assumption.
  unfold load in *.
  unfold mapfold in *.
  simpl.
  replace (load1 est n a) with (load1 est m a).
  rewrite IHX.
  reflexivity.
  clear IHX H4.
  unfold load1.
  destroy_bools_on_sight; try reflexivity.
  lia.
  lia.
Qed.


(*
Theorem tl_tllct_ok {X C n} {x: ThetaLambdaTree C n} (t2: TLT2 X x) :
  match (tl_tllct n) with
  | Some llct => Forall (fun a=>a_lct a <= llct) X 
  | _ => True
  end.
Proof.
  remember x as x'.
  induction t2.
  - constructor.
    auto.
    constructor.
  - simpl; auto.
  - simpl.
    specialize (IHt2_1 lhs eq_refl).
    specialize (IHt2_2 rhs eq_refl).
    destruct (tl_tllct li).
    destruct (tl_tllct ri).
    simpl.
    apply (interleave_forall i).
    apply (bump_forall_lct n (max n n0)).
    lia.
    assumption.
    apply (bump_forall_lct n0 (max n n0)).
    lia.
    assumption.
    simpl.
*)

Theorem tl_load_theta_eq_tree {X C n} {x: ThetaLambdaTree C n} (t2: TLT2 X x)
  (est lct: nat) :
  (exists lelct,
    tl_lelct n = Some lelct  /\
    lct < lelct) \/ tl_lelct n = None ->
  tl_load_either est lct x = tl_load_theta est lct x.
Proof.
  induction t2; intros.
  auto.
  simpl in *.
  unfold load1.
  destruct H as [[lelct [H H0]]|H]; [|inversion H].
  inversion H.
  rewrite H2.
  destroy_bools_on_sight.
  lia.
  reflexivity.
  reflexivity.

  simpl in *.
  destruct H as [[lelct [H H1]]|H].
  destruct (tl_lelct li) as [lelct_li|];
  destruct (tl_lelct ri) as [lelct_ri|];
  inversion H; 
  (rewrite IHt2_1; [rewrite IHt2_2; [reflexivity|]|]);
  clear - H1 H2;
  [left|left|right|left|left|right]; try reflexivity;
  [exists lelct_ri|exists lelct_li|exists lelct_li|exists lelct_ri];
  (constructor; [reflexivity|]); lia.


  pose proof (tl_load_theta_eq est lct lhs) as EL.
  pose proof (tl_load_theta_eq est lct rhs) as ER.
  destruct (tl_lelct li) as [lelct_li|];
  destruct (tl_lelct ri) as [lelct_ri|];
  inversion H.
  rewrite EL.
  rewrite ER.
  reflexivity.
Qed.

Theorem tl_load_theta_bump
  (C : nat)
  (n : ThetaLambdaInner)
  (x : ThetaLambdaTree C n)
  (est lct1 lct2 : nat) :
  (exists tllct,
    Some tllct = tl_tllct n /\
    tllct <= lct1 /\
    tllct <= lct2) \/ None = tl_tllct n ->
  tl_load_theta est lct1 x = tl_load_theta est lct2 x.
Proof.
  intros.
  generalize dependent H.
  induction x; intros.

  destruct H as [[tllct [H [H1 H2]]]|].
  simpl in *.
  unfold load1.
  destruct (est <=? a_est a); [|reflexivity].
  inversion H; subst; clear H.
  destroy_bools_on_sight.
  reflexivity.
  lia.
  lia.
  reflexivity.
  inversion H.

  destruct H as [[tllct [H [H1 H2]]]|].
  reflexivity.
  reflexivity.

  destruct H as [[tllct [H [H1 H2]]]|].
  simpl in *.
  destruct (tl_tllct li) as [tllct_li|];
  destruct (tl_tllct ri) as [tllct_ri|];
  inversion H; clear H;
  (rewrite <- IHx1; [rewrite <- IHx2; [reflexivity|]|]);
  [left|left|right|left|left|right]; try reflexivity;
  [exists tllct_ri|exists tllct_li|exists tllct_li|exists tllct_ri];
  (constructor; try reflexivity); lia.

  simpl in *.
  destruct (tl_tllct li) as [tllct_li|];
  destruct (tl_tllct ri) as [tllct_ri|];
  inversion H; clear H.
  rewrite <- IHx1; [rewrite <- IHx2|]; [|right|right]; reflexivity.
Qed.


Theorem tl_theta_load_wiggle {X C n} {x: ThetaLambdaTree C n} (t2: TLT2 X x)
  (est: nat) :
  forall (lct: nat),
  forall tllct, tl_tllct n = Some tllct -> tllct <= lct ->
    match tl_lelct n with
    | Some lelct => lct < lelct
    | None => True
    end -> load X est lct = load X est tllct.

Proof.
  intros.
  rewrite <- (tl2_load_eq _ _ t2).
  rewrite <- (tl2_load_eq _ _ t2).

  pose proof (tl_load_theta_eq_tree t2 est lct).
  rewrite H2; clear H2.
  pose proof (TLT2_tllct_lt_lelct t2).
  rewrite H in H2.
  unfold olt in H2.
  pose proof (tl_load_theta_eq_tree t2 est tllct).
  rewrite H3; clear H3.
  apply tl_load_theta_bump.
  left.
  exists tllct.
  auto.
  destruct (tl_lelct n) as [lelct|]; [left|right;reflexivity].
  exists lelct.
  auto.

  destruct (tl_lelct n) as [lelct|]; [left|right;reflexivity].
  exists lelct.
  auto.
Qed.
(*
Theorem tl_pop_max_env_load {X C n} {x: ThetaLambdaTree C n} (t2: TLT2 X x) :
  match (tl_tllct n) with
  | Some llct =>
    match (tl_pop_max_env x) with
    | Some (i, a, Some y) =>
      match tl_envelopeΛ n with envp vcest vnrg =>
        let c  := a_c a in 
        let p  := a_p a in 
        tl_load_either vcest llct x + c*p = vnrg
      end
    | _ => True
    end
  | None => True
  end.
Proof.
  set (x_ := x).
  dependent induction t2.
  simpl; auto.
  simpl; auto.
  rename a into lra.
  destruct (tl_tllct (theta_lambda_combine li ri)) as [tllct|] eqn:H1; try apply I.
  destruct (tl_pop_max_env x_) as [[[a b] [c|]]|] eqn:H2; try apply I.
  simpl.
  remember (maxEnvelope3 (tl_envelopeΛ li + tl_energy ri)%e
    (tl_envelope ri + tl_energyΛ ri)%e (tl_envelopeΛ ri)) as kenv.
  enough (
    kenv = (tl_envelopeΛ li + tl_energy ri)%e \/
    kenv = (tl_envelope ri + tl_energyΛ ri)%e \/
    kenv = (tl_envelopeΛ ri)).
  destruct H as [HenvΛ|[HenvΛ|HenvΛ]];
  clear Heqkenv;
  subst kenv;
  simpl.
  
  destruct (tl_tllct li) as [llct_li|] eqn:LCTL; [|
    set (info1 := "no elements left in lhs" % string); move info1 at top].
  destruct (tl_tllct ri) as [llct_ri|] eqn:LCTR; [|
    set (info2 := "no elements left in rhs" % string); move info2 at top].
*)
Theorem tl_pop_max_env_load {X C n} {x: ThetaLambdaTree C n} (t2: TLT2 X x) :
  match (tl_tllct n) with
  | Some llct =>
    match (tl_pop_max_env x) with
    | Some (i, a, Some y) =>
      match tl_envelopeΛ n with envp vcest vnrg =>
        let c  := a_c a in 
        let p  := a_p a in 
        load X vcest llct + c*p = vnrg
      end
    | _ => True
    end
  | None => True
  end.
Proof.
  set (t2_ := t2).
  dependent induction t2.
  simpl; auto.
  simpl; auto.
  rename a into lra.
  replace (tl_tllct (theta_lambda_combine li ri))
     with (omax (tl_tllct li) (tl_tllct ri))
       by auto.
  destruct (tl_tllct li) as [llct_li|] eqn:LCTL; [|
    set (info1 := "no elements left in lhs" % string); move info1 at top].
  destruct (tl_tllct ri) as [llct_ri|] eqn:LCTR; [|
    set (info2 := "no elements left in rhs" % string); move info2 at top].
  replace (omax (Some llct_li) (Some llct_ri)) with (Some (max llct_li llct_ri)).
  destruct (tl_pop_max_env lhs) as [[[l2i l2a] [l2|]]|] eqn:R3.
  destruct (tl_envelopeΛ li) as [lvcest lvnrg].
  destruct (tl_pop_max_env rhs) as [[[r2i r2a] [r2|]]|] eqn:R5.
  destruct (tl_envelopeΛ ri) as [rvcest rvnrg].
  simpl.
  destruct (tl_envelopeΛ ri <? tl_envelopeΛ li) eqn:EnvΛLR.
  apply Nat.ltb_lt in EnvΛLR.
  rewrite R3.
  remember (maxEnvelope3 (tl_envelopeΛ li + tl_energy ri)%e
    (tl_envelope ri + tl_energyΛ ri)%e (tl_envelopeΛ ri)) as kenv.
  enough (
    kenv = (tl_envelopeΛ li + tl_energy ri)%e \/
    kenv = (tl_envelope ri + tl_energyΛ ri)%e \/
    kenv = (tl_envelopeΛ ri)).
  destruct H as [HenvΛ|[HenvΛ|HenvΛ]];
  clear Heqkenv;
  subst kenv;
  simpl.


  - generalize dependent i.

  dependent induction i; [
    set (info3 := "interleave induction: nil" % string)|
    set (info3 := "interleave induction: left (a::x) (a::z)" % string)|
    set (info3 := "interleave induction: right (a::y) (a::z)" % string)
    (*set (info3 := "interleave induction: drop (a::z)" % string)*)];
    move info3 at top.
  simpl.
  exfalso.
  apply (TLT2_nil t2_1).
  move t2_1 at bottom.
  move t2_2 at bottom.
  move IHt2_1 at bottom.
  move IHt2_2 at bottom.
  simpl.
  unfold load.
  unfold mapfold.
  simpl in *.
  (* goal:
    load (a :: z) (vcest (tl_envelopeΛ li)) (max n n0) + a_c l2a * a_p l2a =
    C * vcest (tl_envelopeΛ li) + (vnrg (tl_envelopeΛ li) + tl_energy ri)
  *)


  dependent induction i.
  exfalso.
  simpl in *.
  simpl in *.
  dependent induction i; intros.
  simpl.


  destruct (tl_pop_max_env (tlt_node C lhs rhs)); [|auto].

  simpl.
Qed.

