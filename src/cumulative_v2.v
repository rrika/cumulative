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

Structure Env := envp { vest: nat; vnrg: nat; vnrg2: nat }.
Definition evalEnvelope C (e: Env) : nat :=
  match e with envp a b c => (C*a)+b+c end.
Definition evalEnvelope2 C (e: option Env) : nat :=
  match e with Some e => evalEnvelope C e | None => 0 end.
Definition addToEnvelope (E: Env) (e: nat) :=
  envp (vest E) (vnrg E + e) (vnrg2 E).
Definition addToEnvelope2 (E: Env) (e: nat) :=
  envp (vest E) (vnrg E) (vnrg2 E + e).

Declare Scope env_scope.
Delimit Scope env_scope with e.
Notation "a + b" := (addToEnvelope a b) : env_scope.

Definition maxEnvelope C (x y: Env) : Env :=
  if (evalEnvelope C x) <? (evalEnvelope C y) then y else x.

Definition maxEnvelope3 C (x y z: Env) : Env :=
  maxEnvelope C x (maxEnvelope C y z).

Record ThetaLambdaInner := mkTLInner {
  tl_teest_tllct : option (nat * nat); (* only present when any theta leaf *)
  (* tl_teest       : option nat; (* earliest start of a theta task *) *)
  (* tl_tllct       : option nat; (* latest completion of a theta task *) *)

  tl_energy    : nat; (* theta tasks only *)
  tl_envelope  : Env; (* theta tasks only *)
  tl_energyΛ   : nat; (* lambda tasks only *)
  tl_dataΛ     : option (Env * nat) (* only present when any lambda leaf *)
  (*tl_envelopeΛ : option Env; (* theta tasks + a single lambda task *) *)
  (*tl_lelct     : option nat; (* earliest latest completion of a lambda task *) *)
}.

Definition tl_teest i := match tl_teest_tllct i with Some (a, b) => Some a | None => None end.
Definition tl_tllct i := match tl_teest_tllct i with Some (a, b) => Some b | None => None end.

Definition tl_envelopeΛ i := match tl_dataΛ i with Some (a, b) => Some a | None => None end.
Definition tl_lelct i     := match tl_dataΛ i with Some (a, b) => Some b | None => None end.

Definition theta_lambda_leaf_theta (C: nat) (a: Activity) : ThetaLambdaInner :=
  let est := (a_est a) in
  let lct := (a_lct a) in
  let e := (a_c a * a_p a) in
  mkTLInner
    (* tl_teest_tllct = *) (Some (est, lct))
    (* tl_energy      = *) e
    (* tl_envelope    = *) (envp est e 0)
    (* tl_energyΛ     = *) 0
    (* tl_dataΛ       = *) None.

Definition theta_lambda_leaf_lambda (C: nat) (a: Activity) : ThetaLambdaInner :=
  let est := (a_est a) in
  let lct := (a_lct a) in
  let e := (a_c a * a_p a) in
  mkTLInner
    (* tl_teest_tllct = *) None
    (* tl_energy      = *) 0
    (* tl_envelope    = *) (envp 0 0 0)
    (* tl_energyΛ     = *) e
    (* tl_dataΛ       = *) (Some ((envp est 0 e), lct)).

Definition theta_lambda_combine C (l: ThetaLambdaInner) (r: ThetaLambdaInner) :=
  mkTLInner
    (* tl_teest_tllct = *)
      match (tl_teest_tllct l, tl_teest_tllct r) with
      | (Some (eel, lll), Some (eer, llr)) => Some (min eel eer, max lll llr)
      | (Some (eel, lll), None) => Some (eel, lll)
      | (None, Some (eer, llr)) => Some (eer, llr)
      | (None, None) => None
      end
    (* tl_energy      = *) ((tl_energy l) + (tl_energy r))
    (* tl_envelope    = *) (maxEnvelope C (tl_envelope l) (tl_envelope r))
    (* tl_energyΛ     = *) ((tl_energyΛ l) + (tl_energyΛ r))
    (* tl_dataΛ       = *) (
      match (tl_dataΛ l, tl_dataΛ r) with
      | (Some (el, kl), Some (er, kr)) => Some (maxEnvelope3 C
          (addToEnvelope el (tl_energy r))
          (addToEnvelope2 (tl_envelope l) (tl_energyΛ r))
          er
        , min kl kr)
      | (Some (el, kl), None         ) => Some (addToEnvelope el (tl_energy r), kl)
      | (None,          Some (er, kr)) => Some ((maxEnvelope C
          (addToEnvelope2 (tl_envelope l) (tl_energyΛ r))
          er), kr)
      | (None,          None         ) => None
      end).

Inductive ThetaLambdaTree (C: nat) : ThetaLambdaInner -> Type :=
| tlt_theta (i: nat) (a: Activity) :
    ThetaLambdaTree C (theta_lambda_leaf_theta C a)
| tlt_lambda (i: nat) (a: Activity) :
    ThetaLambdaTree C (theta_lambda_leaf_lambda C a)
| tlt_node {li ri}
    (lhs: ThetaLambdaTree C li)
    (rhs: ThetaLambdaTree C ri) :
    ThetaLambdaTree C (theta_lambda_combine C li ri).

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

Theorem tl_teest_tllct_none_recursive C a b :
  tl_teest_tllct (theta_lambda_combine C a b) = None ->
  tl_teest_tllct a = None /\
  tl_teest_tllct b = None.
Proof.
  simpl.
  intro.
  destruct (tl_teest_tllct a) as [[eel lll]|];
  destruct (tl_teest_tllct b) as [[eer llr]|].
  discriminate H.
  discriminate H.
  discriminate H.
  easy.
Qed.

Theorem tl_dataΛ_none_recursive C a b :
  tl_dataΛ (theta_lambda_combine C a b) = None ->
  tl_dataΛ a = None /\
  tl_dataΛ b = None.
Proof.
  simpl.
  intro.
  destruct (tl_dataΛ a) as [[envl lelctl]|];
  destruct (tl_dataΛ b) as [[envr lelctr]|].
  discriminate H.
  discriminate H.
  discriminate H.
  easy.
Qed.

Theorem tl_load_theta_eq {C n} (est lct: nat) (x: ThetaLambdaTree C n) :
  match tl_lelct n with
  | Some lelct => lct < lelct
  | None       => True
  end ->
  tl_load_theta est lct x = tl_load_either est lct x.
Proof.
  induction x; simpl; intro Condition; intros.
  - easy.
  - unfold load1.
    destruct (a_lct a <=? lct) eqn:K.
    apply Nat.leb_le in K.
    exfalso.
    lia.
    destruct (est <=? a_est a); reflexivity.
  - enough (
      match tl_lelct li with
      | Some lelct => lct < lelct
      | None => True
      end /\
      match tl_lelct ri with
      | Some lelct => lct < lelct
      | None => True
      end).
    rewrite IHx1 by easy.
    rewrite IHx2 by easy.
    reflexivity.

    clear IHx1 IHx2 est x1 x2.
    unfold tl_lelct in *.
    destruct (tl_dataΛ li) as [[enl lll]|] eqn:EL;
    destruct (tl_dataΛ ri) as [[enr llr]|] eqn:ER;
    [
    | refine (conj _ I)
    | refine (conj I _)
    | easy ]; (
        unfold theta_lambda_combine in Condition; simpl in *;
        rewrite EL in Condition;
        rewrite ER in Condition;
        clear - Condition; lia).
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
  unfold tl_tllct in *.
  simpl.
  destruct (tl_teest_tllct li) as [[eel lll]|];
    destruct (tl_teest_tllct ri) as [[eer llr]|]; simpl; try apply I.
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


Definition argMaxEnvelope C (x y: Env) {A} (t u: A) : A :=
  if (evalEnvelope C x) <? (evalEnvelope C y) then u else t.

Definition argMaxEnvelope3 C (x y z: Env) {A} (t u v : A) : A :=
  let yz :=    maxEnvelope C y z in
  let uv := argMaxEnvelope C y z u v in
  argMaxEnvelope C x yz t uv.

Inductive LR : Type :=
| ll
| rr.

Inductive Path {C: nat} {leaf_inner} {leaf_node: ThetaLambdaTree C leaf_inner} :
  forall root_inner (root_node: ThetaLambdaTree C root_inner), Type :=
| tp_leaf :
    Path leaf_inner leaf_node
| tp_left {nl nr lhs rhs} :
    Path nl lhs ->
    Path (theta_lambda_combine C nl nr) (tlt_node C lhs rhs)
| tp_right {nl nr lhs rhs} :
    Path nr rhs ->
    Path (theta_lambda_combine C nl nr) (tlt_node C lhs rhs).


Fixpoint path_simplify {C: nat} {leafn leaft rootn roott}
  (tpl: @Path C leafn leaft rootn roott) :
  list LR
:=
  match tpl with
  | tp_leaf => nil
  | tp_left subpath => (cons ll (path_simplify subpath))
  | tp_right subpath => (cons rr (path_simplify subpath))
  end.

Definition is_leaf {C n} (x: ThetaLambdaTree C n) := match x with
  | tlt_theta _ _ _ => true
  | tlt_lambda _ _ _=> true
  | tlt_node _ _ _ => false
  end.

Fixpoint tl_remove_path {C}
  {leafn leafx rootn} rootx
  (p: @Path C leafn leafx rootn rootx) :
  option {n : ThetaLambdaInner & ThetaLambdaTree C n }
:=
  match p with
  | tp_leaf => None
  | @tp_left _ _ _ l r lhs rhs subpath =>
    match tl_remove_path lhs subpath with
    | Some (existT _ newl newlhs) =>
      Some (existT _ _ (@tlt_node C newl r newlhs rhs))
    | None =>
      Some (existT _ r rhs)
    end
  | @tp_right _ _ _ l r lhs rhs subpath =>
    match tl_remove_path rhs subpath with
    | Some (existT _ newr newrhs) =>
      Some (existT _ _ (@tlt_node C l newr lhs newrhs))
    | None =>
      Some (existT _ l lhs)
    end
  end.

Definition tl_max_env_side C l r :=
  match (tl_dataΛ l, tl_dataΛ r) with
  | (Some (el, kl), Some (er, kr)) => (argMaxEnvelope3 C
      (*x*) (addToEnvelope el (tl_energy r))
      (*y*) (addToEnvelope2 (tl_envelope l) (tl_energyΛ r))
      (*z*) er
      (*t*) ll
      (*u*) rr
      (*v*) rr)
  | (Some _, None) => ll
  | (None, Some _) => rr
  | (None, None) => (*any*) ll
  end.

Fixpoint tl_pop_max_env_path {C n} (x: ThetaLambdaTree C n) :
  list LR :=
match x with
| tlt_theta _ i a  => nil
| tlt_lambda _ i a => nil
| @tlt_node _ l r lhs rhs =>
  match tl_max_env_side C l r with
  | ll => (cons ll (tl_pop_max_env_path lhs))
  | rr => (cons rr (tl_pop_max_env_path rhs))
  end
end.

Theorem tl_pop_max_env_path_2 {C n} (t: ThetaLambdaTree C n) :
  {ln : ThetaLambdaInner & {lx : ThetaLambdaTree C ln & @Path C ln lx n t } }.
Proof.
  pose (tl_pop_max_env_path t) as l.
  induction t; simpl in l.
  refine (existT _ _ (existT _ _ tp_leaf)).
  refine (existT _ _ (existT _ _ tp_leaf)).
  destruct (tl_max_env_side C li ri); [
    destruct IHt1 as [ln [lx subp]] |
    destruct IHt2 as [ln [lx subp]]
  ];
  refine (existT _ _ (existT _ _ _)).
  apply tp_left.
  apply subp.
  apply tp_right.
  apply subp.
Qed.

Fixpoint tl_pop_max_env {C n} (x: ThetaLambdaTree C n) :
  {n : ThetaLambdaInner & ThetaLambdaTree C n } :=
match x with
| tlt_theta _ i a  => existT _ _ x
| tlt_lambda _ i a => existT _ _ x
| @tlt_node _ l r lhs rhs =>
  let descendLeft :
    {n : ThetaLambdaInner & ThetaLambdaTree C n }
  :=
    match tl_pop_max_env lhs with
    | existT _ newl newlhs =>
      existT _ _ (@tlt_node C newl r newlhs rhs)
    end
  in
  let descendRight :
    {n : ThetaLambdaInner & ThetaLambdaTree C n }
  :=
    match tl_pop_max_env rhs with
    | existT _ newr newrhs =>
      existT _ _ (@tlt_node C l newr lhs newrhs)
    end
  in
  match (tl_dataΛ l, tl_dataΛ r) with
  | (Some (el, kl), Some (er, kr)) => (argMaxEnvelope3 C
      (*x*) (addToEnvelope el (tl_energy r))
      (*y*) (addToEnvelope2 (tl_envelope l) (tl_energyΛ r))
      (*z*) er
      (*t*) descendLeft
      (*u*) descendRight
      (*v*) descendRight
    )
  | (Some (el, kl), None         ) => descendLeft
  | (None,          Some (er, kr)) => descendRight
  | (None,          None         ) => existT _ _ x
  end
end.


(*Theorem tl_pop_max_env_some {C n} (x: ThetaLambdaTree C n) :
  tl_pop_max_env x <> None ->
  match x with
  | tlt_theta _ i a  => True
  | tlt_lambda _ i a => True
  | @tlt_node _ nl nr lhs rhs =>
    if (
      evalEnvelope2 C (tl_envelopeΛ nr) <?
      evalEnvelope2 C (tl_envelopeΛ nl)
    ) then
      tl_pop_max_env lhs <> None
    else
      tl_pop_max_env rhs <> None
  end.
Proof.
  intro; destruct x; try easy.
  simpl in H.
  destruct (evalEnvelope2 C (tl_envelopeΛ ri) <? evalEnvelope2 C (tl_envelopeΛ li)).
  now destruct (tl_pop_max_env x1).
  now destruct (tl_pop_max_env x2).
Qed.*)


Definition tl_towards_max_lct {C n} (x: ThetaLambdaTree C n) : option LR :=
match x with
| tlt_theta _ i a  => None
| tlt_lambda _ i a => None
| @tlt_node _ nl nr lhs rhs =>
  match (tl_tllct nl, tl_tllct nr) with
  | (None,       None)       => None
  | (Some lllct, None)       => Some ll
  | (None,       Some rllct) => Some rr
  | (Some lllct, Some rllct) =>
    Some (if rllct <? lllct then ll else rr)
  end
end.


Inductive Interleave {A} : list A -> list A -> list A -> Type :=
| s_nil           : Interleave nil nil nil
| s_left  a x y z : Interleave x y z -> Interleave (a::x) y (a::z)
| s_right a x y z : Interleave x y z -> Interleave x (a::y) (a::z).

Definition tl_llct_prop (tl: ThetaLambdaInner) (a:A) :=
  match (tl_tllct tl) with Some llct => a_lct a <= llct | _ => True end.

Inductive TLT2 {C} : AA -> forall {n}, ThetaLambdaTree C n -> Type :=
| tlt2_theta  i a : TLT2 (cons a nil) (tlt_theta  C i a)
| tlt2_lambda i a : TLT2 (cons a nil) (tlt_lambda C i a)
| tlt2_node {la ra a li ri}
  {lhs: ThetaLambdaTree C li}
  {rhs: ThetaLambdaTree C ri} :
  TLT2 la lhs ->
  TLT2 ra rhs ->
  Interleave (*tl_llct_prop (theta_lambda_combine li ri)*) la ra a ->
  olt (tl_tllct (theta_lambda_combine C li ri)) (tl_lelct (theta_lambda_combine C li ri)) ->
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
  - unfold tl_lelct in *.
    unfold theta_lambda_combine in H.
    destruct (tl_dataΛ li) as [[env_li lelct_li]|];
    destruct (tl_dataΛ ri) as [[env_ri lelct_ri]|];
    inversion H; 
    (rewrite IHt2_1; [rewrite IHt2_2; [reflexivity|]|]);
    clear - H1 H2;
    [left|left|right|left|left|right]; try reflexivity;
    [exists lelct_ri|exists lelct_li|exists lelct_li|exists lelct_ri];
    refine (conj eq_refl _); lia.
  - unfold theta_lambda_combine in H.
    pose proof (tl_load_theta_eq est lct lhs) as EL.
    pose proof (tl_load_theta_eq est lct rhs) as ER.
    unfold tl_lelct in *.
    destruct (tl_dataΛ li) as [[env_li lelct_li]|];
    destruct (tl_dataΛ ri) as [[env_ri lelct_ri]|];
    simpl in H;
    inversion H.
    rewrite EL by apply I.
    rewrite ER by apply I.
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
  unfold tl_tllct in *.
  unfold theta_lambda_combine in H.
  destruct (tl_teest_tllct li) as [[teest_li tllct_li]|];
  destruct (tl_teest_tllct ri) as [[teest_ri tllct_ri]|];
  inversion H; clear H;
  (rewrite <- IHx1; [rewrite <- IHx2; [reflexivity|]|]);
  [left|left|right|left|left|right]; try reflexivity;
  [exists tllct_ri|exists tllct_li|exists tllct_li|exists tllct_ri];
  (constructor; try reflexivity); lia.

  simpl in *.
  unfold tl_tllct in *.
  unfold theta_lambda_combine in H.
  destruct (tl_teest_tllct li) as [[teest_li tllct_li]|];
  destruct (tl_teest_tllct ri) as [[teest_ri tllct_ri]|];
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
      match tl_envelopeΛ n with envp vest vnrg =>
        let c  := a_c a in 
        let p  := a_p a in 
        tl_load_either vest llct x + c*p = vnrg
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


(*
Theorem tl_pop_max_env_load_simplified {X C n} {x: ThetaLambdaTree C n}
  (t2: TLT2 X x) lct vest vnrg vnrg2 lelct :
  lct < lelct ->
  tl_dataΛ n = Some ((envp vest vnrg vnrg2), lelct) ->
  tl_load_theta vest lct x = vnrg.
Proof.
  induction t2; simpl; auto.
  destruct (maxEnvelopeO3Either
    (addToEnvelope3 (tl_envelopeΛ li) (tl_energy ri))
    (addToEnvelope2 (tl_envelope ri) (tl_energyΛ ri)) 
    (tl_envelopeΛ ri)) as [H|[H|H]]; rewrite H; clear H.
  destruct li.
  destruct ri.
  destruct tl_envelopeΛ0.
  destruct tl_envelopeΛ1.
  destruct e.
  destruct e0.
  simpl in *.
  destruct tl_tllct0.
  destruct tl_tllct1.
  simpl in *.
Admitted.

Theorem tl_can_pop_has_data {C nf} {x: ThetaLambdaTree C nf} :
  tl_dataΛ nf <> None <-> tl_pop_max_env x <> None.
Proof.
  induction x; simpl; intros.
  constructor; contradiction.
  constructor; intros A B; discriminate B.
  destruct IHx1.
  destruct IHx2.
  unfold tl_envelopeΛ.
  destruct (tl_dataΛ li) as [[dle dlj]|]; destruct (tl_pop_max_env x1);
    [|exfalso; now apply H|exfalso; now apply H0|];
  (destruct (tl_dataΛ ri) as [[dre drj]|]; destruct (tl_pop_max_env x2);
    [|exfalso; now apply H1|exfalso; now apply H2|]);
  (constructor; intro Z; [clear Z| try (clear; easy)]).
  - destruct (evalEnvelope2 C (Some dre) <? evalEnvelope2 C (Some dle)).
    destruct p  as [[pi pa] po]. destruct po; easy.
    destruct p0 as [[pi pa] po]. destruct po; easy.
  - simpl.
     destruct (evalEnvelope2 C (tl_envelopeΛ ri) <? evalEnvelope2 C (tl_envelopeΛ li)) eqn:B.
    destruct p  as [[pi pa] po]. destruct po; easy.
    
    destruct p0 as [[pi pa] po]. destruct po; easy.
    

    simpl; destruct p; destruct p; destruct o; easy.
    simpl; destruct p0.
    simpl; destruct p; destruct p; destruct o; easy.  
  admit.
  admit.
  admit.
  admit.
  admit.
Admitted.*)

Compute 0.

(*

Inductive Update (c p: nat) (oe ol: nat) (ne nl: nat) : AA -> AA -> Type :=
| u1 a xs ys : Update c p oe ol ne nl xs ys ->
               Update c p oe ol ne nl (cons a xs) (cons a ys)
| u0 s       : Update c p oe ol ne nl 
                  (cons (mkActivity oe ol c p) s)
                  (cons (mkActivity ne nl c p) s).
*)

Record SingleUpdate := mkSu {
  su_c : nat;
  su_p : nat;
  su_oe : nat;
  su_ol : nat;
  su_ne : nat;
  su_nl : nat;
}.

Definition u0m (c p oe ol ne nl : nat) (a b: A) (s: AA) :
  a = (mkActivity oe ol c p) ->
  b = (mkActivity ne nl c p) ->
  Update c p oe ol ne nl (cons a s) (cons b s).
Proof.
  intros HA HB.
  rewrite HA.
  rewrite HB.
  apply u0.
Qed.

Theorem TLT2_X_of_lambda {X C i a} (t: TLT2 X (tlt_lambda C i a)) :
  X = (cons a nil).
Proof.
  inversion t.
  reflexivity.
Qed.

Definition update_single_for_overload_lct (a: Activity) (overload_lct: nat) :=
  mkActivity (a_est a) (overload_lct + (a_p a) - 1) (a_c a) (a_p a).

(*  Z    = 1 9 8 2 3 7 6 4  ^ *)
(*  X1   = 1 - - 2 3 - - 4  ^ *)
(*  Y    = - 9 8 - - 7 6 -  | *)
(*  X2   = 5 - - 5 5 - - 5  v *)
(*  return 5 9 8 5 5 7 6 5  v *)

Fixpoint interleave_replace_left {A} (X1 X2 Y Z: list A)
  (i: Interleave X1 Y Z) : list A :=
match i with
| s_nil  => nil
| s_left a x y z s =>
  match X2 with
  | (cons a2 x2) => (a2 :: interleave_replace_left _ x2 y z s)
  | _ => nil (* not enough replacements *)
  end
| s_right a x y z s => (a :: interleave_replace_left _ X2 y z s)
end.

Theorem interleave_replace_left_nop {A} (X Y Z: list A)
  (i: Interleave X Y Z) :
  interleave_replace_left X X Y Z i = Z.
Proof.
  induction i; auto.
  all: simpl; rewrite IHi; reflexivity.
Qed.

Theorem interleave_replace_left_spec {A} (X1 X2 Y Z: list A) 
  (i: Interleave X1 Y Z) :
  List.length X1 = List.length X2 ->
  Interleave X2 Y (interleave_replace_left X1 X2 Y Z i).
Proof.
  intros.
  generalize dependent X2.
  induction i; intros.
  - simpl in *.
    destruct X2.
    apply s_nil.
    discriminate H.
  - destruct X2; simpl in H.
    discriminate H.
    inversion H.
    simpl.
    specialize (IHi X2 H1).
    apply s_left.
    apply IHi.
  - simpl.
    apply s_right.
    apply IHi.
    apply H.
Qed.

Fixpoint interleave_replace_right {A} (X Y1 Y2 Z: list A)
  (i: Interleave X Y1 Z) : list A :=
match i with
| s_nil  => nil
| s_right a x y z s =>
  match Y2 with
  | (cons a2 y2) => (a2 :: interleave_replace_right x _ y2 z s)
  | _ => nil (* not enough replacements *)
  end
| s_left a x y z s => (a :: interleave_replace_right x _ Y2 z s)
end.

Theorem interleave_replace_right_nop {A} (X Y Z: list A)
  (i: Interleave X Y Z) :
  interleave_replace_right X Y Y Z i = Z.
Proof.
  induction i; auto.
  all: simpl; rewrite IHi; reflexivity.
Qed.

(* update from - - - A B C - - -
            to - - - D E F - - -
            to construct an
   update from I J K A B C L M N
            to I J K D E F L M N
*)

Theorem update_left
  {X XL YL R}
  {c p oe ol ne nl}
  (i : Interleave XL R X) : 
  Update c p oe ol ne nl XL YL ->
  Update c p oe ol ne nl X (interleave_replace_left XL YL R X i).
Proof.
  generalize dependent YL.
  induction i; intros.
  - inversion H.
  - inversion H; subst.
    + apply u1.
      apply IHi.
      apply H3.
    + simpl in *.
      rewrite interleave_replace_left_nop.
      apply u0.
  - simpl.
    apply u1.
    apply IHi.
    apply H.
Qed.

Theorem update_right
  {X L XR YR}
  {c p oe ol ne nl}
  (i : Interleave L XR X) : 
  Update c p oe ol ne nl XR YR ->
  Update c p oe ol ne nl X (interleave_replace_right L XR YR X i).
Proof.
  generalize dependent YR.
  induction i; intros.
  - inversion H.
  - simpl.
    apply u1.
    apply IHi.
    apply H.
  - inversion H; subst.
    + apply u1.
      apply IHi.
      apply H3.
    + simpl in *.
      rewrite interleave_replace_right_nop.
      apply u0.
Qed.

Theorem update_by_tl_pop
  {X C n e} {x: ThetaLambdaTree C n} (t2: TLT2 X x) (overload_lct: nat)
:
  tl_dataΛ n = Some e ->
  { su : SingleUpdate & { Y : AA & (prod 
    (su_ol su = su_nl su)
    (Update (su_c su)  (su_p su)
            (su_oe su) (su_ol su)
            (su_ne su) (su_nl su)
     X Y)
  ) } }.
Proof.
  generalize dependent e.
  induction t2; intros; simpl in *.
  (* theta *)
  - discriminate H.
  (* lambda *)
  - (* a is the select lambda task *)
    set (mkActivity
      (overload_lct + (a_p a) - 1)
      (a_lct a)
      (a_c a)
      (a_p a)
    ) as b.
    set (mkSu
      (a_c a)
      (a_p a)
      (a_est a)
      (a_lct a)
      (a_est b)
      (a_lct b)
    ) as su.
    exists su.
    exists (cons b nil).
    refine (eq_refl, _).
    apply u0m.
    destruct a; reflexivity.
    unfold b; reflexivity.

  (* inner node *)
  - destruct (tl_dataΛ li) as [[el el_]|] eqn:B1;
    destruct (tl_dataΛ ri) as [[er er_]|] eqn:B2;
    subst.
    specialize (IHt2_1 (el, el_) eq_refl).
    specialize (IHt2_2 (er, er_) eq_refl).

    unfold maxEnvelope3 in H.
    unfold maxEnvelope in H.

    destruct (evalEnvelope C (el + tl_energy ri)%e <?
        evalEnvelope C
          (if
            evalEnvelope C
              (addToEnvelope2 (tl_envelope li) (tl_energyΛ ri)) <?
            evalEnvelope C er
           then er
           else addToEnvelope2 (tl_envelope li) (tl_energyΛ ri))).
    (* both sides have Λ, right side wins *)
    clear IHt2_1.
    destruct IHt2_2 as [su [YR [YE YU]]].
    exists su.
    exists (interleave_replace_right la ra YR a i).
    refine (YE, _).
    apply update_right.
    apply YU.
    (* both sides have Λ, left side wins *)
    clear IHt2_2.
    destruct IHt2_1 as [su [XL [XE XU]]].
    exists su.
    exists (interleave_replace_left la XL ra a i).
    refine (XE, _).
    apply update_left.
    apply XU.
    (* left side has Λ *)
    clear IHt2_2.
    specialize (IHt2_1 (el, el_) eq_refl).
    destruct IHt2_1 as [su [XL [XE XU]]].
    exists su.
    exists (interleave_replace_left la XL ra a i).
    refine (XE, _).
    apply update_left.
    apply XU.
    (* right side has Λ *)
    clear IHt2_1.
    specialize (IHt2_2 (er, er_) eq_refl).
    destruct IHt2_2 as [su [YR [YE YU]]].
    exists su.
    exists (interleave_replace_right la ra YR a i).
    refine (YE, _).
    apply update_right.
    apply YU.
    (* contradiction *)
    discriminate H.
Qed.

Theorem UNUSED_extend_proof_by_tl_pop
  {X C n e} {x: ThetaLambdaTree C n} (t2: TLT2 X x)
  {K} (baseproof: Proof C K X)
:
  tl_dataΛ n = Some e (*(env, lelct)*) ->
  (* vnrg env + vnrg2 vnrg > C * (lelct - vest env) -> *)
  { Y : AA & Proof C K Y }.
Proof.
  intro.
  destruct e as [[vest vnrg vnrg2] tllct].
  destruct (update_by_tl_pop t2 tllct H) as [[c p oe ol ne nl] [Y [m update]]].
  simpl in *.

  destruct (ne + p <=? ol) eqn:U;
    relb_to_rel.
  destruct (C * (ne + p - 1 - oe) <? load X oe (ne + p - 1) + c * p) eqn:B;
    relb_to_rel.

  exists Y.
  rewrite <- m in update.
  apply (p_step C K X Y
    c p oe ne ol
    baseproof
    update).
  apply ps_tighten_est_plain.
  apply B.
  apply U.

  (* not actually overloaded, return input unmodified *)
  exists X.
  exact baseproof.

  (* this set of tasks isn't schedulable, the chosen
     task was reduced to less than its minimum time.
     the Proof datatype currently doesn't have a good
     way of encoding this, so return input unmodified *)
  exists X.
  exact baseproof.
Qed.

Theorem proofstep_by_tl_pop
  {X C n e} {x: ThetaLambdaTree C n} (t2: TLT2 X x)
:
  tl_dataΛ n = Some e ->
  option { c : nat &
  { p : nat &
  { oe : nat &
  { ne : nat &
  { l : nat &
  { Y : AA &
    prod
    (Update c p oe l ne l X Y)
    (ProofStep C X c p oe ne l)
  } } } } } }.
Proof.
  intro.
  destruct e as [[vest vnrg vnrg2] tllct].
  destruct (update_by_tl_pop t2 tllct H) as [[c p oe ol ne nl] [Y [m update]]].
  simpl in *.

  destruct (ne + p <=? ol) eqn:U;
    relb_to_rel.
  destruct (C * (ne + p - 1 - oe) <? load X oe (ne + p - 1) + c * p) eqn:B;
    relb_to_rel.
  apply Some.

  exists c.
  exists p.
  exists oe.
  exists ne.
  exists ol.
  exists Y.
  rewrite <- m in update.
  refine ((update, _)).
  apply ps_tighten_est_plain.
  apply B.
  apply U.

  (* not actually overloaded *)
  apply None.

  (* this set of tasks isn't schedulable, the chosen
     task was reduced to less than its minimum time.
     the Proof datatype currently doesn't have a good
     way of encoding this *)
  apply None.
Qed.

Theorem proofstep_over_subset
  {X XO XT YT C}
  (c p oe ne l : nat)
  (i: Interleave XT XO X)
:
  Update c p oe l ne l XT YT ->
  ProofStep C XT c p oe ne l ->
  prod
    (Update c p oe l ne l X (interleave_replace_left XT YT XO X i))
    (ProofStep C X c p oe ne l).
Proof.
  intros.
  destruct H0; (constructor; [apply update_left; apply H|]).
  - apply ps_tighten_est_plain.
    pose proof (interleave_load i oe (ne + p - 1)).
    lia.
    assumption.
  - (* ps_tighten_est_partial *)
    apply (ps_tighten_est_partial) with (xe:=xe) (xl:=xl) (nep:=nep); auto.
    pose proof (interleave_load i xe xl).
    lia.
Qed.

Require Import Coq.Sorting.Mergesort.
Require Import Coq.Sorting.Permutation.
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

Theorem load_permute est lct X Y (p: Permutation X Y) :
  load X est lct = load Y est lct.
Proof.
  induction p; try reflexivity;
    unfold load in *; unfold mapfold in *; simpl; lia.
Qed.

Theorem load_interleave_bounds est lct A B C (i: Interleave A B C) :
  load A est lct <= load C est lct /\ load B est lct <= load C est lct.
Proof.
  unfold load.
  unfold mapfold.
  induction i.
  auto.
  simpl in *.
  lia.
  simpl in *.
  lia.
Qed.

Theorem interleave_move_one_to_right {A} {X Y Z: list A} {a: A}
  (I: Interleave (a::X) Y Z) :
  { Y2 : list A & Interleave X Y2 Z}.
Proof.
  dependent induction I.
  - exists (a :: y).
    apply s_right.
    apply I.
  - specialize (IHI X a eq_refl).
    destruct IHI.
    exists (a0 :: x).
    apply s_right.
    apply i.
Qed.

(*
         aa_total, mi
           /      \
      aa_tree    aa_removed
         /
    tl2, n, e
       /
  t, C -> n2, t2
*)

Compute 0.

Fixpoint drop_updated {c p oe ol ne nl X Y} (U: Update c p oe ol ne nl X Y) : AA :=
  match U with
  | u1 _ _ _ _ _ _ a xs ys us => (cons a (drop_updated us))
  | u0 _ _ _ _ _ _ s => s
  end.

Definition update_interleave_for_pop
  (C : nat)
  (aa_tree aa_removed aa_total : AA)
  (mi: Interleave aa_tree aa_removed aa_total)
  {c p oe ol ne nl} (aa_tree_u: AA) (U: Update c p oe ol ne nl aa_tree aa_tree_u)
:
  { aa_removed' : AA &
  (Interleave (drop_updated U) aa_removed' aa_total) }.
  (*prod (Interleave aa_tree' aa_removed' aa_total)
       (option (@TLT2 C aa_tree' n t)) } }.*)
Proof.
  generalize dependent aa_tree_u.
  induction mi; intros.
  - (* nothing to pop *)
    inversion U.
  - (* interleave focused on element of aa_tree, what did the update do with this element? *)
    dependent destruction U.
    + destruct (IHmi ys U) as [aa_removed' mii].
      exists aa_removed'.
      simpl.
      apply s_left.
      apply mii.
    + (* update modified this element. thus it gets removed *)
      clear IHmi.
      eexists (cons _ y).
      apply s_right.
      simpl.
      apply mi.
  - (* interleave focused on element of aa_removed *)
    destruct (IHmi aa_tree_u U) as [aa_removed' IHmi'].
    exists (cons a aa_removed').
    apply s_right.
    apply IHmi'.
Qed.


Definition update_interleave_for_pop_x
  (C : nat)
  (aa_tree aa_tree_u aa_removed aa_total : AA)
  (mi: Interleave aa_tree aa_removed aa_total)
  (aa_total' := interleave_replace_left aa_tree aa_tree_u aa_removed aa_total mi)
  {c p oe ol ne nl} (U: Update c p oe ol ne nl aa_tree aa_tree_u)
:
  { aa_removed' : AA &
  (Interleave (drop_updated U) aa_removed' aa_total') }.
Proof.
  generalize dependent aa_tree_u.
  induction mi; intros.
  - (* nothing to pop *)
    inversion U.
  - (* interleave focused on element of aa_tree, what did the update do with this element? *)
    dependent destruction U.
    + destruct (IHmi ys U) as [aa_removed' mii].
      exists aa_removed'.
      simpl.
      apply s_left.
      apply mii.
    + (* update modified this element. thus it gets removed *)
      subst aa_total'.
      clear IHmi.
      eexists (cons _ y).
      apply s_right.
      rewrite interleave_replace_left_nop.
      apply mi.
  - (* interleave focused on element of aa_removed *)
    destruct (IHmi aa_tree_u U) as [aa_removed' IHmi'].
    exists (cons a aa_removed').
    apply s_right.
    apply IHmi'.
Qed.

Definition deinterleave_update
  {c p oe ol ne nl} {Z Z'} (U: Update c p oe ol ne nl Z Z')
  {X Y} (mi: Interleave X Y Z)
:
   sum ({X': AA & Update c p oe ol ne nl X X'}) ({Y': AA & Update c p oe ol ne nl Y Y'}).
Proof.
  generalize dependent Y.
  generalize dependent X.
  induction U; intros.
  - (* update happens further down *)
    dependent destruction mi.
    + specialize (IHU x y mi). (* top is from left *)
      destruct IHU; [left|right].
      * (* updated item is on left, take *)
        destruct s as [X' U'].
        exists (cons a X').
        apply u1.
        apply U'.
      * (* updated item is on right, skip *)
        apply s.
   + specialize (IHU x y mi). (* top is from right *)
      destruct IHU; [left|right].
      * (* updated item is on left, skip *)
        apply s.
      * (* updated item is on right, take *)
        destruct s as [X' U'].
        exists (cons a X').
        apply u1.
        apply U'.
  - (* update is here *)
    dependent destruction mi.
    + left.
      eexists (cons _ x).
      apply u0.
    + right.
      eexists (cons _ y).
      apply u0.
Qed.

Definition deinterleave_update_
  {c p oe ol ne nl} {Z Z'} (U: Update c p oe ol ne nl Z Z')
  {X Y} (mi: Interleave X Y Z)
:
   sum ({X': AA & {XU: Update c p oe ol ne nl X X' & Interleave (drop_updated XU) Y (drop_updated U) } })
       ({Y': AA & {YU: Update c p oe ol ne nl Y Y' & Interleave X (drop_updated YU) (drop_updated U) } }).
Proof.
  generalize dependent Y.
  generalize dependent X.
  induction U; intros.
  - (* update happens further down *)
    dependent destruction mi.
    + specialize (IHU x y mi). (* top is from left *)
      destruct IHU; [left|right].
      * (* updated item is on left, take *)
        destruct s as [X' [U' mii]].
        exists (cons a X').
        exists (u1 _ _ _ _ _ _ _ _ _ U').
        simpl.
        apply s_left.
        apply mii.
      * (* updated item is on right, skip *)
        destruct s as [Y' [U' mii]].
        exists Y'.
        exists U'.
        simpl.
        apply s_left.
        apply mii.
   + specialize (IHU x y mi). (* top is from right *)
      destruct IHU; [left|right].
      * (* updated item is on left, skip *)
        destruct s as [X' [U' mii]].
        exists X'.
        exists U'.
        simpl.
        apply s_right.
        apply mii.
      * (* updated item is on right, take *)
        destruct s as [Y' [U' mii]].
        exists (cons a Y').
        exists (u1 _ _ _ _ _ _ _ _ _ U').
        simpl.
        apply s_right.
        apply mii.
  - (* update is here *)
    dependent destruction mi.
    + left.
      eexists (cons _ x).
      exists (u0 _ _ _ _ _ _ _).
      auto.
    + right.
      eexists (cons _ y).
      exists (u0 _ _ _ _ _ _ _).
      auto.
Qed.

Theorem tl_tllct_combined {C li ri} :
  tl_tllct (theta_lambda_combine C li ri) = omax (tl_tllct li) (tl_tllct ri).
Proof.
  destruct li.
  destruct ri.
  unfold theta_lambda_combine.
  unfold tl_tllct.
  simpl.
  unfold omax.
  unfold olift.
  destruct tl_teest_tllct0.
  destruct p.
  destruct tl_teest_tllct1.
  destruct p.
  reflexivity.
  reflexivity.
  destruct tl_teest_tllct1.
  destruct p.
  reflexivity.
  reflexivity.
Qed.

Theorem tl_lelct_combined {C li ri} :
  tl_lelct (theta_lambda_combine C li ri) = omin (tl_lelct li) (tl_lelct ri).
Proof.
  destruct li.
  destruct ri.
  unfold theta_lambda_combine.
  unfold tl_lelct.
  simpl.
  unfold omin.
  unfold olift.
  destruct tl_dataΛ0.
  destruct p.
  destruct tl_dataΛ1.
  destruct p.
  reflexivity.
  reflexivity.
  destruct tl_dataΛ1.
  destruct p.
  reflexivity.
  reflexivity.
Qed.

Theorem olt_omax_split {a b c} :
  olt (omax a b) c ->
  (olt a c) /\ (olt b c).
Proof.
  intros.
  destruct a as [a|];
  destruct b as [b|];
  destruct c as [c|];
  unfold olt in *; try auto.
  unfold omax in H.
  unfold olift in H.
  constructor; lia.
Qed.

Theorem olt_omax_join {a b c} :
  olt a c -> olt b c ->
  olt (omax a b) c.
Proof.
  intros.
  destruct a as [a|];
  destruct b as [b|];
  destruct c as [c|];
  unfold olt in *; try auto.
  unfold omax.
  unfold olift.
  lia.
Qed.

Theorem olt_omin_split {a b c} :
  olt a (omin b c) ->
  (olt a b) /\ (olt a c).
Proof.
  intros.
  destruct a as [a|];
  destruct b as [b|];
  destruct c as [c|];
  unfold olt in *; try auto.
  unfold omin in H.
  unfold olift in H.
  constructor; lia.
Qed.

Theorem olt_omin_join {a b c} :
  olt a b -> olt a c ->
  olt a (omin b c).
Proof.
  intros.
  destruct a as [a|];
  destruct b as [b|];
  destruct c as [c|];
  unfold olt in *; try auto.
  unfold omin.
  unfold olift.
  lia.
Qed.

Inductive LeA : option nat -> option nat -> Type :=
| lea0     :         LeA None     None
| lea1 b   :         LeA None     (Some b)
| lea2 a b : a<=b -> LeA (Some a) (Some b).

Inductive LeB : option nat -> option nat -> Type :=
| leb0     :         LeB None     None
| leb1 a   :         LeB (Some a) None
| leb2 a b : a<=b -> LeB (Some a) (Some b).


Theorem transitive_le_lt {a b c} :
  LeA a b -> olt b c -> olt a c.
Proof.
  intros.
  destruct H; unfold olt; auto.
  destruct c; auto.
  unfold olt in *.
  lia.
Qed.

Theorem transitive_lt_le {a b c} :
  olt a b -> LeB b c -> olt a c.
Proof.
  intros.
  destruct H0; unfold olt; auto.
  destruct a; auto.
  destruct a; auto.
  unfold olt in *.
  lia.
Qed.

Theorem transitive_le_lt_le {a b c d} :
  LeA a b -> olt b c -> LeB c d -> olt a d.
Proof.
  intros.
  destruct H;
  destruct H1; unfold olt; auto.
  unfold olt in H0.
  lia.
Qed.

Inductive Gap (a b c d: option nat) : Type :=
| gap : LeA a b -> LeB c d -> Gap a b c d.

Theorem gap_nones {a b c d} : Gap a b c d -> (b = None -> a = None) /\ (c = None -> d = None).
Proof.
  intro.
  destruct H; destruct l; destruct l0; auto; constructor; auto; intro; inversion H.
Qed.

Theorem tlt2_node_condition_adapt_left {C li ri li'}
  (G: Gap (tl_tllct li') (tl_tllct li) (tl_lelct li) (tl_lelct li')) :
  olt (tl_tllct (theta_lambda_combine C li ri)) (tl_lelct (theta_lambda_combine C li ri)) ->
  olt (tl_tllct (theta_lambda_combine C li' ri)) (tl_lelct (theta_lambda_combine C li' ri)).
Proof.
  rewrite tl_tllct_combined.
  rewrite tl_tllct_combined.
  rewrite tl_lelct_combined.
  rewrite tl_lelct_combined.
  clear C.
  remember (tl_tllct li') as A.
  remember (tl_tllct li)  as B.
  remember (tl_tllct ri)  as X.
  remember (tl_lelct ri)  as Y.
  remember (tl_lelct li)  as C.
  remember (tl_lelct li') as D.
  clear - G.
  destruct G as [A_B C_D].
  intros BX_CY.
  destruct (olt_omax_split BX_CY) as [B_CY X_CY]; clear BX_CY.
  destruct (olt_omin_split B_CY) as [B_C B_Y]; clear B_CY.
  destruct (olt_omin_split X_CY) as [X_C X_Y]; clear X_CY.
  apply olt_omax_join; apply olt_omin_join.
  apply (transitive_le_lt_le A_B B_C C_D).
  refine (transitive_le_lt A_B B_Y).
  refine (transitive_lt_le X_C C_D).
  apply X_Y.
Qed.

Theorem tlt2_node_condition_adapt_left_2 {C li ri li'}
  (G: Gap (tl_tllct li') (tl_tllct li) (tl_lelct li) (tl_lelct li')) :
  Gap (tl_tllct (theta_lambda_combine C li' ri)) (tl_tllct (theta_lambda_combine C li ri))
      (tl_lelct (theta_lambda_combine C li ri)) (tl_lelct (theta_lambda_combine C li' ri)).
Proof.
  rewrite tl_tllct_combined.
  rewrite tl_tllct_combined.
  rewrite tl_lelct_combined.
  rewrite tl_lelct_combined.
  destruct G as [GA GB].
  unfold omax; unfold olift.
  constructor; [clear GB|clear GA].
  destruct GA.
  destruct (tl_tllct ri).
    apply lea2; auto.
    apply lea0.
  destruct (tl_tllct ri).
    apply lea2; lia.
    apply lea1.
  destruct (tl_tllct ri).
    apply lea2; lia.
    apply lea2; lia.
  destruct GB.
  destruct (tl_lelct ri).
    apply leb2; auto.
    apply leb0.
  destruct (tl_lelct ri).
    apply leb2; lia.
    apply leb1.
  destruct (tl_lelct ri).
    apply leb2; lia.
    apply leb2; lia.
Qed.

Theorem tlt2_node_condition_adapt_right {C li ri ri'}
  (G: Gap (tl_tllct ri') (tl_tllct ri) (tl_lelct ri) (tl_lelct ri')) :
  olt (tl_tllct (theta_lambda_combine C li ri)) (tl_lelct (theta_lambda_combine C li ri)) ->
  olt (tl_tllct (theta_lambda_combine C li ri')) (tl_lelct (theta_lambda_combine C li ri')).
Proof.
  rewrite tl_tllct_combined.
  rewrite tl_tllct_combined.
  rewrite tl_lelct_combined.
  rewrite tl_lelct_combined.
  clear C.
  remember (tl_tllct ri') as A.
  remember (tl_tllct ri)  as B.
  remember (tl_tllct li)  as X.
  remember (tl_lelct li)  as Y.
  remember (tl_lelct ri)  as C.
  remember (tl_lelct ri') as D.
  clear - G.
  destruct G as [A_B C_D].
  intros XB_YC.
  destruct (olt_omax_split XB_YC) as [X_YC B_YC]; clear XB_YC.
  destruct (olt_omin_split B_YC) as [B_Y B_C]; clear B_YC.
  destruct (olt_omin_split X_YC) as [X_Y X_C]; clear X_YC.
  apply olt_omax_join; apply olt_omin_join.
  apply X_Y.
  refine (transitive_lt_le X_C C_D).
  refine (transitive_le_lt A_B B_Y).
  apply (transitive_le_lt_le A_B B_C C_D).
Qed.

Theorem tlt2_node_condition_adapt_right_2 {C li ri ri'}
  (G: Gap (tl_tllct ri') (tl_tllct ri) (tl_lelct ri) (tl_lelct ri')) :
  Gap (tl_tllct (theta_lambda_combine C li ri')) (tl_tllct (theta_lambda_combine C li ri))
      (tl_lelct (theta_lambda_combine C li ri)) (tl_lelct (theta_lambda_combine C li ri')).
Proof.
  rewrite tl_tllct_combined.
  rewrite tl_tllct_combined.
  rewrite tl_lelct_combined.
  rewrite tl_lelct_combined.
  destruct G as [GA GB].
  unfold omax; unfold olift.
  constructor; [clear GB|clear GA].
  destruct GA.
  destruct (tl_tllct li).
    apply lea2; auto.
    apply lea0.
  destruct (tl_tllct li).
    apply lea2; lia.
    apply lea1.
  destruct (tl_tllct li).
    apply lea2; lia.
    apply lea2; lia.
  destruct GB.
  destruct (tl_lelct li).
    apply leb2; auto.
    apply leb0.
  destruct (tl_lelct li).
    apply leb2; lia.
    apply leb1.
  destruct (tl_lelct li).
    apply leb2; lia.
    apply leb2; lia.
Qed.

Theorem gap_trivial_left {C li ri} :
  Gap
    (tl_tllct ri)
    (tl_tllct (theta_lambda_combine C li ri))
    (tl_lelct (theta_lambda_combine C li ri))
    (tl_lelct ri).
Proof.
  constructor.
  rewrite tl_tllct_combined.
  unfold omax; unfold olift.
  destruct (tl_tllct ri).
  destruct (tl_tllct li).
  apply lea2; lia.
  apply lea2; auto.
  destruct (tl_tllct li).
  apply lea1; auto.
  apply lea0; auto.
  rewrite tl_lelct_combined.
  destruct (tl_lelct ri).
  destruct (tl_lelct li).
  apply leb2; lia.
  apply leb2; auto.
  destruct (tl_lelct li).
  apply leb1; auto.
  apply leb0; auto.
Qed.

Theorem gap_trivial_right {C li ri} :
  Gap
    (tl_tllct li)
    (tl_tllct (theta_lambda_combine C li ri))
    (tl_lelct (theta_lambda_combine C li ri))
    (tl_lelct li).
Proof.
  constructor.
  rewrite tl_tllct_combined.
  unfold omax; unfold olift.
  destruct (tl_tllct li).
  destruct (tl_tllct ri).
  apply lea2; lia.
  apply lea2; auto.
  destruct (tl_tllct ri).
  apply lea1; auto.
  apply lea0; auto.
  rewrite tl_lelct_combined.
  destruct (tl_lelct li).
  destruct (tl_lelct ri).
  apply leb2; lia.
  apply leb2; auto.
  destruct (tl_lelct ri).
  apply leb1; auto.
  apply leb0; auto.
Qed.

Definition update_tl2_for_pop
  (C : nat)
  (n : ThetaLambdaInner)
  (t : ThetaLambdaTree C n)
  (aa_tree: AA)
  (tl2 : @TLT2 C aa_tree n t)
  {c p oe ol ne nl} (aa_tree_u: AA) (U: Update c p oe ol ne nl aa_tree aa_tree_u)
:
  sum {n': ThetaLambdaInner & {t': ThetaLambdaTree C n' &
        prod (@TLT2 C (drop_updated U) n' t')
             (Gap (tl_tllct n') (tl_tllct n) (tl_lelct n) (tl_lelct n'))
  } }
      ((drop_updated U) = nil).
Proof.
  generalize dependent aa_tree_u.
  induction tl2 eqn:W; intros.
  - (* theta leaf *)
    dependent destruction U.
    inversion U.
    right.
    reflexivity.
  - (* lambda leaf *)
    dependent destruction U.
    inversion U.
    right.
    reflexivity.
  - (* inner node, deinterleave update for subtrees *)
    destruct (deinterleave_update_ U i) as [[X' [XU XPP]]|[Y' [YU YPP]]].
    + (* left side has the update *)
      clear IHt0_2.
      specialize (IHt0_1 t0_1 eq_refl X' XU).
      destruct IHt0_1.
      * (* something remains of left side after pop *)
        left.
        destruct s as [li' s].
        destruct s as [lhs' [t0_1' G]].
        eexists _.
        exists (tlt_node C lhs' rhs).
        constructor.
        apply (tlt2_node t0_1' t0_2).
        apply XPP.
        apply (@tlt2_node_condition_adapt_left C li ri li' G o).
        apply (tlt2_node_condition_adapt_left_2 G). 
      * (* left side empty, return right *)
        left.
        exists ri.
        exists rhs.
        rewrite e in XPP.
        constructor.
        apply interleave_right in XPP.
        subst.
        apply t0_2.
        apply gap_trivial_left.
    + (* right side has the update *)
      clear IHt0_1.
      specialize (IHt0_2 t0_2 eq_refl Y' YU).
      destruct IHt0_2.
      * (* something remains of right side after pop *)
        left. (* non-empty *)
        destruct s as [ri' s].
        destruct s as [rhs' [t0_2' G]].
        eexists _.
        exists (tlt_node C lhs rhs').
        constructor.
        apply (tlt2_node t0_1 t0_2').
        apply YPP.
        apply (@tlt2_node_condition_adapt_right C li ri ri' G o).
        apply (tlt2_node_condition_adapt_right_2 G). 
      * (* right side empty, return left *)
        left. (* non-empty *)
        exists li.
        exists lhs.
        rewrite e in YPP.
        apply interleave_left in YPP.
        subst.
        constructor.
        apply t0_1.
        apply gap_trivial_right.
Qed.

(*Theorem tl_pop_max_env {C n} (x: ThetaLambdaTree C n) :
  {n : ThetaLambdaInner & ThetaLambdaTree C n } :=
match x with*)

(* as a leaf is removed from the tree,
   the corresponding activity in the list is updated *)

Fixpoint theta_lambda_pop_loop
  (steps: nat)
  (C : nat)
  (n : ThetaLambdaInner)
  (t : ThetaLambdaTree C n)
  (aa_tree aa_removed aa_total : AA)
  (tl2 : @TLT2 C aa_tree n t)
  (mi: Interleave aa_tree aa_removed aa_total)
  {K} (baseproof: Proof C K aa_total)
:
  { aa_tree'    : AA &
  { aa_removed' : AA &
  prod (Interleave aa_tree' aa_removed' aa_total) (sum
    { n' : ThetaLambdaInner &
    { t' : ThetaLambdaTree C n' & @TLT2 C aa_tree' n' t'} }
    (aa_tree' = nil)) } } *
  { Z : AA & Proof C K Z }.
Proof.
  destruct steps; [
    (* 1: no more steps *) clear theta_lambda_pop_loop |
    specialize (theta_lambda_pop_loop steps C); clear steps;
    destruct (tl_dataΛ n) as [
      (* 2: have a lambda node *)
      e |
      (* 3: no more lambda nodes *)
    ] eqn:E].

  2: destruct (proofstep_by_tl_pop tl2 E) as [[c [p [oe [ne [l [Y [innerU innerP]]]]]]]|].
  (* 1: no more steps *)
  (* 2: have a lambda node and found overload *)
  (* 3: have a lambda node and found no overload *)
  (* 4: no more lambda nodes *)
  1, 3, 4: constructor; [
    exists aa_tree; exists aa_removed; refine ((mi, inl _)); exists n; exists t; apply tl2 |
    exists aa_total; apply baseproof ].

  constructor.
  (* as proofstep_by_tl_pop shrinks the list of activities, the fixpoint still has to
     show how it relates to the full list. given aa_tree, aa_removed, aa_total we now
     need a new aa_tree' and aa_removed' *)

  pose proof (update_interleave_for_pop C aa_tree aa_removed aa_total mi Y innerU).
  pose proof (update_tl2_for_pop _ _ _ _ tl2 _ innerU).
  destruct H as [aa_removed' mii].
  destruct H0 as [[n' [t' tl2']]|H0].
  exists (drop_updated innerU).
  (* pop successful *)
    exists aa_removed'.
    refine ((mii, _)).
    left.
    exists n'.
    exists t'.
    apply tl2'.
  (* empty after pop *)
    (* but we were assured that it's not by E : tl_dataΛ n = Some e *)
    rewrite H0 in *.
    exists nil.
    exists aa_removed'.
    refine ((mii, _)).
    right.
    reflexivity.

  destruct (proofstep_over_subset c p oe ne l mi innerU innerP) as [outerU outerP].
  exists (interleave_replace_left aa_tree Y aa_removed aa_total mi).
  apply (p_step C K aa_total _ c p oe ne l).
  apply baseproof.
  apply outerU.
  apply outerP.
Qed.


Fixpoint theta_lambda_pop_loop_x
  (steps: nat)
  (C : nat)
  (n : ThetaLambdaInner)
  (t : ThetaLambdaTree C n)
  (aa_tree aa_removed aa_total : AA)
  (tl2 : @TLT2 C aa_tree n t)
  (mi: Interleave aa_tree aa_removed aa_total)
  {K} (baseproof: Proof C K aa_total)
:
  { aa_total'   : AA & 
  { aa_tree'    : AA &
  { aa_removed' : AA &
  prod (prod (Interleave aa_tree' aa_removed' aa_total') (sum
    { n' : ThetaLambdaInner &
    { t' : ThetaLambdaTree C n' & @TLT2 C aa_tree' n' t'} }
    (aa_tree' = nil)))
  (Proof C K aa_total') } } }.
Proof.

  destruct steps; [
    (* 1: no more steps *) clear theta_lambda_pop_loop_x |
    specialize (theta_lambda_pop_loop_x steps C); clear steps;
    destruct (tl_dataΛ n) as [
      (* 2: have a lambda node *)
      e |
      (* 3: no more lambda nodes *)
    ] eqn:E].

  2: destruct (proofstep_by_tl_pop tl2 E) as
       [[c [p [oe [ne [l [aa_tree' [innerU innerP]]]]]]]|].

  (* 1: no more steps *)
  (* 2: have a lambda node and found overload *)
  (* 3: have a lambda node and found no overload *)
  (* 4: no more lambda nodes *)
  1, 3, 4:
    exists aa_total; exists aa_tree; exists aa_removed; refine (((mi, inl _)), baseproof); exists n; exists t; apply tl2.


  (* as proofstep_by_tl_pop shrinks the list of activities, the fixpoint still has to
     show how it relates to the full list. given aa_tree, aa_removed, aa_total we now
     need a new aa_tree' and aa_removed' *)

  pose proof (update_interleave_for_pop_x C aa_tree aa_tree' aa_removed aa_total mi innerU).
  exists (*aa_total'=*) (interleave_replace_left aa_tree aa_tree' aa_removed aa_total mi).
  pose proof (update_tl2_for_pop _ _ _ _ tl2 _ innerU).
  destruct H as [aa_removed' mii].
  destruct H0 as [[n' [t' tl2']]|H0].
  exists (drop_updated innerU).
  (* pop successful *)
    exists aa_removed'.
    constructor.
    refine ((mii, _)).
    left.
    exists n'.
    exists t'.
    apply tl2'.

    destruct (proofstep_over_subset c p oe ne l mi innerU innerP) as [outerU outerP].
    apply (p_step C K aa_total _ c p oe ne l).
    apply baseproof.
    apply outerU.
    apply outerP.
  (* empty after pop *)
    (* but we were assured that it's not by E : tl_dataΛ n = Some e *)
    rewrite H0 in *.
    exists nil.
    exists aa_removed'.
    constructor.
    refine ((mii, _)).
    right.
    reflexivity.

  destruct (proofstep_over_subset c p oe ne l mi innerU innerP) as [outerU outerP].
  apply (p_step C K aa_total _ c p oe ne l).
  apply baseproof.
  apply outerU.
  apply outerP.
Qed.

Inductive OptionTree (C: nat) (aa: AA) :=
| otsome (n: ThetaLambdaInner) (t : ThetaLambdaTree C n) (tl2 : @TLT2 C aa n t) : OptionTree C aa
| otnone : aa = nil -> OptionTree C aa.

Inductive TreeAndRemovedTasks (C: nat) (aa: AA) :=
| tart
  (aa_tree aa_removed: AA)
  (mi: Interleave aa_tree aa_removed aa)
  (ot: OptionTree C aa_tree)
  : TreeAndRemovedTasks C aa.

Definition tart_fn (C : nat) :=
  forall
    (aa : AA)
    (tr : TreeAndRemovedTasks C aa)
    {K} (baseproof: Proof C K aa),
    { Z : AA & prod (TreeAndRemovedTasks C Z) (Proof C K Z) }.

Definition tart_bind {C} (f1: tart_fn C) (f2: tart_fn C) : tart_fn C.
Proof.
  unfold tart_fn in *.
  intros.
  specialize (f1 aa tr K baseproof).
  clear aa tr baseproof.
  destruct f1 as [aa' [tr' proof']].
  specialize (f2 aa' tr' K proof').
  clear aa' tr' proof'.
  apply f2.
Qed.

(*

(* a rewrite of the above theta_lambda_pop_loop to use TreeAndRemovedTasks instead *)

Fixpoint theta_lambda_pop_loop_v2 (steps: nat)
  (C : nat)
  (aa : AA)
  (tr : TreeAndRemovedTasks C aa)
  {K} (baseproof: Proof C K aa)
:
  TreeAndRemovedTasks C aa * { Z : AA & Proof C K Z }.
Proof.
  set (no_more_changes := (tr, existT _ _ baseproof)).
  destruct steps; [apply no_more_changes|clear steps].
  destruct tr.
  destruct (tl_dataΛ n) as [e|] eqn:E.

  2: destruct (proofstep_by_tl_pop tl2 E) as [[c [p [oe [ne [l [Y [innerU innerP]]]]]]]|].
*)

Definition theta_lambda_pop_loop_wrapped
  (steps: nat)
  (C : nat)
  (aa : AA)
  (tr : TreeAndRemovedTasks C aa)
  {K} (baseproof: Proof C K aa)
:
  { Z : AA & prod (TreeAndRemovedTasks C aa) (Proof C K Z) }.
Proof.
  destruct tr.
  destruct ot.
  pose proof (theta_lambda_pop_loop steps C n t aa_tree aa_removed aa
    tl2 mi baseproof) as H.
  destruct H as [H ZP].
  destruct H as [aa_tree' [aa_removed' [I J]]].
  assert (OptionTree C aa_tree').
  destruct J.
  destruct s as [n' [t' tl2']].
  apply (otsome C aa_tree' n' t' tl2').
  apply (otnone C aa_tree' e).
  destruct ZP as [Z P].
  exists Z.
  constructor.
  apply (tart C aa aa_tree' aa_removed' I H).
  apply P.

  exists aa.
  constructor.
  apply (tart C aa aa_tree aa_removed mi (otnone _ _ e)).
  exact baseproof.
Qed.


Definition theta_lambda_pop_loop_wrapped_x
  (steps: nat)
  (C : nat)
  (aa : AA)
  (tr : TreeAndRemovedTasks C aa)
  {K} (baseproof: Proof C K aa)
:
  { Z : AA & prod (TreeAndRemovedTasks C Z) (Proof C K Z) }.
Proof.
  destruct tr.
  destruct ot.
  pose proof (theta_lambda_pop_loop_x steps C n t aa_tree aa_removed aa
    tl2 mi baseproof) as H.
  destruct H as [aa_total' [aa_tree' [aa_removed' [[I J] P]]]].
  assert (OptionTree C aa_tree').
  destruct J.
  destruct s as [n' [t' tl2']].
  apply (otsome C aa_tree' n' t' tl2').
  apply (otnone C aa_tree' e).

  exists aa_total'.
  constructor.
  apply (tart C _ aa_tree' aa_removed' I H).
  apply P.

  exists aa.
  constructor.
  apply (tart C aa aa_tree aa_removed mi (otnone _ _ e)).
  exact baseproof.
Qed.

(* theta -> lambda *)
Definition tlt2_flip_max_lct {C aa n} (t: ThetaLambdaTree C n)
  (tl: @TLT2 C aa n t) :
  option {n' : ThetaLambdaInner & {t': ThetaLambdaTree C n' &
(@TLT2 C aa n' t') (*
    prod (@TLT2 C aa n' t') (prod
      (ole (tl_tllct))
      (ole (tl_tllct))
    )*)}}.
Proof.
  induction tl.
  apply Some.
  eexists _.
  eexists _.
  apply tlt2_lambda.
  apply None.
  destruct (tl_towards_max_lct (tlt_node C lhs rhs)).
  destruct IHtl1 as [[li' [lhs' lhs2']]|]; [apply Some|apply None].
  set (ni := theta_lambda_combine C li' ri).
  set (node := tlt_node C lhs' rhs).
  exists ni.
  exists node.
  apply (tlt2_node lhs2' tl2).
  apply i.

  (* after the leaf flipped the gap invariant must be upheld *)
  (* currently this is impossible as when two tasks have the *)
  (* same lct and one of them gets flipped, the two times are *)
  (* equal, not one less than the other *)
  (* probably the solution is to flip ALL tasks with the same *)
  (* lct at the same time *)
  admit.

  destruct IHtl2 as [[ri' [rhs' rhs2']]|]; [apply Some|apply None].
  set (ni := theta_lambda_combine C li ri').
  set (node := tlt_node C lhs rhs').
  exists ni.
  exists node.
  apply (tlt2_node tl1 rhs2').
  apply i.
  admit. (* as above *)
Admitted.

Definition theta_lambda_flip
  (C : nat)
  (aa : AA)
  (tr : TreeAndRemovedTasks C aa)
  {K} (baseproof: Proof C K aa)
:
  { Z : AA & prod (TreeAndRemovedTasks C Z) (Proof C K Z) }.
Proof.
  exists aa.
  destruct tr eqn:W.
  destruct ot.
  clear W.
  destruct (tlt2_flip_max_lct t tl2).
  refine ((_, baseproof)).
  destruct s as [n' [t' tl2']].
  apply (tart C aa aa_tree aa_removed mi (otsome C _ _ t' tl2')).
  exact ((tr, baseproof)).
  exact ((tr, baseproof)).
Qed.

Fixpoint theta_lambda_sweep_loop
  (steps_inner: nat)
  (steps: nat)
  (C : nat)
  (aa : AA)
  (tr: TreeAndRemovedTasks C aa)
  {K} (baseproof: Proof C K aa)
:
  { Z : AA & prod (TreeAndRemovedTasks C Z) (Proof C K Z) }.
Proof.
  destruct steps; [exact (existT _ _ (tr, baseproof))|].
  specialize (theta_lambda_sweep_loop steps_inner steps C); clear steps.
  enough (tart_fn C).
  specialize (H aa tr K baseproof).
  apply H.
  refine (tart_bind (theta_lambda_flip C) _).
  refine (tart_bind (theta_lambda_pop_loop_wrapped_x steps_inner C)
    theta_lambda_sweep_loop).
Qed.
