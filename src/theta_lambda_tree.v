Require Import Nat.
Require Import definitions.

Record ThetaLambdaInner := mkTLInner {
  tl_eest      : nat;
  tl_energy    : nat;
  tl_energyΛ   : nat * option Activity;
  tl_envelope  : nat;
  tl_envelopeΛ : nat * option Activity;
}.

Inductive ThetaLambdaLeaf :=
| tl_theta : Activity -> ThetaLambdaLeaf
| tl_lambda : Activity -> ThetaLambdaLeaf.

Definition thetaLambdaInnerFromLeaf (C: nat) (l: ThetaLambdaLeaf) :=
  match l with
  | tl_theta  a => mkTLInner (est a) (energy a) ((envelope_unit C a), None) 0 (0, None)
  | tl_lambda a => mkTLInner (est a) 0 (0, None) (energy a) (envelope_unit C a, None)
  end.

Definition rmax {R} (a b: nat*R) :=
  match (a, b) with ((a, ra), (b, rb)) =>
  let m := max a b in
  (m, if m =? a then ra else rb)
  end.

Definition radd1 {R} (a: nat*R) (b: nat) := ((fst a)+b, snd a).
Definition radd2 {R} (a: nat) (b: nat*R) := (a+(fst b), snd b).

Definition thetaLambdaPropagate (a b: ThetaLambdaInner) : ThetaLambdaInner :=
  mkTLInner
    (min (tl_eest a)   (tl_eest b))
    (add (tl_energy a) (tl_energy b))
    (rmax (radd1 (tl_energyΛ a) (tl_energy  b))
          (radd2 (tl_energy  a) (tl_energyΛ b)))
    (max (add (tl_envelope a) (tl_energy  b))
         (tl_envelope b))
    (rmax (tl_envelopeΛ b) (rmax
          (radd1 (tl_envelopeΛ a) (tl_energy  b))
          (radd2 (tl_envelope  a) (tl_energyΛ b))))
.

Inductive AbstractTree {A B: Type} (f: A->B) (g: B->B->B) : B -> Type :=
| at_inner {a b} : AbstractTree f g a -> AbstractTree f g b -> AbstractTree f g (g a b)
| at_leaf  (a: A) : AbstractTree f g (f a).

Inductive Path {A B} {f: A->B} {g: B->B->B} : forall {b}, AbstractTree f g b -> Type :=
| p_left  {bl} (l: AbstractTree f g bl)
          {br} (r: AbstractTree f g br) :
          Path l ->
          Path (at_inner f g l r)
| p_right {bl} (l: AbstractTree f g bl)
          {br} (r: AbstractTree f g br) :
          Path r ->
          Path (at_inner f g l r)
| p_here  {a} :
          Path (at_leaf f g a).

Require Import Coq.Program.Equality.

Fixpoint lookupLeaf {A B: Type} (f: A->B) (g: B->B->B)
    {b: B} {node: AbstractTree f g b} (path: Path node) : A :=
  match path with
  | p_left  l r pl => lookupLeaf f g pl
  | p_right l r pr => lookupLeaf f g pr
  | @p_here _ _ _ _ a => a
  end.

Definition updateLeaf {A B: Type} (f: A->B) (g: B->B->B) (update: A->A)
    {b: B} {node: AbstractTree f g b} (path: Path node) : { b': B & AbstractTree f g b' }.
induction path.
+ exists bl. apply l.
+ exists br. apply r.
+ exists (f (update a)). apply at_leaf.
Defined.

Definition updateLeafRel 
  {A B: Type} (f: A->B) (g: B->B->B) (update: A->A)
  (y x: { b: B & AbstractTree f g b }) :=
    exists (path: Path (projT2 x)), updateLeaf f g update path = y.


Require Import Coq.Init.Wf.

Definition wfFunc
  {A}
  (f: A -> A)
:= {P: A->Prop | @well_founded A (fun a b => P b /\ f b = a)}.

Ltac apply_clear X := apply X; clear X.

(* just make sure wfFunc is sane *)
Theorem wfDec : wfFunc (fun (a: nat) => a-1).
  exists (fun x => x > 0).
  intro.
  induction a; constructor; intros y [precondition rel].
  inversion precondition.
  simpl in rel.
  rewrite PeanoNat.Nat.sub_0_r in rel; subst.
  apply IHa.
Qed.

Theorem updateLeafWellFounded
  {A B: Type} (f: A->B) (g: B->B->B) (update: A->A) (WF: wfFunc update) :
  well_founded (updateLeafRel f g update).
Proof.
  intro.
  destruct a as [xb x].
  constructor.
  intros.
  destruct y as [yb y].
  (* it's tempting to destroy the 'Acc' in the goal here, but not so fast!
     for the final element there -is- no even smaller element.
     in that situation there should be a contradiction in the assumptions. *)
  destruct H as [path HUpdate].
  set (yby := existT (fun b : B => AbstractTree f g b) yb y) in *.
  
  induction path eqn:Z.
  (*
       x    y
      / \
     l   r
  *)
  (* in the first two cases, the path taking the left or right side
     implies that both x and y -have- to be at_inner, not at_leaf.
     demonstrate this by destroying x and y and showing that their
     at_inner cases are infeasible. *)
  (*
  + enough (xb = g bl br). subst xb.
    enough (x = at_inner f g l r). subst x.
    destruct y.
    rewrite <- H. clear H.
    simpl.*)
  + admit.
  + admit.
  + 

Definition ThetaLambdaNode (C: nat) :=
  @AbstractTree
    ThetaLambdaLeaf
    ThetaLambdaInner
    (thetaLambdaInnerFromLeaf C)
    thetaLambdaPropagate.

Definition maxEnvelopeΛPath {C} {b} (node: ThetaLambdaNode C b) : Path node.
  induction node.
  pose (fst (tl_envelopeΛ b) <? fst (tl_envelopeΛ a)).
  destruct b0 eqn:Z.
  apply p_left.
  apply IHnode1.
  apply p_right.
  apply IHnode2.
  apply p_here.
Qed.
