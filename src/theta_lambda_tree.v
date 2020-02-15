
Inductive AbstractTree {A B: Type} (f: A->B) (g: B->B->B) : B -> Type :=
| at_inner {a b} : AbstractTree f g a -> AbstractTree f g b -> AbstractTree f g (g a b)
| at_leaf  (a: A) : AbstractTree f g (f a).

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

Definition ThetaLambdaNode (C: nat) :=
  @AbstractTree
    ThetaLambdaLeaf
    ThetaLambdaInner
    (thetaLambdaInnerFromLeaf C)
    thetaLambdaPropagate.
