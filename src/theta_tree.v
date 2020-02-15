Require Import definitions.
Require Import Nat.

Inductive SomeKindaTree : Type :=
| t_inner (eest: nat) (energy: nat) (nvlpc: nat)
          (lhs: SomeKindaTree) (rhs: SomeKindaTree) : SomeKindaTree
| t_leaf (energy: nat) (nvlpc: nat) : SomeKindaTree.

Definition ThetaTree := SomeKindaTree.
Axiom tree_insert : forall (t: ThetaTree) (n: Activity), ThetaTree.

Axiom split_at : forall (node: SomeKindaTree) (est_split: nat),
  (SomeKindaTree * SomeKindaTree).

Definition tree_energy (node: SomeKindaTree) := match node with
| t_inner _ energy _ _ _ => energy
| t_leaf energy _ => energy
end.

Definition nvlpc (node: SomeKindaTree) := match node with
| t_inner _ _ nvlpc _ _ => nvlpc
| t_leaf _ nvlpc => nvlpc
end.

Fixpoint eval_maxest_i
  (task_lct: nat)
  (C_c: nat)
  (E: nat)
  (node: SomeKindaTree)
:
  nat
:=
  match node with
  | t_leaf eest _ => eest
  | t_inner eest _ _ lhs rhs =>
    if (C_c) * task_lct <? nvlpc rhs + E then
      eval_maxest_i task_lct C_c E rhs
    else
      eval_maxest_i task_lct C_c (E+tree_energy rhs) lhs
  end.

Definition eval_maxest (C: nat) (c: nat) (task_lct: nat) (root: SomeKindaTree) :=
  eval_maxest_i task_lct (C-c) 0 root.

(*

Definition isMaxOfFunctionOverType
    {A: Type} (p : A -> Prop) (f: A -> nat) (max: nat) : Prop :=
  (forall (a: A), p a -> f a <= max) /\ (exists (a: A), p a /\ f a = max).

Inductive SortedTree (A: Type) (rel: A -> A -> Prop) : list A -> A -> Type :=
| o_leaf (a: A) : SortedTree A rel (cons a nil) a
| o_node {ll lr} {l r} (lhs: SortedTree A rel ll l) (rhs: SortedTree A rel lr r) :
  rel l r -> SortedTree A rel (ll++lr) l.

Definition est_le {A} `{Work A} (a b: A) := (est a) <= (est b).

Definition ThetaTree := SortedTree Activity est_le.

Fixpoint theta_tree_energy {l a} (t: ThetaTree l a) : nat := match t with
| o_leaf _ _ activity => est activity
| o_node _ _ lhs rhs related => (theta_tree_energy lhs) + (theta_tree_energy rhs)
end.

Fixpoint theta_tree_envelope {l a} (C: nat) (t: ThetaTree l a) : nat := match t with
| o_leaf _ _ activity => (est activity) * C + (energy activity)
| o_node _ _ lhs rhs related =>
    max
    (theta_tree_envelope C lhs + theta_tree_energy rhs)
    (theta_tree_envelope C rhs)
end.

Definition envelope_op (C: nat) (energy_a envelope_a energy_b envelope_b) :=
  (energy_a + energy_b, max (envelope_a + energy_a) envelope_b).

*)