Require Import List PeanoNat.
Require Import Nat Bool.
Require Import misc.
Require Import definitions.
Require Import assignments.
Require Import edge_finding.

Axiom sorted : forall {A} (key: A->nat) (l: list A), list A.

Definition dummyActivity : Activity.
Proof.
  refine (mkActivity 0 0 0 0).
Qed.
(*
  refine (mkActivity 0 0 0 0 _).
  intuition.
Defined.*)

Definition ends_before_x (C: nat) (aa: list Activity) (end_a b: nat) :=
  forall
    (LB: b < length aa)
    (starts: list nat)
    (LSLA: length aa = length starts)
    (SB := eq_ind
      (length aa)
      (fun (limit: nat) => b < limit)
      LB
      _
      LSLA),
    let assignment := combine aa starts in
    aa_valid assignment ->
    aa_fit C assignment ->
    let end_b := nthi b starts SB + (a_p (nth b aa dummyActivity)) in
    end_a < end_b.

(* when to a group
    |---------aa---------|
   adding a task
        |-----s------|
   that doesn't bump lct, then not fitting in the range
    |est{s,aa}----lct{aa}|
   is the same as, not fitting in the range
    |est{s,aa}--lct{s,aa}|
   also known as
    unassignableByEnergy C (s:aa)
*)

Theorem fe (C: nat) (s: Activity) (aa: list Activity) :
  lct s <= lct aa ->
  ((lct aa) - (est (cons s aa))) * C < energy (cons s aa) ->
  unassignableByEnergy C (cons s aa).
Proof.
  intro.
  replace (lct aa) with (lct (cons s aa)).
  auto.
  simpl.
  unfold mapfold.
  simpl.
  rewrite Nat.max_r.
  reflexivity.
  auto.
Qed.


(*
  .---------.      .-------....
  |         |      | aa[*] |  :
 est sa[*] lct  <  |    .--'----.
  |         |      |    | aa[b] |
  '---------'      '----'-------'
                ->

*)

(*
Theorem ends_before_x_th (C: nat) (aa: list Activity) (end_a b: nat) :
  forall (sa: list Activity),
    ((lct sa) - (est sa)) * C < energy (nth b aa dummyActivity) + energy aa ->
    ends_before_x C aa end_a b.
Proof.
  intros.
  intro.
  intros.
  pose proof (aa_fit_weak_easy C assignment H3 (range (est sa) (lct sa))).
  assert (end_b <= end_a -> False).
  intro.

  unfold aa_fit_weak in H4.
  rewrite length_range in H4.
  rewrite (aa_uses_between_est_lct_is_energy assignment) in H4.
*)

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

Definition LCut (aa: list Activity) (plct: nat) :=
  filter (fun a => lct a <=? plct) aa.

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

(* Definition envelope_exists (C: nat) (aa: list Activity) :=
  { subset: list Activity |
    (*subset is a subset of aa and*)
    C * (est subset) + (energy subset) = envelope aa }. *)

(*Definition edgeFindingOne' :=
  forall (C: nat) (aa: list Activity) (plct: nat) (b: nat),
    let ba := nth b aa dummyActivity in
    b < length aa ->
    plct < lct ba ->
    envelope C (cons ba (LCut aa plct)) > C * plct ->
    ends_before C aa a b.*)

(*
   for concrete assignments:
     aa_fit:      for each time, usage is below the limit
     aa_uses:     for list of given times, the sum of usages
     aa_fit_weak: for list of given times, the sum of usages is below sum oflimits

   relating concrete assignments and static measures:
     transpose_aa_uses: aa_uses = energy
*)

Check aa_uses_between_est_lct_is_energy. 
  (* : forall aa : list (Activity * nat),
       aa_uses aa (range (est aa) (lct aa)) = energy aa *)
Check fe.
  (* : forall (C : nat) (s : Activity) (aa : list Activity),
       lct s <= lct aa ->
       (lct aa - est (s :: aa)) * C < energy (s :: aa) ->
       unassignableByEnergy C (s :: aa) *)


(*Definition detection_phase (C: nat) (a: list Activity) : list nat :=
  let by_uest := sorted est a in
  let by_lct := sorted est a in
  let tree := mk_theta_lambda_tree (sorted est a) in *)

(*
def edge_finding(tasks):
	prec = {}
	tasks.sort(key=lambda task: task.est)
	order = {x: i for i, x in enumerate(tasks)}
	atree = AbstractTree(len(tasks))
	numΛ = 0
	nodes = [None] * (atree.root+1)

	def assign_leaf(i, inΛ):
		nonlocal numΛ
		nodes[i] = NodeRhoLambda.leaf((tasks[i], inΛ))
		atree.rebuild(nodes, i, NodeRhoLambda.node)

	for i in range(len(tasks)):
		assign_leaf(i, False)

	for task in sorted(tasks, key=lambda task: -task.lct):

		while numΛ:
			root = nodes[atree.root]
			nvlp, ntask = root.nvlp2, root.nvlp2res

			if nvlp <= C * task.lct: break

			prec[ntask] = task.lct
			atree.remove_leaf(order[ntask])
			numΛ -= 1

		assign_leaf(order[task], True)
		numΛ += 1

	return prec
*)

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

Axiom unique_nats : forall (i: list nat), list nat.

Axiom nvlp : forall (r: ThetaTree), nat.
Axiom nrg : forall (r: ThetaTree), nat.


Axiom div_ceil : forall (a: nat) (b: nat), nat.

Definition adjustment_phase_iteration
  (C: nat)
  (c: nat)
  (task: Activity)
  (Θ: ThetaTree)
:
  nat
:=
	let maxest := eval_maxest C (lct task) c Θ in
	let (α, β) := split_at Θ maxest in
	let Envjc  := nvlp α + (if β then nrg β else 0) in
	let diff   := div_ceil (Envjc - (C-c)*lct task) c in
  diff.

Axiom empty_tree : ThetaTree.

Definition tmap {A B} (i: list A) (f: A->B) : list B := map f i.

Definition adjustment_phase (C: nat) (aa: list Activity)
  : list (nat * (list (Activity * nat)))
:=
  tmap (unique_nats (map a_c aa)) (fun c => (c,
    let Θinitial        := empty_tree in
    let upd_initial     := 0 in
    let updates_initial := nil in 
    match fold_left (fun (state: ThetaTree*nat*(list (Activity*nat))) task =>
      match state with | (Θ, upd, updates) =>
      let Θ2    := tree_insert Θ task in
      let diff  := adjustment_phase_iteration C c task Θ2 in
			let upd2  := max upd diff in
      let updates2 := (cons (task, upd2) updates) in
      (Θ2, upd2, updates2)
      end
    ) (sorted lct aa) (Θinitial, upd_initial, updates_initial)
    with (Θfinal, _, updates_final) => updates_final end
  )).

Definition apply_update (C: nat) (aa: list Activity)
  (prec: list nat) (updates: list (nat * (list (Activity * nat))))
:
  list Activity
:=
  let updates_for_c (c: nat) :=
    flat_map snd (filter (fun update_group => c =? (fst update_group)) updates) in

  let updates_for_c_lct (c: nat) (lct: nat) :=
    map snd (filter (fun update_entry => lct =? (a_lct (fst update_entry)))
      (updates_for_c c)) in

  fold_left (fun p a =>
    let old_est := a_est a in
    let new_est := fold_left max (updates_for_c_lct
      (a_c a)
      (a_lct a)) old_est in
    let updated_activity : Activity := mkActivity
      new_est
      (a_lct a)
      (a_c a)
      (a_p a)
    in
    (cons updated_activity p)
  ) aa nil.

Definition edge_filtering_for_cumulative_resources
  (C: nat)
  (a: list Activity)
:=
  let prec   := detection_phase C a in
  let update := adjustment_phase C a in
  apply_update C a prec update.

Theorem edge_filtering_for_cumulative_resources_sound :
  forall (C: nat) (a: list Activity),
    equallyAssignable C a (edge_filtering_for_cumulative_resources C a).
Proof.
  intros.
  unfold edge_filtering_for_cumulative_resources.
  unfold apply_update.
  unfold equallyAssignable.
  intros.
  constructor; auto.
Qed.

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