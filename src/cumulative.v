Require Import List PeanoNat.
Require Import Nat Bool.
Require Import misc.
Require Import definitions.
Require Import assignments.
Require Import edge_finding.
Require Import theta_tree.

Axiom sorted : forall {A} (key: A->nat) (l: list A), list A.

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
    let end_b := nthi b starts SB + (a_p (nthi b aa LB)) in
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


(*Definition detection_phase (C: nat) (a: list Activity) : list nat.
Admitted.*)

Definition detection_phase (C: nat) (a: list Activity) : list nat :=
  let by_uest := sorted est a in
  let by_lct := sorted est a in
  let tree := mk_theta_lambda_tree (sorted est a) in

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
		nodes[i] = NodeThetaLambda.leaf((tasks[i], inΛ))
		atree.rebuild(nodes, i, NodeThetaLambda.node)

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
Admitted.
