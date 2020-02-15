from pprint import pprint
import math
import sys

# Edge Finding Filtering Algorithm for Discrete Cumulative Resources in O(kn log n)
#  by Petr Vilı́m
#
# 2. Basic Notation
#    C                   total capacity
#    T = {...}           the set of activities(/tasks)
#    est i               earliest completion time of activity i
#    lct i               latest completion time of activity i
#    c i                 capacity required by activity i
#    p i                 time taken by activity i
#
#    e i = (c i)*(p i)   "energy" of activity i
#
#    k = |{c i, i ∈ T}|  distinct capacity requirements
#                        relevant for the O(k·n log n) runtime
#
#    for activities i,
#      c i ≤ C
#      est i + p i ≤ lct i
#      
#    for sets of activities Ω ⊆ T,
#      est Ω = min {est i, i ∈ Ω}
#      lct Ω = max {lct i, i ∈ Ω}
#      e   Ω = sum {e i, i ∈ Ω}
#       CAN Ω BE THE EMPTY SET?
#
# 3. Earliest completion time
#    Ect(Θ) = ⌈Env(Θ)/C⌉  
#    Env(Θ) = max {C est Ω + e Ω, Ω ⊆ Θ}
#       CAN Ω BE THE EMPTY SET?
#       CAN Θ BE THE EMPTY SET?
#
# 3.1 Cumulative Θ Tree
#    The leafs correspond to the activities sorted by est.
#    Nodes v, have two attributes e, and Env representing:
#      e   v = e   (Leaves v)
#      Env v = Env (Leaves v)
#
#    For leaf nodes v, containing only i
#      e   v = e   (Leaves v) = e   {i} = e i
#      Env v = Env (Leaves v) = Env {i} = e i + C·est i
#    For inner nodes v,
#      e   v = e (left v) + e (right v)
#      Env v = max(
#        Env (left v) + e (right v)
#        Env (rigth v)
#      )
#
# 4. Relation "Ends before End"
#    ∀ Ω ⊂ T, i ∈ T\Ω, (Ω <: i) ⇔ (∀j ∈ Ω, j <: i)
#
#    Example:
#      {a, b, c} <: x  (for x not in {a, b, c})
#        <->
#      a <: x and
#      b <: x and
#      c <: x
#
# 5. Edge finding
#    LCut(T, j) = {l, l ∈ T & lct l ≤ lct j}
#
#    ∀ j ∈ T, i ∈ T \ LCut (T,j),
#      Ect (LCut (T, j) ∪ {i}) > lct j
#        ⇒ LCut (T, j) <: i
#
#    The set LCut(T, j) must be processed before lct j. So
#    if there is not enough time to process i together with
#    LCut(T, j) then the activity i must end after LCut(T, j).
#
#    ∀ j ∈ T, i ∈ T \ LCut (T, j),
#      Env (LCut (T, j) ∪ {i}) > C lct j
#        ⇒ LCut(T, j) <: i
#
# 6. Detection Algorithm
#
# 6.1 Computation of Env (Θ, Λ)
#
# 6.2 Improving Detection
#
# 7. Time bound adjustment
#    maxest(j, c) = max {est Ω , Ω ⊆ LCut (T, j) & e Ω > (C − c)(lct j − est Ω )}
#


# <: is meant to be ⋖  but Sublime Text won't render it for me currently

# todo: whereever it says "ref" and the result doesn't match

mode = len(sys.argv) >= 2 and sys.argv[1] == "new"

class Task:
	def __init__(self, est, lct, p, c):
		self.est = est
		self.lct = lct
		self.p = p
		self.c = c
		self.letter = ""

	def __repr__(self):
		return "Task{}({}-{}-{})*{}".format(self.letter, self.est, self.p, self.lct, self.c)
		return self.__class__.__name__ + repr(vars(self))

def maxnone(*args):
	args = [arg for arg in args if arg is not None]
	if len(args) == 0: return None
	if len(args) == 1: return args[0]
	return max(*args)

def sumnone(*args):
	if None in args:
		# anything plus minus infinity is minus infinity
		return None
	return sum(args)

class AbstractTree:
	def __init__(self, n):
		self.n = n
		self.parent = [None]*n
		self.child1 = [None]*n
		self.child2 = [None]*n
		elem = list(range(n))
		k = n
		while len(elem) > 1:
			nelem = []
			for a, b in zip(elem[::2], elem[1::2]):
				self.parent[a] = k
				self.parent[b] = k
				self.parent.append(None)
				self.child1.append(a)
				self.child2.append(b)
				nelem.append(k)
				k += 1
			if len(elem) % 2 == 1:
				nelem.append(elem[-1])
			elem = nelem

		self.root = k-1
		#print("AbstractTree.__init__: parent, child1, child2")
		#pprint(self.parent)
		#pprint(self.child1)
		#pprint(self.child2)

	def rebuild(self, nodes, x, mknode):
		if x == self.root:
			return
		x = self.parent[x]
		while True:
			nodes[x] = mknode(nodes[self.child1[x]], nodes[self.child2[x]])
			if x == self.root: return
			x = self.parent[x]


	def remove_leaf(self, x):
		if x == self.root:
			self.root = None
			return

		p = self.parent[x]
		self.parent[x] = None
		assert p is not None

		xy = {self.child1[p], self.child2[p]}
		y, = xy - {x}

		if p == self.root:
			self.parent[y] = None
			self.root = y
			return

		pp = self.parent[p]
		self.parent[p] = None
		self.child1[p] = None
		self.child2[p] = None

		self.parent[y] = pp
		if self.child1[pp] == p: self.child1[pp] = y
		if self.child2[pp] == p: self.child2[pp] = y

class NodeThetaLambda:

	def pprint(self, i=""):
		if self.inner:
			print(i+"Node(eest={}, e={}, E={}, e'={}, E'={})".format(
				self.eest, self.nrg, self.nvlp, self.nrg2, self.nvlp2))
			if self.lhs: self.lhs.pprint(i+"    ")
			if self.rhs: self.rhs.pprint(i+"    ")
		else:
			print(i+repr(self))

	def __repr__(self):
		if self.inner:
			return "Node(eest={}, e={}, E={}, e'={}, E'={})({}{}{}, {}{}{})".format(
				self.eest,
				self.nrg, self.nvlp, self.nrg2, self.nvlp2,
				"e=>" if self.nrg2res == self.lhs.nrg2res else "", "E=>" if self.nvlp2res == self.lhs.nvlp2res else "", self.lhs,
				"e=>" if self.nrg2res == self.rhs.nrg2res else "", "E=>" if self.nvlp2res == self.rhs.nvlp2res else "", self.rhs)
		else:
			return "Leaf(eest={}, e={}, E={}, e'={}, E'={})".format(
				self.eest,
				self.nrg, self.nvlp, self.nrg2, self.nvlp2)

	@staticmethod
	def node(lhs, rhs):
		if not rhs: return lhs
		if not lhs: return rhs
		n = NodeThetaLambda()
		n.lhs = lhs
		n.rhs = rhs
		n.inner = True
		n.eest = min(lhs.eest, rhs.eest)

		# e    = nrg
		# e^   = nrg2
		# Env  = nvlp
		# Env^ = nvlp2

		n.nrg  = lhs.nrg + rhs.nrg
		n.nrg2 = maxnone(
			sumnone(lhs.nrg2, rhs.nrg),
			sumnone(lhs.nrg,  rhs.nrg2))
		n.nvlp  = maxnone(
			sumnone(lhs.nvlp,  rhs.nrg),
			rhs.nvlp)
		n.nvlp2 = maxnone(
			sumnone(lhs.nvlp2, rhs.nrg),
			rhs.nvlp2,
			sumnone(lhs.nvlp, rhs.nrg2))

		if n.nrg2 == sumnone(lhs.nrg2, rhs.nrg):
			n.nrg2res = lhs.nrg2res
		else:
			n.nrg2res = rhs.nrg2res

		if n.nvlp2 == sumnone(lhs.nvlp2, rhs.nrg):
			n.nvlp2res = lhs.nvlp2res
		elif n.nvlp2 == rhs.nvlp2:
			n.nvlp2res = rhs.nvlp2res
		else:
			n.nvlp2res = rhs.nrg2res

		return n

	@staticmethod
	def leaf(desc):
		task, group = desc
		nrg = task.p * task.c
		nvlp = C * task.est  + nrg

		n = NodeThetaLambda()
		n.eest = task.est
		n.inner = False
		n.nrg2res = task
		n.nvlp2res = task

		if group == 0: # theta
			n.nrg = nrg
			n.nvlp = nvlp
			n.nrg2 = None
			n.nvlp2 = None

		else: # lambda
			n.nrg = 0
			n.nvlp = None
			n.nrg2 = nrg
			n.nvlp2 = nvlp

		return n

class NodeTheta:
	def __repr__(self):
		if self.inner:
			return "Node(eest={}, e={}, E={}, Ec={})({}, {})".format(
				self.eest, self.nrg, self.nvlp, self.nvlpc, self.lhs, self.rhs)
		else:
			return "Leaf(eest={}, e={}, E={}, Ec={})".format(
				self.eest, self.nrg, self.nvlp, self.nvlpc)

	@staticmethod
	def node(lhs, rhs):
		if not rhs: return lhs
		if not lhs: return rhs
		n = NodeTheta()
		n.inner = True
		n.lhs = lhs
		n.rhs = rhs
		n.leaf = False
		n.eest = min(lhs.eest, rhs.eest)

		n.nrg = lhs.nrg + rhs.nrg
		n.nvlp = max(lhs.nvlp + rhs.nrg, rhs.nvlp)
		n.nvlpc = max(lhs.nvlpc + rhs.nrg, rhs.nvlpc)
		return n

	@staticmethod
	def leaf(task, c=None):
		n = NodeTheta()
		n._task = task
		n.inner = False
		n.eest = task.est
		n.nrg = task.p * task.c
		n.nvlp = C * task.est + n.nrg
		if c is None: c = C
		n.nvlpc = (C-c) * task.est + n.nrg
		return n

	def split_along_est(self, est):
		if self.leaf:
			if self.eest <= est:
				return self, None
			else:
				return None, self
		else:
			if self.eest <= est:
				if self.rhs.eest <= est:
					rl, rr = self.rhs.split_along_est(est)
					return NodeTheta.node(self.lhs, rl), rr
				else:
					ll, lr = self.lhs.split_along_est(est)
					return ll, NodeTheta.node(lr, self.rhs)
			else:
				return None, self


def build_tree(NodeClass, tasks, c=None):
	if len(tasks) == 0:
		return None
	if c is None:
		nodes = [NodeClass.leaf(task) for task in tasks]
	else:
		nodes = [NodeClass.leaf(task, c) for task in tasks]
	while len(nodes) > 1:
		nodes2 = [NodeClass.node(a, b) for a, b in zip(nodes[::2], nodes[1::2])]
		if len(nodes) % 2 == 1:
			nodes2.append(nodes[-1])
		nodes = nodes2
	return nodes[0]

def leaf_prefixes(tree):
	def flatten(node):
		if node.leaf:
			yield node
		else:
			yield from flatten(node.lhs)
			yield from flatten(node.rhs)
	leafs = [leaf._task for leaf in flatten(tree)]
	for i in range(len(leafs)):
		yield leafs[:i+1]

def subsets_of(s, p=set()):
	if isinstance(s, set):
		s = list(s)
	if len(s) == 0:
		yield p
	else:
		yield from subsets_of(s[1:], p)
		yield from subsets_of(s[1:], p | {s[0]})

def est_set(tasks): return min(task.est for task in tasks)
def lct_set(tasks): return max(task.lct for task in tasks)
def nrg_set(tasks): return sum(task.p * task.c for task in tasks)
def nrg_nvlp(tasks):
	return max(
		C * est_set(subtasks) + nrg_set(subtasks)
		for subtasks in subsets_of(tasks) if len(subtasks))

def edge_finding_nsquare(tasks, prec):
	Θ = set(tasks)
	Λ = set()
	for task in sorted(tasks, key=lambda task: -task.lct):
		while len(Λ):
			nvlp, ntask, tree = eval_nrg_nvlp(Θ, Λ) # TODO: don't rebuild tree
			yield nvlp, ntask, tree
			assert ntask in Λ, (ntask, Λ)
			if nvlp <= C * task.lct: break
			prec[ntask] = task.lct
			Λ.discard(ntask) # remove a leaf and propagate up
		Θ.discard(task)      # recategorize a leaf and propagate up
		Λ.add(task)          # recategorize a leaf and propagate up

def edge_finding_nlogn(tasks, prec):
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
			nvlp, ntask = eval_nrg_nvlp2(nodes, atree)

			yield nvlp, ntask, nodes[atree.root]
			if nvlp <= C * task.lct: break

			prec[ntask] = task.lct
			atree.remove_leaf(order[ntask])
			numΛ -= 1

		assign_leaf(order[task], True)
		numΛ += 1

def edge_finding(tasks):
	tasks.sort(key=lambda task: task.est)
	prec1 = {}
	prec2 = {}
	gen1 = edge_finding_nsquare(tasks, prec1)
	gen2 = edge_finding_nlogn(tasks, prec2)
	for (nvlp1, ntask1, tree1), (nvlp2, ntask2, tree2) in zip(gen1, gen2):
		# print((nvlp1, ntask1), (nvlp2, ntask2))
		# tree1.pprint("")
		# tree2.pprint("")
		assert nvlp1 == nvlp2
		assert ntask1 == ntask2

	assert prec1 == prec2
	return prec2

def eval_nrg_nvlp(Θ, Λ):
	#print("len(Θ) =", len(Θ))
	#print("len(Λ) =", len(Λ))
	leaftasks = [(task, 0) for task in Θ] + [(task, 1) for task in Λ]
	leaftasks.sort(key=lambda task: task[0].est)
	#pprint(leaftasks)
	root = build_tree(NodeThetaLambda, leaftasks)
	#print("tree =", root)
	return root.nvlp2, root.nvlp2res, root

def eval_nrg_nvlp2(nodes, atree):
	root = nodes[atree.root]
	return root.nvlp2, root.nvlp2res

def nvlp_for_c_div_c(Ω, c, lct):
	block = (C - c) * (lct - est_set(Ω))
	surpasser = nrg_set(Ω)
	surpasses = surpasser - block
	print("           nvlp_for_c_div_c({}:{}:{}, lctx={}, c={}) (block={}*{}={}, surpasser_energy={} (+{} ~ {}t)".format(
		est_set(Ω), repr_taskset(Ω), lct_set(Ω),
		lct, c, (C-c), (lct - est_set(Ω)), block, surpasser, surpasses, math.ceil(surpasses/c)))
	return est_set(Ω) + math.ceil(
		(nrg_set(Ω) - (C - c) * (lct - est_set(Ω))) / c
	)

def nvlp_for_c(tasks, c):
	return max(
		(C-c) * est_set(subtasks) + nrg_set(subtasks)
		for subtasks in subsets_of(tasks) if len(subtasks) > 0)

def repr_taskset(ts):
	return "{"+"".join(t.letter for t in ts)+"}"

def energy_filter(tasks, lct, c, f, ref_update_mode=0, when_empty=0):
	lcut = {task for task in tasks if task.lct <= lct}
	print("         lcut({}, lct={}) = {}".format(repr_taskset(tasks), lct, lcut))
	mc = [Ω
		for Ω in subsets_of(lcut)
		if len(Ω)
		if nrg_set(Ω) > (C - c) * ((lct_set(Ω) if ref_update_mode else lct) - est_set(Ω))]

	if mc:
		fs = [f(Ω) for Ω in mc]
		print("         ", *("{}({}: e{}>sq{}={}*{})".format(
			repr_taskset(Ω),
			fo,
			nrg_set(Ω),
			(C - c) * (lct_set(Ω) - est_set(Ω)),
			(C - c), (lct_set(Ω) - est_set(Ω))
		) for fo, Ω in zip(fs, mc)))
		return max(fs)
	else:
		return when_empty

def maxest_filter(tasks, lct, c, f): #unused yet
	lcut = {task for task in tasks if task.lct <= lct}
	maxest_ = maxest(tasks, lct, c)
	mc = [Ω
		for Ω in subsets_of(lcut)
		if len(Ω)
		if est_set(Ω) <= maxest_]
	try:
		fs = [f(Ω) for Ω in mc]
		print("         ", *("{}({})".format(
			repr_taskset(Ω),
			fo,
		) for fo, Ω in zip(fs, mc)))
		return max(fs)
	except ValueError:
		return 0

def ref_update(tasks, lct, c):
	return energy_filter(tasks, lct, c, lambda Ω:
		nvlp_for_c_div_c(Ω, c, lct_set(Ω)), 1, None)

def diff1(tasks, lct, c):
	return energy_filter(tasks, lct, c, lambda Ω:
		nvlp_for_c_div_c(Ω, c, lct), 0, None)

def maxest(tasks, lct, c):
	print("        ref_maxest(lct={}, c={}) = ...".format(lct, c))
	r = energy_filter(tasks, lct, c, lambda Ω:
		est_set(Ω), 0)
	print("        ref_maxest(lct={}, c={}) = {}".format(lct, c, r))
	return r

def diff2(tasks, lct, c): #unused yet
	return maxest_filter(tasks, lct, c, lambda Ω:
		nvlp_for_c_div_c(Ω, c, lct))

def nrg_nvlp2(tasks):
	return energy_filter(tasks, lct, c, lambda Ω:
		C * est_set(subtasks) + nrg_nvlp(subtasks), 0)

# def diff3(tasks, lct, c):
# 	return math.ceil(
# 		(nrg_nvlp(lct, c) - (C-c)*lct) / c
# 	)

def eval_maxest(Θ, task_lct, c, root):
	node = root
	E = 0
	while node.inner:
		print("        eval_maxest(lctj={}, c={}) %".format(task_lct, c), node)
		if node.rhs.nvlpc + E > (C-c) * task_lct:
			print("          Env[{}](={}) + E(={}) >  {}*{}".format(c, node.rhs.nvlpc, E, C-c, task_lct))
			node = node.rhs
		else:
			print("          Env[{}](={}) + E(={}) <= {}*{}".format(c, node.rhs.nvlpc, E, C-c, task_lct))
			E = E+node.rhs.nrg
			node = node.lhs

	print("        eval_maxest(lctj={}, c={}) !".format(task_lct, c), node)
	return node.eest

def compute_update(tasks, prec):
	update = {}
	for c in {task.c for task in tasks}:
		print("compute_update(c={}) # {} tasks".format(c, len(tasks)))
		Θ = set()
		upd = None
		diff_history = []
		for task in sorted(tasks, key=lambda task: task.lct):
			print("   ", task.letter, "Θ=", repr_taskset(Θ))
			print("    :", task, "Θ=", Θ)
			Θ.add(task)
			Θcopy = sorted(Θ, key=lambda task: task.est)
			root = build_tree(NodeTheta, Θcopy, c)
			for prefix in leaf_prefixes(root):
				print("        ref [{}] Env={}, Env[{}]={}".format(repr_taskset(prefix), nrg_nvlp(prefix), c, nvlp_for_c(prefix, c)))
			print()
			maxest_ = eval_maxest(Θ, task.lct, c, root)
			print()
			maxest__ = maxest(Θcopy, task.lct, c)
			print()
			α, β = root.split_along_est(maxest__)
			assert β is None or (β.nvlpc <= (C-c) * task.lct)
			print("        root =", root)
			print("        maxest =", maxest_, "ref =", maxest__)
			assert maxest_ == maxest__
			print("        α =", α)
			print("        β =", β)
			Envjc = α.nvlp + (β.nrg if β else 0)
			diff = math.ceil((Envjc - (C-c)*task.lct) / c)
			print("        α.nvlp+β.nrg-{}*lct = {} - {}*{}; …/{} = {}".format(C-c, Envjc, C-c, task.lct, c, diff))
			print()
			print("        diff1 lct=", task.lct)
			diff1_ = diff1(Θcopy, task.lct, c)
			assert diff1_ is None or diff == diff1_, (diff, diff1_)
			print()
			print("        diff2 lct=", task.lct)
			diff2_ = diff2(Θcopy, task.lct, c)
			assert diff == diff2_, (diff, diff2_)
			print()
			upd = maxnone(diff, upd)
			update[task, c] = upd
			print("        ref_update lct=", task.lct)
			upd_ref = ref_update(Θcopy, task.lct, c)
			print("        previously", diff_history, "now", (diff, upd, upd_ref))
			print("        update[{}, c={}] = {} (diff={}/{}/{}, ref={})".format(
				task.letter, c, upd, diff, diff1_, diff2_, upd_ref))
			assert upd_ref is None or upd == upd_ref
			print()
			diff_history.append((diff, upd))

	return update

# prec [i] := lct j ; // means: LCut(T, j) ⋖ i

def apply_update(tasks, update, prec):
	for i, j_lct in prec.items():
		print("apply update for", prec_line(tasks, i, j_lct), "(c={})".format(i.c))
		b = i.est
		for j in tasks:
			if j.lct == j_lct:
				#print(j, i.c, i)
				#i.est = maxnone(update.get((j, i.c), None), i.est)
				print("   [{}, c={}]: {}".format(j.letter, i.c, update[j, i.c]))
				i.est = maxnone(update[j, i.c], i.est)
		if i.est != b:
			print("  {}.est = {} (from {})".format(i, i.est, b))

example_figure_1 = [
	Task(0, 5, 1, 3),
	Task(2, 5, 3, 1),
	Task(2, 5, 2, 2),
	Task(0, 10, 3, 2)
]

for task, letter in zip(example_figure_1, "ABCD"):
	task.letter = letter

example_figure_5 = [
	Task(0, 7, 2, 1),
	Task(0, 7, 6, 1),
	Task(6, 7, 1, 1),
	Task(0, 10, 6, 1)
]

for task, letter in zip(example_figure_5, "WXYZ"):
	task.letter = letter

#C, tasks = 3, example_figure_1
C, tasks = 2, example_figure_5

def prec_line(tasks, i, j_lct):
	lhs_set = sorted(task.letter for task in tasks if task.lct <= j_lct)
	return "{"+",".join(lhs_set)+"} ⋖ " + i.letter

def print_prec(tasks, prec):
	for i, j_lct in prec.items():
		print(" ", prec_line(tasks, i, j_lct))
	pprint(prec)
	print()

print("C =", C)
prec = edge_finding(tasks)
print("prec1=")
print_prec(tasks, prec)
prec = {task: max(p, task.est + task.p) for task, p in prec.items()}
print("prec2=")
print_prec(tasks, prec)

update = compute_update(tasks, prec)

print("\nupdate=")
pprint(update)
print("\nbefore")
pprint(tasks)

apply_update(tasks, update, prec)

print("\nafter")
pprint(tasks)
