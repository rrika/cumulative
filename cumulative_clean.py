import math
import typing

# an implementation of 
#  Edge Finding Filtering Algorithm for Discrete Cumulative Resources in O(kn log n)
#    by Petr Vilı́m

# TODO: make this truly O(n log n) by addressing the tree
#       rebuild in every iteration in compute_update,

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

	@staticmethod
	def node(lhs, rhs):
		# type: (NodeThetaLambda, NodeThetaLambda) -> NodeThetaLambda
		if not rhs: return lhs
		if not lhs: return rhs
		n = NodeThetaLambda()
		n.lhs = lhs
		n.rhs = rhs
		n.inner = True
		n.eest = min(lhs.eest, rhs.eest)

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

		if group == 0: # rho
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
	@staticmethod
	def node(lhs, rhs):
		if not rhs: return lhs
		if not lhs: return rhs
		n = NodeTheta()
		n.inner = True
		n.lhs = lhs
		n.rhs = rhs
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

def eval_maxest(task_lct, c, root):
	node = root
	E = 0
	while node.inner:
		if node.rhs.nvlpc + E > (C-c) * task_lct:
			node = node.rhs
		else:
			E = E+node.rhs.nrg
			node = node.lhs

	return node.eest

def compute_update(tasks):
	update = {}
	for c in {task.c for task in tasks}:
		Θ = set()
		upd = None
		for task in sorted(tasks, key=lambda task: task.lct):
			Θ.add(task)
			Θcopy   = sorted(Θ, key=lambda task: task.est)
			root    = build_tree(NodeTheta, Θcopy, c) # TODO: this is n log n, instead of log n
			maxest_ = eval_maxest(task.lct, c, root)
			α, β    = root.split_along_est(maxest_)
			Envjc   = α.nvlp + (β.nrg if β else 0)
			diff    = math.ceil((Envjc - (C-c)*task.lct) / c)
			upd     = maxnone(diff, upd)
			update[task, c] = upd

	return update

def apply_update(tasks, update, prec):
	for i, j_lct in prec.items():
		b = i.est
		for j in tasks:
			if j.lct == j_lct:
				i.est = maxnone(update[j, i.c], i.est)

def cumulative(tasks: typing.List[Task]):
	prec = edge_finding(tasks)
	prec = {task: max(p, task.est + task.p) for task, p in prec.items()}
	update = compute_update(tasks)
	apply_update(tasks, update, prec)

def main():
	global C

	example_figure_1 = [
		Task(0, 5, 1, 3),
		Task(2, 5, 3, 1),
		Task(2, 5, 2, 2),
		Task(0, 10, 3, 2)
	]

	for task, letter in zip(example_figure_1, "ABCD"):
		task.letter = letter

	example_figure_5: typing.List[Task] = [
		Task(0, 7, 2, 1),
		Task(0, 7, 6, 1),
		Task(6, 7, 1, 1),
		Task(0, 10, 6, 1)
	]

	for task, letter in zip(example_figure_5, "WXYZ"):
		task.letter = letter

	C, tasks = 3, example_figure_1
	#C, tasks = 2, example_figure_5

	print("before", tasks)
	cumulative(tasks)
	print("after ", tasks)

if __name__ == "__main__":
	main()
