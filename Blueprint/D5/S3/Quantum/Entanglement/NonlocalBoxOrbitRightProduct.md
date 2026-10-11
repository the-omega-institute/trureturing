# Right multiplication maximizes CHSH over the orbit

## Abstract

Right multiplication maximizes CHSH over every parenthesization in the PR-SR-I triangle.

**Definition 1.1 (Popescu-Rohrlich box).**

$$\forall (a : \operatorname{Fin}(2)), \forall (b : \operatorname{Fin}(2)), \forall (x : \operatorname{Fin}(2)), \forall (y : \operatorname{Fin}(2)), \operatorname{PR}(a, b, x, y) = \operatorname{if} (a + b = x * y) \operatorname{then} \frac{1}{2} \operatorname{else} 0$$

*Formalization.* `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.PR` (`✓ std3`).

*Citation.* P. Botteron; A. Broadbent; R. Chhaibi; I. Nechita; C. Pellegrini (2024). *Algebra of Nonlocal Boxes and the Collapse of Communication Complexity*. URL: <https://arxiv.org/abs/2312.00725v3>.

*Commentary.*

Introduction, displayed definitions of PR, I, P0 and P1: PR(a,b|x,y) := (1/2) 1[a XOR b = xy]. Bits are Fin 2: addition and multiplication are modulo two, and the four arguments are a,b,x,y in that order. The displayed conditional has real values.

**Definition 1.2 (Constant-zero shared output).**

$$\forall (a : \operatorname{Fin}(2)), \forall (b : \operatorname{Fin}(2)), \forall (x : \operatorname{Fin}(2)), \forall (y : \operatorname{Fin}(2)), \operatorname{P0}(a, b, x, y) = \operatorname{if} ((a = 0) \land (b = 0)) \operatorname{then} 1 \operatorname{else} 0$$

*Formalization.* `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.P0` (`✓ std3`).

*Citation.* P. Botteron; A. Broadbent; R. Chhaibi; I. Nechita; C. Pellegrini (2024). *Algebra of Nonlocal Boxes and the Collapse of Communication Complexity*. URL: <https://arxiv.org/abs/2312.00725v3>.

*Commentary.*

Introduction, displayed definitions of PR, I, P0 and P1: P0 := 1[a=b=0]. The conditional ignores both input bits.

**Definition 1.3 (Constant-one shared output).**

$$\forall (a : \operatorname{Fin}(2)), \forall (b : \operatorname{Fin}(2)), \forall (x : \operatorname{Fin}(2)), \forall (y : \operatorname{Fin}(2)), \operatorname{P1}(a, b, x, y) = \operatorname{if} ((a = 1) \land (b = 1)) \operatorname{then} 1 \operatorname{else} 0$$

*Formalization.* `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.P1` (`✓ std3`).

*Citation.* P. Botteron; A. Broadbent; R. Chhaibi; I. Nechita; C. Pellegrini (2024). *Algebra of Nonlocal Boxes and the Collapse of Communication Complexity*. URL: <https://arxiv.org/abs/2312.00725v3>.

*Commentary.*

Introduction, displayed definitions of PR, I, P0 and P1: P1 := 1[a=b=1]. The conditional ignores both input bits.

**Definition 1.4 (Shared randomness).**

$$\operatorname{SR} = \frac{1}{2} \cdot (\operatorname{P0} + \operatorname{P1})$$

*Formalization.* `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.SR` (`✓ std3`).

*Citation.* P. Botteron; A. Broadbent; R. Chhaibi; I. Nechita; C. Pellegrini (2024). *Algebra of Nonlocal Boxes and the Collapse of Communication Complexity*. URL: <https://arxiv.org/abs/2312.00725v3>.

*Commentary.*

Section 2.5, p. 17: SR := (P0 + P1)/2 is the shared randomness box. The real scalar acts pointwise on the function.

**Definition 1.5 (Uniform box).**

$$\forall (a : \operatorname{Fin}(2)), \forall (b : \operatorname{Fin}(2)), \forall (x : \operatorname{Fin}(2)), \forall (y : \operatorname{Fin}(2)), \operatorname{Ibox}(a, b, x, y) = \frac{1}{4}$$

*Formalization.* `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.Ibox` (`✓ std3`).

*Citation.* P. Botteron; A. Broadbent; R. Chhaibi; I. Nechita; C. Pellegrini (2024). *Algebra of Nonlocal Boxes and the Collapse of Communication Complexity*. URL: <https://arxiv.org/abs/2312.00725v3>.

*Commentary.*

Introduction, displayed definitions of PR, I, P0 and P1: I := 1/4. Ibox is its Lean name; every conditional probability has the same real value.

**Definition 1.6 (The WBS box product).**

$$\forall (P : \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \mathbb{R}), \forall (Q : \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \mathbb{R}), \forall (a : \operatorname{Fin}(2)), \forall (b : \operatorname{Fin}(2)), \forall (x : \operatorname{Fin}(2)), \forall (y : \operatorname{Fin}(2)), \operatorname{boxProd}(P, Q, a, b, x, y) = \sum_{a1 : \operatorname{Fin}(2)} (\sum_{a2 : \operatorname{Fin}(2)} (\sum_{b1 : \operatorname{Fin}(2)} (\sum_{b2 : \operatorname{Fin}(2)} (P(a1, b1, x, y) * Q(a2, b2, x * a1, y * b1) * (\operatorname{if} (a = a1 + a2) \operatorname{then} 1 \operatorname{else} 0) * (\operatorname{if} (b = b1 + b2) \operatorname{then} 1 \operatorname{else} 0)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.boxProd` (`✓ std3`).

*Citation.* P. Botteron; A. Broadbent; R. Chhaibi; I. Nechita; C. Pellegrini (2024). *Algebra of Nonlocal Boxes and the Collapse of Communication Complexity*. URL: <https://arxiv.org/abs/2312.00725v3>.

*Commentary.*

Equation (9) is the sum over a1,a2,b1,b2 of the two box probabilities and the two output indicators. For the wiring W_BS in Section 4, f1=x, g1=y, f2=x a1, g2=y b1, f3=a1 XOR a2 and g3=b1 XOR b2. The displayed finite sums use the literal product of the two output conditionals; the external arguments are a,b,x,y. Each sum ranges over Fin 2, and its value is real.

**Definition 1.7 (CHSH winning probability).**

$$\forall (P : \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \mathbb{R}), \operatorname{chsh}(P) = \frac{1}{4} * \sum_{a : \operatorname{Fin}(2)} (\sum_{b : \operatorname{Fin}(2)} (\sum_{x : \operatorname{Fin}(2)} (\sum_{y : \operatorname{Fin}(2), a + b = x * y} P(a, b, x, y))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.chsh` (`✓ std3`).

*Citation.* P. Botteron; A. Broadbent; R. Chhaibi; I. Nechita; C. Pellegrini (2024). *Algebra of Nonlocal Boxes and the Collapse of Communication Complexity*. URL: <https://arxiv.org/abs/2312.00725v3>.

*Commentary.*

Section 2.3, p. 15: CHSH(P) := one quarter of the sum of P(a,b|x,y) over a XOR b = xy. The final sum is filtered by precisely that equation; all four bits range over Fin 2. This is the winning-probability normalization, rather than the correlator normalization.

**Definition 1.8 (Full binary parenthesizations).**

$$\operatorname{Paren} : \operatorname{Type} \;\operatorname{Paren}.\operatorname{leaf} : \operatorname{Paren} \;\operatorname{Paren}.\operatorname{node} : \operatorname{Paren} \to \operatorname{Paren} \to \operatorname{Paren}$$

*Formalization.* `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.Paren` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A full binary parenthesization has either one leaf or an ordered pair of child parenthesizations. The constructors leaf and node carry no labels: every leaf stands for the same box P.

**Definition 1.9 (Leaf count).**

$$\forall (l : \operatorname{Paren}), \forall (r : \operatorname{Paren}), (\operatorname{Paren}.\operatorname{size}(\operatorname{Paren}.\operatorname{leaf}) = 1) \land (\operatorname{Paren}.\operatorname{size}(\operatorname{Paren}.\operatorname{node}(l, r)) = \operatorname{Paren}.\operatorname{size}(l) + \operatorname{Paren}.\operatorname{size}(r))$$

*Formalization.* `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.size` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The leaf count is one at a leaf and the sum of both child counts at a node. It counts copies of P, not internal multiplication nodes.

**Definition 1.10 (Evaluate a parenthesization).**

$$\forall (P : \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \mathbb{R}), \forall (l : \operatorname{Paren}), \forall (r : \operatorname{Paren}), (\operatorname{eval}(P, \operatorname{Paren}.\operatorname{leaf}) = P) \land (\operatorname{eval}(P, \operatorname{Paren}.\operatorname{node}(l, r)) = \operatorname{boxProd}(\operatorname{eval}(P, l), \operatorname{eval}(P, r)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.eval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluation substitutes P at every leaf and the W_BS product at every internal node. Both subtree evaluations use the same box.

**Definition 1.11 (Every product of k copies).**

$$\forall (k : \mathbb{N}), \forall (P : \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \mathbb{R}), \operatorname{orbit}(k, P) = \{Q : \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \mathbb{R} \mid \exists (t : \operatorname{Paren}), (\operatorname{Paren}.\operatorname{size}(t) = k) \land (Q = \operatorname{eval}(P, t))\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.orbit` (`✓ std3`).

*Citation.* P. Botteron; A. Broadbent; R. Chhaibi; I. Nechita; C. Pellegrini (2024). *Algebra of Nonlocal Boxes and the Collapse of Communication Complexity*. URL: <https://arxiv.org/abs/2312.00725v3>.

*Commentary.*

Section 2.1, p. 12, defines the k-orbit by the words: all possible products with k times the term P, using the multiplication \boxtimes_W. Q belongs exactly when a full binary tree t has k leaves and Q equals its evaluation. There is no zero-leaf tree, so orbit 0 P is empty.

**Definition 1.12 (Multiply fresh copies on the right).**

$$\forall (P : \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \mathbb{R}), \forall (n : \mathbb{N}), (\operatorname{rightPow}(P, 0) = P) \land ((\operatorname{rightPow}(P, 1) = P) \land (\operatorname{rightPow}(P, n + 2) = \operatorname{boxProd}(\operatorname{rightPow}(P, n + 1), P)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.rightPow` (`✓ std3`).

*Citation.* P. Botteron; A. Broadbent; R. Chhaibi; I. Nechita; C. Pellegrini (2024). *Algebra of Nonlocal Boxes and the Collapse of Communication Complexity*. URL: <https://arxiv.org/abs/2312.00725v3>.

*Commentary.*

Theorem 13, p. 16, writes P^{boxtimes k} := ((P boxtimes P) boxtimes P) ... boxtimes P. rightPow is this left-nested product: every step multiplies by a fresh P on the right. Its zero-depth value is set to P; that convention has no effect on the empty zero-depth orbit.

**Definition 1.13 (Conjecture 15).**

$$\operatorname{claim} = (\forall (P : \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \mathbb{R}), (P \in \operatorname{convexHull}(\mathbb{R}, \{\operatorname{PR}, \operatorname{SR}, \operatorname{Ibox}\})) \Rightarrow (\frac{3}{4} \leq \operatorname{chsh}(P)) \Rightarrow \forall (k : \mathbb{N}), (2 \leq k) \Rightarrow \forall (Q : \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \mathbb{R}), (Q \in \operatorname{orbit}(k, P)) \Rightarrow \operatorname{chsh}(Q) \leq \operatorname{chsh}(\operatorname{rightPow}(P, k)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.claim` (`✓ std3`).

*Citation.* P. Botteron; A. Broadbent; R. Chhaibi; I. Nechita; C. Pellegrini (2024). *Algebra of Nonlocal Boxes and the Collapse of Communication Complexity*. URL: <https://arxiv.org/abs/2312.00725v3>.

*Commentary.*

Conjecture 15 (Dyck paths), p. 16, verbatim: We conjecture that the same result actually holds without the tilde, i.e. the right multiplication P^{\boxtimes k} gives the highest CHSH-value of \mathrm{Orbit}^{(k)}(P), as observed numerically. The source's displayed notation is P^{\boxtimes k} and \mathrm{Orbit}^{(k)}(P). The encoding ranges over every real box function P in convexHull Real {PR,SR,Ibox} with chsh P >= 3/4, every natural k >= 2 and every Q in orbit k P. It drops Theorem 13's tilted-orbit distillation hypothesis. Fin 2 implements XOR as modular addition. No restriction is imposed on the full binary parenthesization.

**Theorem 1.14 (The whole triangle satisfies the bound).**

$$\forall (P : \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \mathbb{R}), (P \in \operatorname{convexHull}(\mathbb{R}, \{\operatorname{PR}, \operatorname{SR}, \operatorname{Ibox}\})) \Rightarrow \forall (k : \mathbb{N}), \forall (Q : \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \operatorname{Fin}(2) \to \mathbb{R}), (Q \in \operatorname{orbit}(k, P)) \Rightarrow \operatorname{chsh}(Q) \leq \operatorname{chsh}(\operatorname{rightPow}(P, k))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.whole_triangle_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Botteron; A. Broadbent; R. Chhaibi; I. Nechita; C. Pellegrini (2024). *Algebra of Nonlocal Boxes and the Collapse of Communication Complexity*. URL: <https://arxiv.org/abs/2312.00725v3>.

*Commentary.*

For every box in Conv{PR,SR,I}, every parenthesization has CHSH at most the right product at the same leaf count. The conclusion needs neither chsh P >= 3/4 nor a distillation hypothesis, and includes the one-leaf case. In coordinates P=a PR+(u-a) SR+(1-u) I, multiplication sends (u,a),(v,b) to (uv,av+(1+u-2a)b/4), and CHSH is 1/2+(u+a)/4. The region 0<=u<=1, 0<=a<=(1+u)/2 is closed under this map. A root rotation increases the second coordinate while preserving the first. Repeated multiplication by the original box on the right is monotone in the second coordinate. Structural induction straightens every tree to the left-nested right product.

**Theorem 1.15 (The right product is maximal).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.result` (`✓ std3`). ∎

*Resolves.* `Problems/botteron-et-al-2024-nonlocal-box-orbit-right-product` (proved) by `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"botteron-et-al-2024-nonlocal-box-orbit-right-product","declaration_gid":"D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* P. Botteron; A. Broadbent; R. Chhaibi; I. Nechita; C. Pellegrini (2024). *Algebra of Nonlocal Boxes and the Collapse of Communication Complexity*. URL: <https://arxiv.org/abs/2312.00725v3>.

*Commentary.*

The whole-triangle bound implies Conjecture 15. The maximality statement of Theorem 13 extends to the full orbit without its distillation assumption. Maximality alone does not say that the right product improves on P or that communication complexity collapses. Other wirings, boxes outside the triangle and an explicit formula for the exact maximum as a function of k remain separate questions.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.Ibox`
- Truth anchor: `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.P0`
- Truth anchor: `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.P1`
- Truth anchor: `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.PR`
- Truth anchor: `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.Paren`
- Truth anchor: `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.SR`
- Truth anchor: `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.boxProd`
- Truth anchor: `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.chsh`
- Truth anchor: `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.eval`
- Truth anchor: `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.orbit`
- Truth anchor: `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.rightPow`
- Truth anchor: `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.size`
- Truth anchor: `D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.whole_triangle_max`
