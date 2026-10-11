---
bibkey: krishna2022cstarsendov
authors: K. Mahesh Krishna
year: 2022
title: "C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture"
doi: 10.48550/arXiv.2203.06916
url: https://arxiv.org/abs/2203.06916v1
claim: "Definitions 2.1 and 2.3 specify differentiation and the C*-disc; Equation (1) specifies positive barycentric form; Conjectures 2.4 and 2.5 assert Sendov bounds, with Theorem 2.6 proving degree two."
strata_touched:
  - D5/S3/Quantum/Algebra/CStarSendov
  - D5/S3/Quantum/Algebra/CStarSendovCommutative
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2203.06916

Source: https://arxiv.org/abs/2203.06916v1

Journal DOI: https://doi.org/10.26117/2079-6641-2026-54-1-56-63

# C*-algebraic Sendov conjectures

K. M. Krishna, "C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture", arXiv:2203.06916v1 (14 March 2022; one arXiv version). Journal version: Vestnik KRAUNC Fiz.-Mat. Nauki 54(1) (2026) 56–63, DOI 10.26117/2079-6641-2026-54-1-56-63 The formal statements below refer to arXiv v1.

Section 2, p. 2, Definition 2.1 (C*-algebraic differentiation):

> Let $\mathcal{A}$ be a unital commutative C*-algebra and $G(\mathcal{A})$ be dense in $\mathcal{A}$. Let $f: \mathcal{A}\to \mathcal{A}$ be a function and $\omega\in \mathcal{A}$. We say that $f$ is C*-algebraic differentiable at $\omega$ if there exists an $L\in \mathcal{A}$ satisfying the following: for each $\varepsilon>0$, there exists a $\delta>0$ such that if $z\in \mathcal{A}$ satisfies $\|z-\omega\|<\delta$ and $z-\omega\in G(\mathcal{A})$, then $\|(z-\omega)^{-1}(f(z)-f(\omega))-L\|<\varepsilon.$ In this case, we write $f'(\omega)=L$.

Theorem 2.2 (Gauss–Lucas), pp. 2–3, Equation (1):

> there are positive $\omega_{z_1}, \dots, \omega_{z_n} \in \mathcal{A}$ such that $z=\sum_{j=1}^{n}\omega_{z_j}a_j, \quad \sum_{j=1}^{n}\omega_{z_j}=1.$

Definition 2.3, p. 3:

> Given a unital C*-algebra $\mathcal{A}$ with identity $1$ and an element $a\in \mathcal{A}$, we define the C*-algebraic closed unit disc centered at $a$ and of radius $r>0$, $r\in \mathbb{R}$, denoted as $\overline{\mathbb{D}^*(a, r)}$ by $\overline{\mathbb{D}^*(a, r)}\coloneqq \{z\in \mathcal{A}: (z-a)(z-a)^*\leq \sqrt{r}\cdot 1\}.$

Conjecture 2.4, p. 3 (Commutative C*-algebraic Sendov's conjecture):

> Let $\mathcal{A}$ be a unital commutative C*-algebra and $G(\mathcal{A})$ be dense in $\mathcal{A}$. Let $n \in \mathbb{N}\setminus \{1\}$ and $p(z)=(z-a_1)(z-a_2)\cdots (z-a_n)\in\mathcal{A}[z]$ be such that $a_1, a_2, \dots, a_n \in \overline{\mathbb{D^*}(0, 1)}$. Assume that $p'$ admits roots in $\mathcal{A}$, say $b_1, b_2, \dots, b_{n-1} \in \overline{\mathbb{D^*}(0, 1)}$ and each $b_k$ can be written in the form of Equation (1). Then for each $a_j$, $1\leq j\leq n$, there exists a zero $b$ of $p'$ such that $b \in \overline{\mathbb{D}^*(a_j, 1)}$.

Conjecture 2.5, p. 3 (C*-algebraic Sendov's conjecture):

> Let $\mathcal{A}$ be a unital C*-algebra. Let $n \in \mathbb{N}\setminus \{1\}$ and $p(z)=(z-a_1)(z-a_2)\cdots (z-a_n)\in\mathcal{A}[z]$ be such that $a_1, a_2, \dots, a_n \in \overline{\mathbb{D^*}(0, 1)}$. Define $p'(z)=\sum_{j=1}^{n}(z-a_1)\cdots \widehat{(z-a_j)}\cdots (z-a_n), \forall z \in \mathcal{A}$, where the term with cap is missing. Assume that $p'$ admits roots in $\mathcal{A}$, say $b_1, b_2, \dots, b_{n-1} \in \overline{\mathbb{D^*}(0, 1)}$ and each $b_k$ can be written in the form of Equation (1). Then for each $a_j$, $1\leq j\leq n$, there exists a zero $b$ of $p'$ such that $b \in \overline{\mathbb{D}^*(a_j, 1)}$.

The source proves Conjecture 2.5 for degree 2 (Theorem 2.6).


The encoding uses zero-based `Fin n` indices, unital C*-algebras in `Type` with a compatible partial order and `StarOrderedRing`, and degrees `2 ≤ n`. These restrictions weaken the universal claims, so their refutations imply refutations of the printed claims. The disc uses the source's `Real.sqrt r`, including its unusual radius convention; only radius one is used. Positive means nonnegative in the C*-order. The constructed barycentric weights are also invertible and strictly positive pointwise.

The commutative derivative is the epsilon-delta condition of Definition 2.1, along invertible increments. Density of invertibles is a hypothesis of the commutative claim. The ordered derivative is the sum of products with exactly one indexed factor omitted; factor order is retained by `List.eraseIdx`. The conclusion permits any algebra-valued derivative zero, including zeros not in the supplied tuple.

Theorem 2.6 (p. 3) proves Conjecture 2.5 for polynomials of degree two. The cubic counterexample does not change that theorem or the independent Gauss-Lucas Theorem 2.2. The journal version is Vestnik KRAUNC Fiz.-Mat. Nauki 54(1), 56–63, and also states a complete-factorization variant. The cubic derivative in the counterexample factors completely; the journal variant is not formalized here.
