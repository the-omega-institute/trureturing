---
bibkey: gschwendtnerbluhmwinter2021programmability
authors: Martina Gschwendtner, Andreas Bluhm, Andreas Winter
year: 2021
title: Programmability of covariant quantum channels
doi: 10.22331/q-2021-06-29-488
url: https://arxiv.org/abs/2012.00717v2
claim: Exact covariant programming has mixed optimum d_c; the Section 5 question asks whether pure programs attain the same dimension.
strata_touched:
  - D5/S3/Quantum/QuantumChannels/PureProgramQubitObstruction
  - D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.22331/q-2021-06-29-488

Source: https://arxiv.org/abs/2012.00717v2

Quantum **5**, 488. The page numbers below refer to the arXiv v2 PDF.

## Covariance and processors

Page 2 defines states by
$\mathcal D(\mathcal H_1)=\{\rho\in\mathcal B(\mathcal H_1)\mid\rho\ge0,\operatorname{tr}(\rho)=1\}$.

> A quantum channel is a completely positive trace-preserving map $T : \mathcal B(\mathcal H_1) \to \mathcal B(\mathcal H_2)$, where $d_1, d_2 \in \mathbb N$.

Definition 2, page 3, states:

> A unitary representation $U$ of a group $G$ on a finite-dimensional vector space $\mathcal H_1$ is called irreducible representation (irrep) if and only if the only invariant subspaces of $\{U_g\mid g\in G\}$ are $\{0\}$ and the whole space.

Definition 10, page 4, states:

> We call $T$ $UV$-covariant if

$$T(U_g A U_g^*)=V_g T(A)V_g^*\qquad\forall A\in\mathcal B(\mathcal H_1),\ \forall g\in G.$$

Definition 12, page 5, states:

> Let $\mathcal H_1$ and $\mathcal H_2$ be separable Hilbert spaces. Then we call $\mathcal P \in \mathrm{CPTP}(\mathcal H_1\otimes\mathcal H_P,\mathcal H_2)$, with finite-dimensional $\mathcal H_P$, an $\epsilon$-programmable quantum processor for a set $\mathcal C\subset\mathrm{CPTP}(\mathcal H_1,\mathcal H_2)$ of channels ($\epsilon$-PQP$_{\mathcal C}$), if for every quantum channel $T\in\mathcal C$ there exists a state $\pi_T\in\mathcal D(\mathcal H_P)$ such that

$$\tfrac12\|\mathcal P(\cdot\otimes\pi_T)-T(\cdot)\|_\diamond\le\epsilon.$$

For $\mathcal C=\mathcal T_{UV}$ this is an $\epsilon$-CPQP$_{UV}$.
At $\epsilon=0$ the processor implements every covariant channel exactly;
$d_P=\dim\mathcal H_P$ is its program dimension.

## Dimension bounds and pure programs

Write the commutant of $\bar U\otimes V$ as
$\mathcal K\cong\bigoplus_k\mathbb1_{b_k}\otimes\mathcal B(\mathbb C^{n_k})$
and set $d_c=\sum_k n_k$.
Theorem 31 supplies the lower bound $d_P\ge d_c$ in the exact case.
The teleportation construction of Theorem 25 attains $d_P=d_c$ with mixed
programs. Purifying those programs gives the general upper bound $d_c^2$.
Remark 13 (pure-mixed), page 6, states:

> In the literature, where the set of channels $\mathcal C$ often consists of isometries or even unitaries, it is customary to impose that the program state $\pi_T$ is pure.

It discusses more refined pure-program constructions.
Corollary 19 (abelian) attains the lower bound with pure programs when
$\mathcal K$ is abelian.

Section 5, page 21, asks:

> We leave it as an open question whether the upper bounds can be improved to match the lower ones also for pure program states.

The affirmative assertion is that every mixed-program dimension can also
be attained with pure programs. The finite-group restriction already
contains the counterexample $G=D_4$, its two-dimensional irreducible $U$,
and trivial two-dimensional $V$. Here $\bar U\otimes V$ contains two copies
of $\bar U$, giving $d_c=2$. All covariant channels then replace the
input by a state. A mixed qubit program implements them, but a pure qubit
program cannot produce the two basis states, their equal superposition,
and $\mathbb1/2$ through one fixed processor. The Lean result certifies
this dimension-two obstruction. The pure dimension-three construction
and the general multiplicity bounds require additional analytic arguments.
