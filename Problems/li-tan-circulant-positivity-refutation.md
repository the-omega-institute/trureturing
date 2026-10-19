---
slug: li-tan-circulant-positivity-refutation
bibkey: litan2024bargmann
doi: 10.48550/arXiv.2412.08022
url: https://arxiv.org/abs/2412.08022v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation.result
---

# Li–Tan circulant positivity is false at order four

## Problem

Mao-Sheng Li and Yi-Xi Tan, *On the Bargmann invariants for quantum imaginarity*, arXiv:2412.08022v1, Section III, page 5, state:

> For the case when n = 3, we deduced that the positive semidefiniteness of C_H follows from the positive semidefiniteness of H. This leads us to the conjecture that the positive semidefiniteness of H implies the positive semidefiniteness of C_H (which may depend on n) for general n.

The universal implication is **Refuted**, even on real positive-entry correlation matrices at $n=4$. [Preregistration #19081](https://github.com/the-omega-institute/trureturing/issues/19081) specifies the source, conventions and literature screen. The [Library note](../Library/QuantumContext/litan2024bargmann.md) quotes the definitions of $\mathbf H_n$, $C_n$ and $z_k$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every positive dimension $n$ | `claim`: every natural `n` with `[NeZero n]` | The source matrices have positive order |
| Every complex matrix $H\in\mathbf H_n$ | Complex matrices indexed by `Fin n`, `H.PosSemidef`, and every diagonal entry equal to one | Hermitianity is included in `Matrix.PosSemidef`; no extra restriction |
| $l\oplus k$ | `l + Fin.ofNat n k` in `z` | Modular addition with zero-based labels |
| $r_{ij}\ge0$ and principal $\theta_{ij}\in(-\pi,\pi]$ | Complex norm and `Complex.arg` | The source's modulus and phase conventions |
| Geometric modulus and arithmetic phase means | `z`, including the real $1/n$ power | All indices occur exactly once |
| $C_H=\sum_{k=0}^{n-1}z_k C_n^k$ | `CH`, with the source shift written entrywise | The shift has a one exactly when $j=i+1$ |
| Positive semidefiniteness of $C_H$ | `(CH n H).PosSemidef` | Full positivity conclusion |
| Refutation | `result : ¬ claim` | One admissible order-four instance disproves the universal assertion |

All binders and conjuncts implement these clauses. The unit-diagonal restriction makes the claimed implication weaker than an unrestricted matrix implication, so its refutation also refutes that stronger assertion.

## Motivation

The source proposes this particular transform as a route from correlation matrices to circulant matrices. A failure of this map distinguishes that route from existence of some circulant realization with a prescribed Bargmann invariant.

## Gap

The source proves an order-three statement and conjectures positivity in general order. The exact order-four instance settles the general implication; it does not classify the transform's positivity domain.

## Route

The module `D5/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation.lean` uses
$H=\begin{pmatrix}1&5/8&1/9&5/8\\5/8&1&5/8&4/9\\1/9&5/8&1&5/8\\5/8&4/9&5/8&1\end{pmatrix}$.
Its private `h_gram` supplies a diagonal Gram factorization; `h_psd` applies `Matrix.PosSemidef.diagonal` and `Matrix.PosSemidef.conjTranspose_mul_mul_same`. `h_diag` checks the unit diagonal. `z_values` evaluates the coefficients as $(1,5/8,2/9,5/8)$, `ch_eq` evaluates the transform, and `quadratic` gives $v^*C_Hv=-1/9$ for $v=(1,-1,1,-1)$. `result` contradicts `Matrix.PosSemidef.dotProduct_mulVec_nonneg`.

The source shift's expression remains literal in `CH`; private `shift_eq` identifies it with `Matrix.circulant (Pi.single (-1) 1)` for the coefficient calculation. Only pinned Mathlib is imported. All theorems have `proof_shape: bind-only`; the module's admission basis is `open-problem-resolution (#19081; Refuted)`. The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Falsifier

A mismatch in the shift orientation, principal-phase convention, admissibility of $H$, or the negative quadratic value would invalidate this certificate as a refutation of the quoted conjecture. The source clauses above fix these conventions; the Lean theorem checks the exact negation of their universal implication.

## Evidence

**Kernel-checked:** `D5.S3.Quantum.Matrix.LiTanCirculantPositivityRefutation.result`, with private helpers listed in Route. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}. The fixed instance is the entire kernel-checked scope.

**Computed:** [the pinned experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/29616f484f91cf715c06c0b73367686d5013270c/docs/reports/li-tan-2024-circulant-positivity-refutation). Command: `python3 check.py` in that directory, exit 0 (`RESULT PASS`); `check.py` SHA-256: `1d4a97405fdc92556d02b3aa02dd9b737acd69ea9b88d1ed350cc41ebe7cbf9f`. The pinned script was rerun without changes. Its exact rational witness has leading principal minors $1,39/64,95/324,275/13122$, coefficients $(1,5/8,2/9,5/8)$, quadratic value $-1/9$ and alternating eigenvalue $-1/36$. Its numerical minimum eigenvalue is $-0.02777777777777742$. With NumPy's `default_rng(0)` it samples 20,000 normalized complex Gaussian Gram matrices for each of $n=3,4$, using an eigenvalue threshold $-10^{-10}$ on the Hermitian part of the transform; the indefinite counts are respectively 0 and 6,093. No parameterized symbolic identity or uniform dimension statement is computed by this script.

## Triage

### What the settlement shows

1. **Kernel-checked — settlement.** `result`, using `h_psd`, `h_diag` and `quadratic`, refutes the universal implication with the real positive-entry matrix displayed above at $n=4$. Complex phase averaging is unnecessary for failure: the certificate's entry phases are zero, as checked in `z_values`.

2. **Kernel-checked — fixed mechanism.** `z_values` and `ch_eq` replace opposite correlations $1/9$ and $4/9$ by their geometric mean $2/9$; `quadratic` gives the negative alternating quadratic value $-1/9$. Positive definiteness of the input, as opposed to semidefiniteness, is **computed** by the exact minors in Evidence, not asserted by a public Lean theorem.

3. **Proved in prose — parameterized mechanism.** For
$H(a,e,f)=\begin{pmatrix}1&a&e&a\\a&1&a&f\\e&a&1&a\\a&f&a&1\end{pmatrix}$,
assume $0<e,f<1$, $e\ne f$, and
$\frac{1+\sqrt{ef}}2<a<\frac{\sqrt{(1+e)(1+f)}}2$.
Let $T$ have columns $e_0+e_2,e_1+e_3,e_0-e_2,e_1-e_3$. Adding and subtracting the corresponding rows and columns gives
$T^{\mathsf T}HT=\operatorname{diagblock}\!\left(\begin{pmatrix}2(1+e)&4a\\4a&2(1+f)\end{pmatrix},2(1-e),2(1-f)\right)$.
The columns have squared norm 2 and are mutually orthogonal. Subtracting the first row of $T$ from its third, and its second from its fourth, leaves an upper triangular matrix with diagonal $(1,1,-2,-2)$, so $\det T=4$. The two scalar blocks are positive. The two-by-two block has positive diagonal and determinant $4((1+e)(1+f)-4a^2)>0$, so congruence makes $H$ positive definite. For $0<e,f<1$, the same block criterion gives the equivalence between positive definiteness of $H$ and $4a^2<(1+e)(1+f)$. Since $a,e,f$ are positive, the transform has first row $(1,a,\sqrt{ef},a)$, hence the alternating vector has eigenvalue $1+\sqrt{ef}-2a<0$. Since $e,f>0$, $\sqrt{ef}=\sqrt e\sqrt f$. Expanding both sides gives
$(1+e)(1+f)-(1+\sqrt{ef})^2=(\sqrt e-\sqrt f)^2>0$,
so the interval for $a$ is nonempty. These calculations supply a prose family proof. The family is not Lean-formalized, and the pinned experiment does not check its symbolic identities; the displayed identities follow from the algebra above.

4. **Computed — frequency on the tested samples.** Evidence reports 0 of 20,000 at $n=3$ and 6,093 of 20,000 at $n=4$ with the stated generator and threshold. These are finite sample counts, not probability bounds, a classification, or a proof of the order-three result.

5. **Open here — surviving scope.** No counterexample to the source's $n=3$ theorem is claimed. The positivity-preserving input classes beyond this counterexample family and a full classification of this map remain open here. Equality $\mathcal B_n=\mathcal B_{n\mid\mathrm{circ}}$ is logically distinct: existence of a circulant realization need not be supplied by this particular $H\mapsto C_H$ construction. Uses of the general positivity conjecture have a false premise; source statements proved separately at $n=3$ retain their stated scope.

6. **Literature reading — other papers.** The literature screen recorded in #19081 attributes an independent route to $\mathcal B_n=\mathcal B_{n\mid\mathrm{circ}}$ to Pratapsi–Gouveia–Novo–Galvão, arXiv:2506.17132. The issue also records Xu (arXiv:2506.13266), Zhang–Xie's survey (arXiv:2601.01858), and seven later works, including arXiv:2507.14878 and arXiv:2601.16435, as not settling positivity of this map in the searched scope. These are issue-supplied literature readings, not independently reverified results in this delivery. The separate equality is unaffected by this refutation.

## ASSUMED-UNVERIFIED

Literature completeness and priority remain `ASSUMED-UNVERIFIED`: the preregistration's literature screen found no settlement in its searched scope and is attributed to its search seat and orchestrator. Agreement of the journal version, Phys. Rev. A 111 (2025) 022409, with the arXiv v1 conjecture is unverified because that journal text was not accessed. The parameterized family above is proved in prose; its universally quantified Lean formalization and a classification outside it remain open. Sampling gives no uniform conclusion.
