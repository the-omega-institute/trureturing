---
slug: rajchel-korzekwa-puchala-zyczkowski-2021-bracelet-monoid
bibkey: rajchelkorzekwapuchalazyczkowski2021birkhoff
doi: 10.1063/5.0046581
url: https://arxiv.org/abs/2101.11288
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.IsBracelet
---

# The bracelet matrices form a monoid

## Problem

G. Rajchel-Mieldzioć, K. Korzekwa, Z. Puchała and K. Życzkowski, *Algebraic and geometric structures inside the Birkhoff polytope*, arXiv:2101.11288, J. Math. Phys. 63, 012202, DOI 10.1063/5.0046581, Section III.A, states:

> Conjecture 9. The set of bracelet matrices $L_d$ forms a monoid, i.e., it is closed under matrix multiplication and contains the identity matrix $I_d$.

The preregistration and source quotation are recorded in [#17593](https://github.com/the-omega-institute/trureturing/issues/17593). The existing `IsBracelet` interface is used literally.

### Statement echo

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| Every finite dimension $d$ | `bracelet_monoid` quantifies over every natural `d` | The Lean statement includes `d = 0`; positive dimensions recover the source range |
| Identity matrix $I_d$ belongs to $L_d$ | `IsBracelet (1 : Matrix (Fin d) (Fin d) ℝ)` | The real square matrix identity uses the existing predicate |
| Closure under multiplication | `∀ A B, IsBracelet A → IsBracelet B → IsBracelet (A * B)` | `*` is ordinary matrix multiplication on `Fin d` |
| Bracelet conditions | `CirculantBraceletNonUnistochastic.IsBracelet` | Entrywise nonnegativity, unit row and column sums, and both distinct-index overlap families are retained |

The field is $\mathbb{R}$, and rows and columns use the same finite index type `Fin d`.

## Motivation

The source treats bracelet inequalities as the length constraints underlying unistochasticity. Conjecture 9 asks whether those constraints are stable under the composition operation already present on bistochastic matrices. The closure question is independent of the source's circulant restrictions and of the later unistochasticity conjectures.

## Gap

Theorem 8 in the source establishes closure when one factor is factorizable. Conjecture 9 allows two arbitrary bracelet factors. The proof constructs phases separately for each tested pair of columns or rows.

## Route

For a nonnegative pair $p,q$, write $\ell_i=\sqrt{p_iq_i}$. The pivot bounds imply that the maximum length is at most the sum of the remaining lengths. Greedy signs on those remaining lengths give a resultant of norm at most the maximum. A continuous path of phases connects the all-positive and signed placements, so the resultant attains the maximum length somewhere on the path. Assign the negative of that resultant to the pivot. The resulting closed polygon gives complex amplitudes $x,y$ with squared moduli $p,q$ and $\sum_i\overline{x_i}y_i=0$.

For a rectangular nonnegative matrix $T$ with unit column sums and bracelet column pairs, put $z_r=\sum_i T_{ri}\overline{x_i}y_i$ and $m_{ij}=x_i y_j-x_j y_i$. The weighted Lagrange identity gives

$$
(Tp)_r(Tq)_r=|z_r|^2+\frac{1}{2}\sum_{i,j}T_{ri}T_{rj}|m_{ij}|^2.
$$

The square root is the Euclidean norm of a vector $v_r$ with coordinates $|z_r|$ and $\sqrt{T_{ri}T_{rj}/2}|m_{ij}|$. The unit column sums give $\sum_r z_r=0$. The bracelet bounds on $T$ give the bounds for the minor coordinates, with zero diagonal minors. Thus $v_r\le\sum_{s\ne r}v_s$ coordinatewise. Monotonicity and the triangle inequality give $\|v_r\|\le\sum_{s\ne r}\|v_s\|$.

Use $T=A$ on the columns of $B$. For the rows, use $T=B^{\mathsf{T}}$ on the columns of $A^{\mathsf{T}}$, since $(AB)^{\mathsf{T}}=B^{\mathsf{T}}A^{\mathsf{T}}$. Mathlib's doubly stochastic submonoid supplies the stochastic clauses. Distinct identity rows and columns have disjoint supports.

## Falsifier

Three equal positive lengths satisfy the pivot inequalities. Three real numbers with those absolute values cannot sum to zero, while three equally spaced complex phases do. The proof uses complex amplitudes even though the matrices are real. Both orientations of each off-diagonal minor occur in the sum and account for the factor one half. The phase path includes equality in the pivot bound, and a zero length contributes zero with phase one.

## Evidence

The kernel-checked declaration is `D5/S3/Quantum/Matrix/Unistochastic/BraceletMonoid.bracelet_monoid`. Its axiom closure is contained in `propext`, `Classical.choice`, and `Quot.sound` under the pinned official Mathlib backend. The source module records the proof shape of each private helper and its live consumer. The scoped Lean target is `D5.S3.Quantum.Matrix.Unistochastic.BraceletMonoid`; the source-bound audit mirror is `Reg.D5.S3.Quantum.Matrix.Unistochastic.BraceletMonoid`.

The bounded literature screen examined arXiv:2204.13008, 2310.03436v2, 2405.05785v6, 2505.08785v1, 2604.02309v1, 2312.00497v2 and 2608.04354v1. It located no earlier proof of the full closure assertion in that scope. The journal article body and some forward-citation endpoints were inaccessible or rate-limited. [Preregistration and proof route](https://github.com/the-omega-institute/trureturing/issues/17593#issuecomment-7235297451)

### Stage B claim (inactive)

The exact Conjecture 9 claim is prepared for Stage B as `∀ d : ℕ, IsBracelet (1 : Matrix (Fin d) (Fin d) ℝ) ∧ (∀ A B : Matrix (Fin d) (Fin d) ℝ, IsBracelet A → IsBracelet B → IsBracelet (A * B))`. The Stage B resolution marker is inactive pending independent review and the later freeze workflow.

## Triage

### What the settlement shows

1. **Proved in Lean — all finite dimensions.** `bracelet_monoid` proves identity membership and product closure for every natural dimension, including the vacuous zero-dimensional distinct-index families.

2. **Proved in Lean — composition mechanism.** The reusable mechanism is rectangular column preservation from orthogonal complex amplitudes, a weighted Lagrange identity, cancellation from unit column sums, and Euclidean norm comparison. Transposition supplies the row conditions.

3. **Source consequence in prose.** The product in Eq. (49) gives the star-shapedness argument described after Theorem 14. For $0\le t\le 1$, the matrix $(1-t)I_d+tW_d$ is bracelet. For $d\ge 2$, each overlap list has two equal largest terms at the two selected indices. Multiplication on the right by a bracelet matrix $B$ gives the segment point $(1-t)B+tW_d$, since $W_dB=W_d$ by unit column sums. The case $d=1$ is the singleton identity. [arXiv:2101.11288v1, Eq. (49)](https://arxiv.org/pdf/2101.11288v1#page=8)

4. **Other source questions.** The existing dossiers give separate refutations of [circulant bracelet sufficiency](rajchel-korzekwa-puchala-zyczkowski-2021-circulant-bracelet-sufficiency.md) and [Conjecture 19](rajchel-korzekwa-puchala-zyczkowski-2021-conjecture19-circulant-lift.md). The rectangular preserver converse and positive-defect contraction are outside this Lean result.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the cited source and the explicitly inspected topic and citation scopes. It does not establish exhaustive prior-art coverage or worldwide priority. The mathematical theorem and its stated axiom closure are the Lean-checked contents of this delivery.
