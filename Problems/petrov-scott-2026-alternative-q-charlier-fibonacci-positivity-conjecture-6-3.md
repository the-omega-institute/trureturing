---
slug: petrov-scott-2026-alternative-q-charlier-fibonacci-positivity-conjecture-6-3
bibkey: petrovscott2026clone
doi: 10.1017/fms.2025.10165
url: https://arxiv.org/abs/2412.21126v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.result
---

# Alternative q-Charlier Fibonacci positivity: Petrov–Scott Conjecture 6.3

## Problem

Leonid Petrov and Jeanne Scott, *Random Fibonacci words via clone Schur functions*, Forum of Mathematics, Sigma 14 (2026), e15, DOI 10.1017/fms.2025.10165, arXiv:2412.21126v2, Conjecture 6.3, p. 31:

> There exist values of ρ and q for which the following specialization (which we call the alternative q-Charlier) is Fibonacci positive:

$$
x_k=\frac{q^{k-1}(1+\rho q^{k-2}+\rho q^{k-1}-\rho q^{2k-2})}{(1+\rho q^{2k-3})(1+\rho q^{2k-1})},\qquad
 y_k=\frac{\rho q^{3k-2}(1-q^k)(1+\rho q^{k-1})}{(1+\rho q^{2k})(1+\rho q^{2k-1})^2(1+\rho q^{2k-2})},\qquad k\ge1.
$$

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Equation (2.10): first tridiagonal determinant, including the empty determinant | `A` | Every matrix entry is literal; size is any natural number. |
| Equation (2.10): second determinant, first row $y_1,x_1y_2$, then diagonal $x_3,x_4,\ldots$ | `B` | `B k` has size $k+1$. |
| Definition 2.5: leading ones, then a two and a shifted remaining word | `sAux`, `s` | Shift is the inline function $k\mapsto u(k+\lvert w\rvert)$; the weight is `List.sum`. The extension to other natural letters does not alter the predicate on Fibonacci words. |
| Definition 4.1: strict positivity for every word over $\{1,2\}$ | `FibonacciPositive` | Includes the empty word and arbitrary weight; no finite cutoff. |
| Conjecture 6.3: the displayed specializations for every $k\ge1$ | `xAQC`, `yAQC` | Integer powers retain negative exponents at $k=1$. Values at index zero are outside the source domain and unused by the word determinants. |
| There exist values of $\rho,q$ | `claim`, `result` | Both range over $\mathbb R$ without extra assumptions; the proof chooses $\rho=q=1/4$. |

Every public definition has its full body in the Blueprint. No source clause is dropped. The private stronger induction applies to the extension on all natural-letter lists; the public result retains exactly the source's Fibonacci-word restriction.

## Motivation

The conjecture asks for an actual positive specialization, rather than positivity of finitely many words. The result supplies $\rho=q=1/4$ with no bound on dimension, word length or weight. The preregistration and source/literature screen are [#18756](https://github.com/the-omega-institute/trureturing/issues/18756).

## Gap

The kernel theorem settles the existential Conjecture 6.3. The exact parameter region, the uniform rectangle $0<\rho,q\le1/4$ in Lean, and scaling limits or further probabilistic consequences are open in this delivery. The sufficient region $0<\rho,q<1$, $q(1+q)(1+\rho)^3<1-\rho$ is proposed with a continuant argument in #18756; no delivered Lean declaration proves that region.

## Route

For $\rho=q=1/4$, the private functions `cc` and `tt` normalize the specialization: `x_normal` and `y_normal` identify the diagonal and upper-diagonal coefficients. `paramT_bounds` and `paramT_lower` yield $0\le t_k\le1/4$, positivity at positive indices and $t_{k+1}\le t_k/2$ for $k\ge1$.

The private `det_pos_of_dominant` proves positive determinant from positive diagonal and strict row diagonal dominance by continuously deforming to a positive diagonal matrix. It uses Mathlib's `det_ne_zero_of_sum_row_lt_diag` and `intermediate_value_Icc'`. The private `tri_det_pos` constructs a positive cumulative reciprocal diagonal multiplier and proves dominance for every matrix size. `A_pos` and `B_pos` apply it, including the exceptional first row of each shifted B matrix. `sAux_pos` uses list induction, and `result` introduces the two existential parameters.

## Falsifier

A failed entrywise normalization, a loss of strict dominance in a shifted B first row, or an incorrect recursion-to-word correspondence would invalidate this route. The Lean statements include all dimensions and shifts; the numerical experiment below covers only its specified finite range.

## Evidence

The settling declaration is `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.result`. Its admission basis is `open-problem-resolution (#18756; Proved)`, generality is `I`, and utility is `none`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The escape audit of `result` is unfinished: [#19808](https://github.com/the-omega-institute/trureturing/issues/19808). No Reg registration is delivered. The missing evidence comprises source-family realization and reconstruction, correspondence, nonemptiness, variation and sensitivity for the real-parameter family with its unbounded word domain. A scoped report has an empty registration inventory; this is not `declared_validated`.

### Experiment

The numerical check is published in [the experiments repository](https://github.com/the-omega-institute/trureturing-experiments/tree/40d9379b7fe91e73c748a45f9194e4f6e3ae130d/docs/reports/petrov-scott-2026-conjecture-6-3-alternative-q-charlier), commit `40d9379b7fe91e73c748a45f9194e4f6e3ae130d`, file `docs/reports/petrov-scott-2026-conjecture-6-3-alternative-q-charlier/check.py`. Command: `python3 /Users/auric/trureturing-experiments/docs/reports/petrov-scott-2026-conjecture-6-3-alternative-q-charlier/check.py`; exit 0, `RESULT PASS`; script SHA-256 `dbf6642bd21815b3f747980c5b42ed5cbf272e8bcd39af28592af1ab5850a184`.

Its exact scope is symbolic normalization for $k=1,\ldots,8$; exact determinant positivity for all 609 words of weight at most 12 at $\rho=q=1/4$; the bounds $0<t_k\le1/4$ and $t_{k+1}\le(125/256)t_k$ for $k=1,\ldots,58$; $E_k(m)\ge(143/768)t_{m+1}$ for $k,m\le20$; and the continuant determinant forms for $k,\ell,m<8$. These finite checks do not prove a uniform parameter region or an unbounded-word statement.

## Triage

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| Conjecture 6.3 at $\rho=q=1/4$ | proved | Kernel-checked `result`, with arbitrary Fibonacci words. |
| Smallness and geometric contraction imply positive normalized determinants | proved | Kernel-checked private `paramT_bounds`, `paramT_lower`, `tt_decay`, `tri_det_pos`, `A_pos`, `B_pos`; this route does not require continuant identities. |
| General weighted tridiagonal positivity lemma and both consumers | proved | Kernel-checked private `tri_det_pos`; direct consumers are `A_pos` and `B_pos`. |
| Finite numerical checks | computed | The experiment entry: 609 words of weight at most 12 and the exact finite normalization, estimate and continuant ranges above. |
| Exact parameter region | open | No delivered classification theorem. |
| Entire rectangle $0<\rho,q\le1/4$ in Lean | open | The kernel proof fixes both parameters at $1/4$. |
| Scaling limits and further probabilistic consequences | open | No delivered limit or probabilistic theorem. |
| Sharper constants $125/256$ and $143/768$ | computed | The experiment verifies their stated finite ranges; the kernel-checked private `tt_decay` instead establishes contraction $1/2$ uniformly at positive indices. |
| Sufficient region $q(1+q)(1+\rho)^3<1-\rho$ with $0<\rho,q<1$ | open in Lean | The argument in #18756 is not a delivered kernel theorem. |
| Literature status | open | The bounded screen below found no settlement; completeness is `ASSUMED-UNVERIFIED`. |

### What the settlement shows

The decisive mechanism is positive diagonal scaling plus strict diagonal dominance for arbitrary sizes and shifts, followed by word induction. The parameter choice is sufficient; no sharpness or maximality assertion is made. The private general lemma `tri_det_pos` handles any positive coefficient sequence and nonnegative upper-weight sequence satisfying its strict row inequalities. The specialization discharges those inequalities using the uniform contraction $1/2$; no finite numerical certificate enters the proof. The exact region, the whole rectangle in Lean, scaling limits and new probabilistic consequences remain open. No delivered statement changes an earlier theorem of the source or establishes a theorem conditional on Conjecture 6.3 beyond that conjecture itself.

### Declaration classification

| Declaration | proof_shape | escape_witness | Direct consumers |
| --- | --- | --- | --- |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A` | definition | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B` | definition | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.sAux_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.sAux` | definition | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.s`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.sAux_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.sAux_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.s` | definition | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.FibonacciPositive` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.FibonacciPositive` | definition | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.claim`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.result` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.xAQC` | definition | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.claim`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.result`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.sAux_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.sAux_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.x_closed`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.x_closed`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.x_normal`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.x_normal` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.yAQC` | definition | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.claim`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.result`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.sAux_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.sAux_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.y_closed`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.y_closed`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.y_normal`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.y_normal` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.claim` | definition | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.result` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.det_pos_of_dominant` | content | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.det_pos_of_dominant` | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tri_det_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.paramT` | definition | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.paramT_bounds`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.paramT_bounds`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.paramT_lower`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.paramT_lower`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_bound`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_decay`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_nonneg`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.x_normal`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.y_normal` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt` | definition | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_all_bound`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_all_bound`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_bound`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_decay`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_decay`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_nonneg`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.x_normal`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.x_normal`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.y_normal`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.y_normal` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.cc` | definition | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.cc_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.cc_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.x_normal`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.x_normal`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.y_normal`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.y_normal` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.paramT_bounds` | bind-only | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_bound`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_decay`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_nonneg` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.paramT_lower` | bind-only | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_decay`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_nonneg` | bind-only | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_bound` | bind-only | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_all_bound` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_pos` | bind-only | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_decay` | bind-only | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.cc_pos` | bind-only | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.fin_sum_spike_le` | bind-only | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tri_det_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.scaleVec` | definition | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tri_det_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tri` | definition | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tri_det_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tri_det_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tri_det_pos` | content | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tri_det_pos` | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.x_closed` | bind-only | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.x_normal` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.y_closed` | bind-only | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.y_normal` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.x_normal` | bind-only | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.y_normal` | bind-only | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos`, `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tt_all_bound` | bind-only | none | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos` | content | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.A_pos` | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.sAux_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos` | content | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.B_pos` | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.sAux_pos` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.sAux_pos` | content | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.sAux_pos` | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.result` |
| `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.result` | content | `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.tri_det_pos` | none |

## ASSUMED-UNVERIFIED

The source/literature screen recorded in #18756 read the source PDF and HTML, Definitions 2.5 and 4.1, equations (2.10)–(2.13) and Conjecture 6.3. The search seat reported the source corrigendum (DOI 10.1017/fms.2026.10186), Dai–Deng–Shi–Wu–Yang (arXiv:2607.24541v2), arXiv:2609.01440, Okada (1994), Koekoek–Swarttouw (arXiv:math/9602214, section 3.22), and Atakishiyev–Klimyk (arXiv:math/0312312), with no proof of all shifted B determinants in that searched scope. Those later sources were not independently re-read by this implementation seat. Literature completeness and priority are `ASSUMED-UNVERIFIED`; neither the finite experiment nor the repository collision search establishes them.
