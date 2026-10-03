---
slug: starke-2025-qudit-swapping-product-bound-refutation
bibkey: starke2025swapping
doi: 10.48550/arXiv.2508.00813
url: https://arxiv.org/abs/2508.00813v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.result
---

# The improved entanglement-swapping product bound fails in dimension four

## Problem

D. S. Starke, M. L. W. Basso, L. C. Céleri and J. Maziero,
“Entanglement swapping for partially entangled qudits and the role of quantum
complementarity”, arXiv:2508.00813v2, p. 8, Eq. (59), conjecture:

> Therefore, we conjecture that the improved upper bound has the form
> $\big\langle E_{l_1}\big(|\hat{\phi}_{pq}^{AB}\rangle\big)\big\rangle
> \le \frac{E_{l_1}(|\xi\rangle_{AC})E_{l_1}(|\eta\rangle_{C'B})}{d-1}.$

For every dimension $d\ge2$, the inputs are
$|\xi\rangle_{AC}=\sum_jc_j|jj\rangle$ and
$|\eta\rangle_{C'B}=\sum_kb_k|kk\rangle$, with
$\sum_j|c_j|^2=\sum_k|b_k|^2=1$; the paper's second coefficient $d_k$ is renamed
$b_k$. The measure is the unscaled ordered sum
$E_{l_1}(a)=\sum_{j\ne k}|a_ja_k|$.

The Bell outcome $(p,q)$ gives
$\phi_{pq}=d^{-1/2}\sum_kc_{p\oplus k}b_k\bar\omega^{qk}|p\oplus k,k\rangle$,
where $\omega=\exp(2\pi i/d)$ and $\oplus$ is addition modulo $d$.
Its probability is its squared Hilbert norm; its normalized state is obtained
by dividing by that norm. The average includes all $d^2$ outcomes, with
zero-probability outcomes contributing zero. Each conditional state is in
Schmidt form, since $k\mapsto p\oplus k$ is a bijection.

## Motivation

The frozen declaration
`D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.result`
refutes the universally quantified improved bound using two identical
normalized ququarts. It distinguishes the proposed dimension-dependent factor
from the paper's unscaled product bound and its exact low-dimensional results.

## Gap

Issue #11499 preregisters this Tier 1 conjecture, the complete quantified
reading and the dimension-four witness before any Lean implementation.
Its literature check reports no settlement in the searched scope: the arXiv v2
retains the conjecture; Semantic Scholar reports zero citing works; the search
seat identifies arXiv:2605.26375 as citing the unscaled product bound, rather
than settling Eq. (59); the MathDB queries find no matching problem.
The latter citation reading is search-seat reported. These bounded checks do
not establish worldwide priority or exclude an independent settlement.

## Route

The Lean definitions encode the Bell phase, the delta-function conditional
state, its Hilbert norm, its probability, the Schmidt-form entanglement and
the probability-weighted average directly. A local `have` inside `result`
establishes, for every positive dimension and every complex coefficient pair,

$$\operatorname{averageEl1}(d,c,b)
=\sum_p\sum_{j\ne k}|c_{p+j}c_{p+k}b_jb_k|.$$

The phase has modulus one. When the probability is nonzero, normalization
cancels the probability; when it is zero, the nonnegative sum of squared
supported coefficients forces every contributing product to vanish. Summing
over $q$ removes the factor $1/d$.

For $d=4$ and $c=b=(7/10,1/10,7/10,1/10)$, exact arithmetic gives both
normalizations equal to $1$, both input entanglements equal to $39/25$, and
average $723/625$. The proposed bound is $(39/25)^2/3=507/625$.

## Falsifier

The witness violates the printed bound by $216/625$. A bound whose right-hand
side is at least $723/625$ at this witness would not be refuted by this result.
The result asserts failure of a universal inequality, rather than failure for
every input or every dimension.

## Evidence

The canonical Lean source is
`D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.lean`.
The sole public theorem is `result : ¬ claim`; the seven public definitions
are `omega`, `phi`, `stateNorm`, `prob`, `El1`, `averageEl1` and `claim`.
The general correlation identity and the normalized rational witness are on
its live proof path. The Scribe mirror displays all eight public declarations
and attaches a Refuted open-problem resolution to `result`.

## Triage

Tier 1 external named conjecture; `theorem`, resolution Refuted.
`admission_basis: open-problem-resolution`, with preregistration #11499.
The sole theorem `result` has `proof_shape: bind-only` and
`escape_witness: none`: instantiation and normalization of pinned Mathlib
facts establish Bell-state support, handle the zero-probability branch and
evaluate the rational witness. Utility is a certified-instance refutation of
the explicitly encoded `claim`. There is no digestion atom or cover step.

### What the settlement shows

- **Proved in this module:** Eq. (59) is false. Two identical normalized
  partially entangled inputs in dimension four give $723/625>507/625$.
- **Established locally in the proof of `result`:** the average is a modular
  correlation sum for every positive dimension, including zero-probability outcomes.
  The failure mechanism is concentration of the input off-diagonal products
  along modular shifts; normalization and Bell-outcome probabilities do not
  supply the conjectured factor $1/(d-1)$.
- **Computed independently:** the exact ordered correlation sum, evaluated
  by `python3` with the command below over $p,j,k\in\{0,1,2,3\}$,
  gives the same average and bound. The ratio of average to input product at
  this witness is $241/507$, exceeding $1/3$. For the fixed pair $(j,k)=(0,2)$, the shifted sum is $1$, exceeding $E_{l_1}(c)/(d-1)=13/25$; this is the pointwise replacement proposed in the paragraph after Eq. (59).
- **Literature-attested, not additional Lean results:** the paper's exact
  qubit and qutrit formulas, Eqs. (48) and (57), and its general unscaled
  product bound, Eq. (43), are separate statements. The witness satisfies
  Eq. (43), since $723/625<1521/625$; it does not contradict those statements.
- **Open:** the optimal dimension-four constant, the dimensions and input
  classes supporting an improved bound, and any dimension-uniform sharp
  replacement are not settled here. Any application using Eq. (59) for
  arbitrary dimensions needs an independently justified replacement;
  the normalized dimension-independent version immediately after Eq. (59) also fails at this witness: its average is $241/625$, while its product bound is $169/625$ (computed below). Source conclusions independent of Eq. (59) are not refuted by this theorem.

The independent exact-value command is:

```sh
python3 - <<'PYCODE'
from fractions import Fraction as F
c = [F(7,10), F(1,10), F(7,10), F(1,10)]
e = sum(c[j]*c[k] for j in range(4) for k in range(4) if j != k)
a = sum(c[(p+j)%4]*c[(p+k)%4]*c[j]*c[k]
        for p in range(4) for j in range(4) for k in range(4) if j != k)
shift = sum(c[p]*c[(p+2)%4] for p in range(4))
print(a, e*e/3, a/(e*e), shift, e/3, a/3, (e/3)**2)
PYCODE
```

Output: `723/625 507/625 241/507 1 13/25 241/625 169/625`.

## ASSUMED-UNVERIFIED

The journal version's retention of Eq. (59) is search-seat reported and not
verified by this delivery. The target is the explicitly cited arXiv v2.
The bounded literature check does not establish exhaustive novelty or priority.
The Lean kernel does not authenticate external publication metadata.
Information-escape registration is paused under CLAUDE.md §3.9
（信息逃逸登记暂缓）. No Reg registration is claimed.
