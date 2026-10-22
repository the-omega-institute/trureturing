---
slug: verhagen-tomamichel-haapasalo-2025-flat-pair-endpoint-homomorphisms-remark-15
bibkey: verhagen2025flatpairendpoints
doi: 10.1007/s00220-026-05675-5
url: https://arxiv.org/abs/2507.07520v3
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.result
---

# Endpoint homomorphisms of everywhere overlapping flat pairs

## Problem

Verhagen, Tomamichel and Haapasalo, *Conditions for Large-Sample Majorization of
Pairs of Flat States in Terms of α-z Relative Entropies*, arXiv:2507.07520v3,
Remark 15, p. 21, ask:

> Namely, it is still an open question whether the homomorphisms for 𝕂 = ℝ₊ or ℝ₊ᵒᵖ that have the same form as (84), but with parameters α = 0, z < 1, or α = 1, z < 1, are monotone or not. The same question of monotonicity can also be asked for the homomorphisms for 𝕂 = 𝕋ℝ₊ that are similar to (85), but with z < 0.

> We suspect that these additional homomorphisms are in fact not monotone either, since they correspond to parameters α, z for which the α-z relative entropy is known not to satisfy DPI for general pairs of quantum states (with some conditions on the support).

The settled claim excludes $z=0$, which the source treats as the degenerate
trace maps. It asserts failure of both real target orders for every
$\alpha\in\{0,1\}$ and every real $z<1$, $z\ne0$, and failure of the ordinary
tropical order for every real $z<0$.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Eq. (31): finite direct sums of two rank-one block matrices; vectors may vanish | `FlatPair`, `FlatPair.A`, `FlatPair.B` | Arbitrary finite block counts and dimensions; sigma indices are written directly |
| Eqs. (33)–(34): nonzero overlap or both block vectors zero | `FlatPair.IsEverywhereOverlapping` | Every block, including zero blocks |
| Eq. (37): weights and normalized overlaps | `FlatPair.p`, `FlatPair.q`, `FlatPair.overlapSq` | Unnormalized vectors, real self-dot-product weights |
| One channel acts on both matrices | `Majorizes` | Existing completely positive trace-preserving `QuantumChannel` |
| Eqs. (84)–(85) | `Phi`, `PhiT` | Zero blocks contribute zero; the maximum starts at zero |
| Both real target orders | `IsMonotone`, `IsMonotoneOp` | The same channel preorder and everywhere-overlapping domain |
| Endpoint suspicion, excluding trace maps | First conjunct of `claim`, proved by `result` | All real parameters $\alpha\in\{0,1\}$, $z<1$, $z\ne0$ |
| Negative tropical suspicion | Second conjunct of `claim`, proved by `result` | Every real $z<0$ in the ordinary tropical order |

## Motivation

The question concerns channels whose input and output remain in the restricted
flat-pair domain. Counterexamples for general pairs do not by themselves settle
this restriction. The orthogonal flag keeps the filter outcomes in distinct
flat blocks, so the channel witness remains inside the required domain.
The preregistered statement and source checks are in
[#19032](https://github.com/the-omega-institute/trureturing/issues/19032).

## Gap

Remark 15 states the suspicion rather than a proof. Verhagen's thesis,
arXiv:2610.16267v1, Remark 4.12, repeats the question. The literature screen in
#19032 records no settlement in the works it examined; completeness is
`ASSUMED-UNVERIFIED`.

The settlement declaration is
`D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.result`.
Its admission basis is `open-problem-resolution (#19032; Proved)`.

## Route

The input has one block with squared normalized overlap $1/2$ and weights $1,1$.
A complete two-operator Kraus family produces two orthogonal blocks with
first weights $1/4,3/4$, second weights $1/2,1/2$, and squared normalized overlaps
$1/4,3/4$. Both pairs are everywhere overlapping. The proof applies
`D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel`
to the displayed complete Kraus families.

For $\alpha=0$, the scalar values are
$\Phi_{0,z}(x)=(1/2)^z$ and
$\Phi_{0,z}(y)=((1/4)^z+(3/4)^z)/2$.
Strict concavity for $0<z<1$ and strict convexity for $z<0$ give opposite strict
inequalities. Erasure sends the input to a one-dimensional pair with value
$1$, giving the other failed order in each range. Swapping the two matrices
transfers the argument to $\alpha=1$. For $z<0$, the tropical value increases
from $(1/2)^z$ to $(1/4)^z$.

## Falsifier

A failure of a Kraus completeness identity, either channel-image identity, the
everywhere-overlapping conditions, or the quantified strict inequalities would
invalidate this argument. The Lean statement retains both real orders and all
real parameters in the specified ranges. The finite numerical grid is a check
of examples and does not establish those universal quantifiers.

## Evidence

The Lean source is
`D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.lean`, with its corresponding
Blueprint Scribe. `result : claim` proves both quantified conjuncts.
The public result has `proof_shape: bind-only` and `escape_witness: none`;
the external named open-problem resolution supplies its admission basis.
Private scalar, matrix, channel and swap lemmas are consumed by that proof.

The escape audit of
`D5.S3.QuantumChannels.FlatPairEndpointHomomorphisms.result` is unfinished under
[#19845](https://github.com/the-omega-institute/trureturing/issues/19845).
No faithful typed registration is supplied: the conjunction of universally
quantified negated monotonicity predicates still needs a theorem-independent
source/readout reconstruction, exact realization bridge, whole-family
variation, sensitivity and observational-dependence evidence.

Experiment: [pinned program and data](https://github.com/the-omega-institute/trureturing-experiments/tree/e109e9f0a6c94629086b516b3976321bd1c0e8a3/docs/reports/verhagen-tomamichel-haapasalo-2025-endpoint-homomorphisms-not-monotone).
Command: `python3 /Users/auric/trureturing-experiments/docs/reports/verhagen-tomamichel-haapasalo-2025-endpoint-homomorphisms-not-monotone/check.py`.
Exit code: 0; final result: `RESULT PASS 0`.
The SHA-256 of `check.py` is
`5d6af1332f2a096d3ad33598ade83488e8622b28cde2559c2ccf2b28894d4520`.
It checks both Kraus families and their images exactly, the weights and squared
overlaps, and erasure. Its numerical parameter check uses
$z\in\{-5,-4.95,\ldots,0.95\}\setminus\{0\}$ (119 values), both endpoint
parameters, and the negative subset for the tropical map. The exact sample
values are $\sqrt2/2\mapsto(1+\sqrt3)/4$ at $z=1/2$,
$2\mapsto8/3$ at $z=-1$, and $2\mapsto4$ for the tropical map at $z=-1$.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Settlement under the exact binding claim | Proved; kernel-checked `result` | Both endpoint orders fail for all $z<1$, $z\ne0$, and the ordinary tropical order fails for all $z<0$ |
| Decisive mechanism | Proved in prose; the Route derivation | Orthogonal flags split the overlap $1/2$ into $1/4,3/4$ while preserving the required domain; strict Jensen inequalities and erasure give opposite directions; swap gives the other endpoint |
| Parameter scope | Proved; kernel-checked `result` | All quantified real parameters, with no finite-grid restriction |
| Exact finite witnesses and sample gaps | Computed; the pinned experiment above | Kraus completeness, images, weights and overlaps, 119 grid values, and the stated exact samples; this computation asserts no uniform extension |
| Tropical opposite-order case | Open | No conclusion about monotonicity into $\mathbb T\mathbb R_+^{op}$ |
| Monotone derivations | Open | The derivation question in Remark 15 is outside `claim` |
| Independent full classification theorem | Open | No Lean declaration formalizes Proposition 13's exhaustive classification |
| The $z=0$ trace-map theorem beyond source context | Open | The source identifies $\operatorname{tr}B$ and $\operatorname{tr}A$; this module excludes $z=0$ and does not separately prove the trace-map identity |
| Consequence for the source classification | Proved in prose, conditional on the source's classification argument | Under the source's nondegeneracy and trivial-kernel hypotheses, Proposition 13 and Remark 15's enumeration leave the additional endpoint and negative tropical candidates of Remark 15; `result` excludes those nondegenerate candidates in the three stated target orders. This combination is not an independently kernel-checked classification theorem |
| Other source results | Proved in source; paper argument | Proposition 13's positive monotonicity results remain applicable; the tropical opposite order and monotone derivations retain their stated open boundaries |
| Literature status | Literature reading reported in #19032 | The paper and thesis state the question; no settlement is recorded in the examined citing works; completeness is `ASSUMED-UNVERIFIED` |

The witnesses already use input dimension two and flagged output dimension
four. The proved ranges are precisely those of `claim`; relaxed hypotheses,
sharpness outside those ranges, and additional classification results are not
asserted here.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The source and literature
checks recorded in #19032 are attributed to its search seat and orchestrator:
arXiv:2507.07520v3; arXiv:2610.16267v1, Remark 4.12; arXiv:2509.18725 and the
titles and abstracts of 2608.21214, 2608.27202, 2601.19182 and 2607.27015;
`google-deepmind/formal-conjectures` with no match. Native MathDB was not accessed
because its request returned HTTP 403. This list is a bounded literature screen,
not evidence that no other settlement exists.
