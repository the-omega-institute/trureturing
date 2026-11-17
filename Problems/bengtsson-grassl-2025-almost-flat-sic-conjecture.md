---
slug: bengtsson-grassl-2025-almost-flat-sic-conjecture
bibkey: bengtssongrassl2025almostflat
doi: null
url: https://arxiv.org/abs/2512.13201
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.IsSICFiducial
---

# The almost flat SIC X-overlap equation

## Problem

Bengtsson and Grassl conjecture that every almost flat SIC fiducial in every
odd dimension satisfies equation (8):

$$\langle v|X^{-2j}|v\rangle=(\sqrt{d+1}+1)v_j^2\quad(j\ne0).$$

The almost flat ansatz, normalization and shift convention are the source's
equations (1), (3), (4) and (5), quoted in the [literature note](../Library/FiniteGeometry/bengtssongrassl2025almostflat.md).
The statement is preregistered in issue
[#30316](https://github.com/the-omega-institute/trureturing/issues/30316).

## Motivation

The equality determines the phases of all nontrivial even-shift overlaps
from the fiducial coordinates. It strengthens their SIC modulus equations.

## Gap

The required inference connects the SIC modulus equations to the coordinate
phases. The target quantifies over all odd dimensions, without assuming primality,
existence of a fiducial in each dimension, or any extra symmetry.

## Route

Set $s=\sqrt{d+1}$, $C=s+1$, $L=d+1+s=sC$. Character orthogonality contracts
the squared displacement overlaps to

$$G(j)=\sum_r\overline{v_{r+j}}^{\,2}v_rv_{r+2j}
=2C^2\,[j=0].$$

Reflection gives $A_k=-\sum_rv_rv_{2k-r}$. Midpoint reindexing then gives
$\sum_jG(j)=-\sum_k\overline{v_k}^{\,2}A_k$.
The zero term is $-(s+2)L$, so the sum over nonzero $k$ is $C(d-1)$.
For odd $d$, every such $-2k$ is nonzero, and the SIC condition gives $|A_k|=C$.
Consequently

$$\sum_{k\ne0}|A_k-Cv_k^2|^2
=2C^2(d-1)-2C\operatorname{Re}\sum_{k\ne0}\overline{v_k}^{\,2}A_k=0.$$

Each summand vanishes. At $d=1$ there is no nonzero $j$.

## Falsifier

A normalized SIC satisfying the exact almost flat ansatz in an odd dimension
but violating one X-overlap equality would refute the target. A different
choice of the imaginary zeroth component or of the shift convention is outside
the encoded statement.

## Evidence

The proof source is `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.lean`.
The exact target is `result`; its coordinate-sum bridge is `overlap_sum`.
The scoped Lean report for this D5 module exits zero. The target's axiom closure
is exactly `Classical.choice`, `Quot.sound` and `propext`.
The module is a frozen ledger member. The thirteen theorem registrations,
including `result`, are `declared_validated` in the joint D5/Reg scoped report.
The nonvacuous audit witness is $d=3$, $v=i(2,-1,-1)$ and $j=1$.
`Reg/Support/AlmostFlatSICQutrit.lean` proves its exact almost-flat and normalized
SIC premises; the result registration consumes both proofs.

## Triage

The mechanism is diagonal quartic contraction followed by equality in the
triangle bound, expressed as a sum of nonnegative squared phase errors.
Only the diagonal contraction of the SIC quartic identity and the nonidentity
X-overlap moduli are used. The universal target has `utility: none`.

| Declaration | proof_shape | Live consumer |
| --- | --- | --- |
| shift_pow_mulVec | bind-only | overlap_sum |
| displacement_overlap_sum | bind-only | diagonal_quartic |
| spectral_autocorrelation | bind-only | diagonal_quartic |
| diagonal_quartic | bind-only | result |
| overlap_sum | bind-only | result |
| conjugate_reflection | bind-only | overlap_convolution |
| coordinate_norm_sq | bind-only | squared_norm |
| squared_norm | bind-only | sic_overlap_squares, result |
| sic_overlap_squares | bind-only | result |
| overlap_convolution | bind-only | midpoint_contraction |
| midpoint_contraction | bind-only | result |
| phase_saturation | bind-only | result |
| result | bind-only | external open-problem resolution |

The auxiliary declarations organize the finite-sum computations and are
consumed by the target's proof. The target's admission basis is
`open-problem-resolution`; no new mathematical primitive is claimed for
the auxiliary algebraic and orthogonality computations.

### What the settlement shows

The intended conclusion is exactly the odd-dimensional forward implication.
The source's Legendre-vector counterexamples to its converse are unaffected.
Even-dimensional equations (94)-(95) and the phase-convention difference from
equation (92) of arXiv:2112.05552 are outside this conclusion. No assertion of
existence in every odd dimension follows from the conditional universal theorem.

## ASSUMED-UNVERIFIED

External quotations and the reported status of the converse are supplied by the
brief; they have not been retrieved independently. Worldwide novelty and priority
are not established by the local library search.
