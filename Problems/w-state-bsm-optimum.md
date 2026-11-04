---
slug: w-state-bsm-optimum
bibkey: chakrabartykundu2026network
doi: 10.48550/arXiv.2610.35838
triage: theorem
motivation_gids:
  - D5/S3/Quantum/MeasurementGeometry/WStateBellMeasurementOptimum.result
url: https://arxiv.org/abs/2610.35838v1
---

# Exact W-state Bell-state-measurement optimum

## Problem

For the normalized state $W=(|001\rangle+|010\rangle+|100\rangle)/\sqrt3$,
prove that the two-frame, four-index variational quantity in Proposition 1 of
Chakrabarty–Kundu, arXiv:2610.35838v1, is $\mathcal N_c(W)=\sqrt{13}/3$.
The source gives this value as a lower bound and reports no larger numerical
value. The preregistration is [#23251](https://github.com/the-omega-institute/trureturing/issues/23251).

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| $W=(\lvert001\rangle+\lvert010\rangle+\lvert100\rangle)/\sqrt3$ | Literal ket in `tau`, with density `Matrix.vecMulVec w (star w)` | Exact normalized complex ket |
| $A_i=e_i\cdot\sigma$, $C_j=f_j\cdot\sigma$, $A_0=C_0=I$ | The two branches and three-coordinate Pauli sums in `tau` | Index zero is included |
| $\tau_{\mu\nu}=(\operatorname{Tr}[\rho A_\mu\otimes\sigma_k\otimes C_\nu])_k$ | `tau` | Tensor order: Alice, end node, Charlie; real part of trace |
| Orthogonal unit $n,n'$ maximize the sum of two squared scalar products | `lambda` | Both norm-one guards and the orthogonality guard are explicit |
| Both complete orthonormal frames and all $\mu,\nu,\mu',\nu'\in\{0,1,2,3\}$ | `claim` and `result` | All frames, zero indices and repeated index pairs |
| Exact value $\sqrt{13}/3$ | `result : claim` | Suprema represent the variational maxima; attainment is proved |

The displayed natural predecessor in `tau` is literal; the private
`index_correspondence` relates it to `Fin.predAbove` for the proof. The Pauli
matrices are the existing `SicKFidelityPauliWeight.pauli1`. No extra physical
hypothesis is added. The reduction from the Bell-network experiment to this
variational quantity is Proposition 1 of the source and is not formalized here.

## Motivation

The frozen settling declaration is
`D5/S3/Quantum/MeasurementGeometry/WStateBellMeasurementOptimum.result`.
Its public surface consists of `tau`, `lambda`, `claim` and `result`.
The module uses `admission_basis: open-problem-resolution (#23251; Proved)`;
the proof classification after expansion is `bind-only`, with no escape witness.

## Gap

The source supplies the attaining standard-frame correlations but does not
give the uniform upper bound over arbitrary pairs of complete frames.
The result closes this mathematical optimization gap. It does not optimize
the larger product-projective class.

## Route

For unit $a,c$, put $D=\operatorname{diag}(2,2,-1)$. The private
`quadratic_identity` proves
$9\|T(a,c)\|^2=(a^TDc)^2+4a_z^2+4c_z^2$.
The proof applies the published owner `EightVertexQutritBound.parseval_three`
to complete frames, `EightVertexQutritBound.bessel_pair` to repeated correlation
pairs, and `HiaiRuskaiRiemannianContraction.Pinching.cauchy_three` to the
three-coordinate Cauchy bound.

The index cases give $\Lambda\le13/9$: identity-index vectors have squared
length at most $4/9$; arbitrary correlation vectors have squared length at
most one; repeated nonidentity pairs satisfy Bessel's bound. One changing
index is bounded by a row Parseval estimate. When both change,
`projection_trace` bounds the selected entries using the complementary frame
directions, and `triple_pair_distinct` gives the required bound.
The standard frames attain $13/9$. Taking the nonnegative square root proves
`result`.

## Falsifier

A frame/index choice with $\Lambda>13/9$ would contradict the private
`pair_upper_bound`. A failure of the literal ket, Pauli order, tensor order,
or any orthogonality guard would instead invalidate the statement echo.
The complete statement includes identity and repeated central indices.

## Evidence

The Lean declarations below are in
`D5.S3.Quantum.MeasurementGeometry.WStateBellMeasurementOptimum` unless an
owner is explicitly named. The private proof declarations are part of the
same compiled module; they introduce no additional public statements.

### Exact finite computation

The [experiment directory at commit 3e3d376e925060a7fa7e3a299ae6e2f7b98edfa0](https://github.com/the-omega-institute/trureturing-experiments/tree/3e3d376e925060a7fa7e3a299ae6e2f7b98edfa0/docs/reports/wbsm-2610)
contains `check.py`. Its SHA-256 is
`aac9922feda7ca6dc2a991f15dcfce11a266be5d9b4df051a9c92d89ddb317a2`.
The command
`git -C /Users/auric/trureturing-experiments show 3e3d376e925060a7fa7e3a299ae6e2f7b98edfa0:docs/reports/wbsm-2610/check.py | python3 -`
exits 0 and ends `ALL_CHECKS_OK`. It checks 256 Cartesian index pairs,
36 rational-unit identity pairs, and white-noise scaling for four index
pairs. These finite checks supplement the universal Lean proof.

## Triage

| Item | Status | Evidence kind and exact scope |
| --- | --- | --- |
| W-specific quadratic identity and complete-frame Parseval bounds give the exact frame/index supremum and square-root optimum | proved | Kernel-checked: private `quadratic_identity`, `projection_trace`, `pair_upper_bound`, `squared_optimum`, and public `result` |
| Standard correlations $\tau_{33}=-\hat z$, $\tau_{13}=(2/3)\hat x$, with orthogonal attainment | proved | Kernel-checked: private `tau_std_33`, `tau_std_13`, `orthogonal_equality`, `attainment` |
| Generic $\Lambda$ upper bound and equality for orthogonal vectors with nonzero norm roots | proved | Kernel-checked: private `lambda_le_normSq_add`, `orthogonal_equality`; nonzero roots are explicit hypotheses |
| Exact checker: 256 Cartesian index pairs, 36 rational-unit identity pairs, white-noise scaling for four checked index pairs | computed | The immutable experiment, command, exit 0, SHA-256 and final reading above; no uniform noisy-state claim |
| Lean extension to noisy states and the larger product-projective class | open | Neither extension is included in `claim` or the module's theorem |

### What the settlement shows

The decisive mechanism is the W-specific quadratic identity combined with
complete-frame Parseval bounds. The constant is sharp because the standard
frames attain $13/9$ before the square root. The generic orthogonal-vector
equality allows arbitrary real vectors with nonzero real norm roots; it is
not restricted to the attaining W-state vectors. Those facts are
kernel-checked by the declarations named in the table.

The noisy-state scaling tested by the checker is a finite computed result.
A Lean theorem for the full noisy-state family and the larger
product-projective optimum remain open. The source's other state-specific
results retain their stated scopes; no new conclusion about them is asserted.

### Literature status

The bounded screen in #23251 covers arXiv identifier/title and author
searches, OpenAlex, Crossref, Semantic Scholar, Zenodo, OEIS and the named
Lean corpora. The AFTD search scope contains formalized equations
from the same paper but no located Proposition 1 W optimum. Rate-limited citation
queries and unread related papers prevent an exhaustive literature claim.
Completeness is `ASSUMED-UNVERIFIED`.

### Escape audit

The escape audit is unfinished under
[#25122](https://github.com/the-omega-institute/trureturing/issues/25122)
for `result` and the published owners `parseval_three`, `bessel_pair` and
`Pinching.cauchy_three`. The examined enrolled equality and dependent-family
templates require faithful realization/equivalence bridges and variation,
sensitivity and observational-dependence evidence. No Reg source or
`declared_validated` registration is claimed.

## ASSUMED-UNVERIFIED

Literature-screen completeness; the physical network-to-variational
reduction cited from Proposition 1; and the unfinished four-slot escape
audit are explicit boundaries. The theorem proves the displayed mathematical
variational optimum. Advisory helper-deletion and exact-search completeness
remain unverified; no exhaustive absence-of-owner claim follows.
