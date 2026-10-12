---
bibkey: tsukamotomoriyamasaki2026lieb
authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
year: 2026
title: Lieb-Ando trace curvature and operator power convexity in Physlib
doi: null
url: https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean
claim: Exact Physlib suppliers give general C-star power convexity on [1,2], all-Hilbert perspective convexity, and arbitrary-K joint trace convexity on positive-definite pairs, alongside Lieb concavity.
strata_touched:
  - D5/S3/Quantum/Lieb
license: Apache-2.0
triage: anchor
---

# Attributed Lieb concavity supplier

The exact Lean source is Physlib revision
`b9043cc548ef6d63a28454cf3a57fb12a0c2e142`, module
`QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LiebAndoTrace`, declaration
`LiebAndoTrace.liebTrace_jointlyConcaveOn_pdSet` at original line 1053.
The file credits Kei Tsukamoto, Kento Mori and Hayata Yamasaki, copyright
Hayata Yamasaki 2026, Apache-2.0. The full supplier license is retained at
`docs/reports/inoutbalance/physlib-LICENSE.txt`; the supplier root has no NOTICE.
The retained supplier does not include the MIT-marked HermitianMat/LiebConcavity
wrapper. Its selected matrix-to-operator trace bridge is reused only in the
transient full-matrix application, with Alex Meiburg's copyright and a full MIT
license retained alongside that application's evidence.

The mathematical result is Lieb's classical joint concavity theorem:
Elliott H. Lieb, *Convex trace functions*, Advances in Mathematics 11 (1973),
267–288, DOI <https://doi.org/10.1016/0001-8708(73)90027-9>.
No mathematical originality is claimed for this source transplant.

The transplanted endpoint ranges over a nontrivial complete finite-dimensional
complex Hilbert space, arbitrary bounded linear operator K, self-adjoint A and B
with strictly positive real spectra, and an exponent strictly between zero and
one. It imposes no commutativity assumption on the original matrices/operators.
The Hilbert–Schmidt left/right multiplication operators commute for arbitrary
A and B; their perspective evaluated against the vector represented by the
adjoint of K equals the real trace functional. The source proof applies joint
operator-perspective concavity and this positive evaluation.

The consumed source includes the strict-PD concavity and convexity endpoints.
The pinned Mathlib rpow concavity theorem directly supplies the concavity
step. The convexity step uses these exact declarations at the same pin:

- `LownerHeinzCore.lean:1427`: `convexOn_nnrpow_Ioo_one_add`, for q in (0,1),
  in ordered complex C-star algebras with Nontrivial and NonnegSpectrumClass.
  One common measure represents the entire integrable kernel
  x times rpowIntegrand01(q,t,x); constant left multiplication proves its
  integrability and identifies its integral with the power 1+q.
- `LownerHeinzCore.lean:1785`: `power_Icc_one_two_operatorConvexOn_Ici`,
  for the closed exponent interval [1,2] and nonnegative spectra, including
  zero and singular inputs. The endpoints are affinity and the square gap;
  mixed products retain their order.
- `LownerHeinzTheorem.lean:263`: `power_Icc_one_two_operatorConvexOn_Ici`,
  the direct Core specialization to every complete nontrivial complex
  Hilbert space, with no finite-dimensionality restriction. The local
  consumed PowerConvexity adapter applies the general Core supplier and
  retains the broader ConvexOn interface, including the trivial algebra.
  No additional unused Hilbert specialization is introduced.
- `OperatorGeometricMean.lean:89`: `operatorPowerMean_jointlyConvexOn_pdSet`,
  for alpha in [1,2], beta in [0,1], on every complete nontrivial complex
  Hilbert space. Its local proof consumes the equivalent all-Hilbert
  CondIciAll adapter; both inputs remain strictly positive.
- `LiebAndoTrace.lean:1118`: `liebTrace_jointlyConvexOn_pdSet`, for arbitrary
  K, 1 <= s <= 2 and strictly positive A,B on complete nontrivial finite
  complex Hilbert spaces. Its proof text is retained in LiebConcavity,
  consuming the existing unrestricted-real-exponent phiK trace bridge.

The exact paths above are relative to
`QuantumInfo/ForMathlib/HayataGroup/TraceInequality/`.
Physlib and the local source share Lean 4.33.0 and Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. The minimal Core slice uses
Mathlib's `CStarAlgebra.convexOn_ringInverse_algebraMap_add` directly in
place of upstream's omitted reciprocal-convexity chain, with the CFC
rewrite of 1/(x+t). Its positivity input uses the existing
`IsSelfAdjoint.conjugate_nonneg` API. No independent power or trace
convexity proof is authored. PowerConvexity uses the module/public-import
interface required by its source-owning OperatorGeometricMean consumer,
with the same public theorem statements. Generic full-line Jensen and the extension
trace endpoint remain outside the consumed slice.

At the implementation's input commit, all sixteen baseline D5 dependencies
were byte-unchanged and kernel-checked by the input report. The current port
extends LownerHeinzCore, OperatorGeometricMean and LiebConcavity and leaves
thirteen baseline dependencies byte-unchanged; all current versions are
covered by the fresh 22-module report. At the independent pre-admission
review checkpoint `0054c8727c7360debeadb019d54eeaa5d67506a2`, matching
Frozen records had not been established. After replaying the same reviewed
mathematical source on current dev, canonical `deposit-uncovered` admission
at `30efa46ad2633b096ebe7fbd17b36f7e3feca90b` established matching
state records for all 22 delivered modules. Native escape audit remains
unfinished under issue #5214; no declared_validated status is asserted.

Effros's 2009 PNAS perspective theorem assumes commuting operator pairs.
The arbitrary noncommuting sandwich perspective extension is recorded by
Effros and Hansen, *Non-commutative perspectives*, arXiv:1309.7701v1,
Theorem 1.1, which credits Ebadian, Nikoufar and Gordji,
*Perspectives of matrix convex functions*, PNAS 108 (2011), 7313–7314.
The 2009 proof applies to commuting Hilbert–Schmidt left/right superoperators
without requiring original A and B to commute.

The strict-PD endpoint was compiled and inspected with the canonical scoped
report. Its exact finite-matrix application was separately compiled for arbitrary
PSD A1, A2, B1, B2, arbitrary K, p and t in [0,1], and every finite decidable
index type, including the empty type, with no A/B commutativity hypothesis.
For T_p(A,B) = Re Tr(K* A^p K B^(1-p)), the result is
(1-t) T_p(A1,B1) + t T_p(A2,B2) ≤
T_p((1-t) A1 + t A2, (1-t) B1 + t B2).
The powers use the spectral CFC convention, including A^0 = I on the PSD cone.
The interior proof applies the strict-PD supplier to A + epsilon I and B +
epsilon I and uses `CFC.continuousOn_nnrpow` on the full PSD cone to take the
limit. At p=0 and p=1 the functional is linear in B and A, respectively; the
empty carrier has zero trace. Both results have exactly the standard three
axioms `propext`, `Classical.choice`, and `Quot.sound`.
The full application is bind-only reuse: its transient D5 source is removed
after source, hashes, build terminal receipt and scoped report are saved in
`/Users/macstudio/omega/research/operator-perspective-lieb-continuation-20261011`.
Its exposition remains in the owning LiebConcavity Scribe. No trace-exponential
consequence is asserted here.

Retire each transplanted supplier when an equivalent consumed
result is available in this repository's pinned Mathlib and replace it by a
direct application; a hypothetical future upstream merge is not the
retirement criterion.

## Verified locator

https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean
