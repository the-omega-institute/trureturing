---
bibkey: tsukamotomoriyamasaki2026lieb
authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
year: 2026
title: Lieb joint trace concavity in Physlib
doi: null
url: https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean
claim: For arbitrary K, the real trace of A to exponent s times the adjoint of K times B to exponent one minus s times K is jointly concave on positive-definite pairs for zero less than s less than one.
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

The intake retains only the strict-PD concavity endpoint and its supporting
local modules. The pinned Mathlib rpow concavity theorem supplies the consumed
power-function concavity step directly; the superseded upstream reciprocal,
integral and convex-power proofs are not copied. Generic full-line Jensen,
Ando convexity and the extension trace endpoint are outside this intake.
The source is split between LiebBridge and LiebConcavity solely to satisfy
ordinary artifact capacity. The consumed original private bridge declarations
are made visible; their mathematical statements and proof text are retained.
All source headers retain the immutable revision and attribution.

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
