---
bibkey: diem2026traceclass
authors: Tom Ole Diem
year: 2026
title: Analytic trace-class and Hilbert-Schmidt operators
doi: null
url: https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass
claim: Analytic basis-independent trace, Hilbert-Schmidt square sums, polar factorization, the two-sided trace-class ideal, trace-norm Banach structure, cyclicity, and continuous trace pairing for arbitrary complex Hilbert spaces.
strata_touched:
  - D5/S3/Quantum/Analysis/TraceClass/Basic
  - D5/S3/Quantum/Analysis/TraceClass/HilbertSchmidt
  - D5/S3/Quantum/Analysis/TraceClass/Polar
  - D5/S3/Quantum/Analysis/TraceClass/GeneralIdeal
  - D5/S3/Quantum/Analysis/TraceClass/GeneralProduct
  - D5/S3/Quantum/Analysis/TraceClass/IdealNorm
  - D5/S3/Quantum/Analysis/TraceClass/Banach
  - D5/S3/Quantum/Analysis/TraceClass/TraceAlgebra
  - D5/S3/Quantum/Analysis/TraceClass/Pairing
  - D5/S3/Quantum/Analysis/TraceClass/ColumnSynthesis
  - D5/S3/Quantum/Analysis/TraceClass/Compact
  - D5/S3/Quantum/Analysis/DiagonalEnergy
license: Apache-2.0
triage: anchor
---

# Analytic trace suppliers

## Verified locator

The immutable source directory declared above is:
https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass

The locators identify the supplied analytic statements. They do not attribute
the weighted-column construction or the logarithmic regularization joins to the
supplier.

| Supplied module | Immutable source and declaration | Attested scope |
| --- | --- | --- |
| Basic | [Basic.lean](https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass/Basic.lean#L434), `trace_eq_of_hilbertBasis_of_nonneg` | The actual trace equals the Hilbert-basis sum for a positive trace-class bounded operator. |
| HilbertSchmidt | [HilbertSchmidt.lean](https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass/HilbertSchmidt.lean#L254), `HilbertSchmidt.tsum_mul_le_sqrt_mul_sqrt` | Cauchy-Schwarz for the two summable real square sums indexed by a set of the Hilbert space. |
| Polar | [Polar.lean](https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass/Polar.lean#L181), `Polar.polarFactor_mul_absOperator` | The bounded polar factor times the positive absolute-value operator is the original bounded operator. |
| GeneralIdeal | [GeneralIdeal.lean](https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass/GeneralIdeal.lean#L98), `trace_eq_of_hilbertBasis` | The actual trace-basis identity for an arbitrary trace-class bounded operator. |
| GeneralProduct | [GeneralProduct.lean](https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass/GeneralProduct.lean#L52), `isTraceClass_mul_of_isHilbertSchmidt` | The product of two Hilbert-Schmidt bounded operators is trace class. |

| IdealNorm | [IdealNorm.lean](https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass/IdealNorm.lean), `traceNorm_mul_mul_le` | The two-sided trace-norm ideal estimate. |
| Banach | [Banach.lean](https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass/Banach.lean), `TraceClass.isTraceClass_of_tendsto_of_traceNorm_bounded` | The genuine trace-class Banach space. |
| TraceAlgebra | [TraceAlgebra.lean](https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass/TraceAlgebra.lean), `trace_mul_cycle` | Cyclicity with a bounded factor. |
| Pairing | [Pairing.lean](https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass/Pairing.lean), `TraceClass.tracePairingContinuousLinearMap_apply` | The continuous observable trace pairing. |

## Adoption and consumer

The nine source modules are adopted from immutable Physlib revision
`b9043cc548ef6d63a28454cf3a57fb12a0c2e142`, under
`PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass/`. The source archive
was checked byte-for-byte against that revision. Project import paths and the
required project headers are adapted; the supplied proofs remain unchanged.
The original Tom Ole Diem copyright and Apache-2.0 notices are preserved.
Full license: `docs/reports/quantum-hs-suppliers/physlib-LICENSE.txt`.
The source archive contains no NOTICE-named file. The public finite-dimensional
compatibility declarations do not replace the analytic trace consumed here.

The live consumer is `QuadraticReferenceHilbertSchmidtBridge`. Its direct
square-summable-column construction and concrete inverse-domain/trace joins
are distinguished from the supplied scalar Cauchy-Schwarz, genuine trace-basis
formula, square-root Hilbert-Schmidt property, polar factor, and ideal facts.
No originality is claimed for the adopted suppliers. Replace each transplant
with direct application when an equivalent live result exists in the
repository's own pinned Mathlib.

The logarithmic regularizations also use `IdealNorm`, `Banach`, `TraceAlgebra`
and `Pairing`. In particular, bounded-factor cyclicity is applied to
`sqrt A * rho`, which is genuinely trace class by the ideal property, to obtain
positive trace pairing without a commutation hypothesis. The trace-class
Banach carrier retains its trace norm; the continuous observable pairing uses
the operator norm. These are standard analytic suppliers, not an originality
claim about operator logarithms or spectral entropy.
## Column synthesis and compactness

The repository's `TraceClass/ColumnSynthesis` constructs the continuous operator
with any square-summable family of basis columns. Its vector-series bound uses
the attributed scalar Cauchy-Schwarz supplier and Mathlib Parseval. The same
construction supplies both the weighted quadratic-reference operator and the
residuals in `TraceClass/Compact`; it is not an additional Physlib transplant.

For a finite subset F of the arbitrary basis index, the existing Schauder
projection P_F has range equal to the finite span of the selected basis vectors.
The approximant S composed with P_F is compact, and the actual operator-norm
residual squared is bounded by the complement-subtype column square sum.
Summability makes these tails converge to zero along all finite subsets,
proving Hilbert-Schmidt compactness on arbitrary complete complex Hilbert spaces.
The analytic trace-class square-root supplier and actual CFC square identity
then prove positive trace-class compactness. The attributed bounded polar
factorization extends compactness to general trace-class operators.

This is a repository formal derivation of the standard finite-rank approximation
argument, not a claim of a new compactness theorem in mathematics. It retains
uncountable indices and zero kernel fibers and supplies no spectral-basis,
unbounded-energy, heat-trace or common-Hamiltonian conclusion.

The diagonal resolvent energy consumer uses GeneralProduct's actual ideal
product and GeneralIdeal's unconditional trace formula for C_m times rho.
This product need not be self-adjoint. An injective full-basis range equivalence
transports the arbitrary index to the Set H telescope. The real and complex
diagonal HasSum statements precede the monotone extended-energy limit. These
are applications of the attributed trace suppliers to the actual resolvent
construction, without a commutation or trace-cyclicity assumption.
