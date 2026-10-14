---
bibkey: diem2026traceclass
authors: Tom Ole Diem
year: 2026
title: Analytic trace-class and Hilbert-Schmidt operators
doi: null
url: https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass
claim: Analytic basis-independent trace, Hilbert-Schmidt square sums, polar factorization, and the two-sided trace-class ideal for arbitrary complex Hilbert spaces.
strata_touched:
  - D5/S3/Quantum/Analysis/TraceClass/Basic
  - D5/S3/Quantum/Analysis/TraceClass/HilbertSchmidt
  - D5/S3/Quantum/Analysis/TraceClass/Polar
  - D5/S3/Quantum/Analysis/TraceClass/GeneralIdeal
  - D5/S3/Quantum/Analysis/TraceClass/GeneralProduct
license: Apache-2.0
triage: anchor
---

# Analytic trace suppliers

## Verified locator

The immutable source directory declared above is:
https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass

The preserved source archive and these declaration locations were checked on
2026-10-14. The locators attest the supplied analytic statements, not the new
weighted-column construction or its original-operator composition.

| Supplied module | Immutable source and declaration | Attested scope |
| --- | --- | --- |
| Basic | [Basic.lean](https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass/Basic.lean#L434), `trace_eq_of_hilbertBasis_of_nonneg` | The actual trace equals the Hilbert-basis sum for a positive trace-class bounded operator. |
| HilbertSchmidt | [HilbertSchmidt.lean](https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass/HilbertSchmidt.lean#L254), `HilbertSchmidt.tsum_mul_le_sqrt_mul_sqrt` | Cauchy-Schwarz for the two summable real square sums indexed by a set of the Hilbert space. |
| Polar | [Polar.lean](https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass/Polar.lean#L181), `Polar.polarFactor_mul_absOperator` | The bounded polar factor times the positive absolute-value operator is the original bounded operator. |
| GeneralIdeal | [GeneralIdeal.lean](https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass/GeneralIdeal.lean#L98), `trace_eq_of_hilbertBasis` | The actual trace-basis identity for an arbitrary trace-class bounded operator. |
| GeneralProduct | [GeneralProduct.lean](https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass/GeneralProduct.lean#L52), `isTraceClass_mul_of_isHilbertSchmidt` | The product of two Hilbert-Schmidt bounded operators is trace class. |

## Adoption and consumer

The five source modules are adopted from immutable Physlib revision
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
