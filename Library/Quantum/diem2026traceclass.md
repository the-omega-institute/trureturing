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
