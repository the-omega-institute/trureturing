---
bibkey: miller2026vlasovot
authors: Joseph K. Miller
year: 2026
title: "General-cost optimal transport in the Vlasov formalization"
doi: null
url: https://github.com/LeanPool/lean-pool/tree/edbe5bd56f476cc2965564676b66199f281ab714/LeanPool/Vlasov/OT
claim: "Actual coupling gluing, finite atomic transport, a c-transform, and the hard general-cost Kantorovich-Rubinstein inequality under cost first moments."
strata_touched:
  - D5/S3/Geometry/ProbabilityTransport/CostCoupling
  - D5/S3/Geometry/ProbabilityTransport/FiniteCostKR
license: Apache-2.0
triage: anchor
---

# General-cost optimal transport source

The selected Lean source is Joseph K. Miller's `LeanPool/Vlasov/OT/Coupling.lean`
and the dual functional in `LeanPool/Vlasov/OT/Wasserstein.lean` at lean-pool
commit `edbe5bd56f476cc2965564676b66199f281ab714`.
The source hashes are respectively
`b87540933b2a661a75f0be732b8b6075f27dfdba3ffe0c76358f430d852dedab` and
`f55d87ffca39c1e69148e793f01121356607278d5dbc1d6e636032cf45034a82`.
The pool card `LeanPool/projects/vlasov-mean-field.yaml` identifies
`Hydrodynamical/Vlasov_Meanfield_Formalization` and arXiv `2607.08986`,
with provenance `AI`. The paper is a bibliographic pointer; the mathematical
supplier used here is the Lean source, rather than an asserted reading of the paper.
No ancestry of a separate original-repository revision is asserted.

The selected port uses native disintegration, composition, marginal and integral
APIs. The source's generic finite LP/cone proof is excluded. The finite
transportation adapter directly applies
`ValidELP.strong_duality_of_both_feasible` from the frozen native
`FiniteStrongDuality` module and preserves actual optimizers and zero masses.
Finite-range approximation uses native `SimpleFunc.approxOn` on a cost-metric
type copy with the original sigma-algebra and the given cost moment.
The finite c-transform and weak comparison retain an attained single-potential
maximum. These are applications and formal source adaptations of known
mathematics, with no original-result or external-open-problem claim.

The source pins are Lean 4.35.0-rc3 and Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`; the receiving pins are
Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Only selected optimal-transport statements are included; no Vlasov dynamics,
Picard infrastructure or pin replacement is part of this dependency.

The complete Apache-2.0 LICENSE is reused byte-for-byte at
`docs/reports/brooks-suppliers/lean-pool-LICENSE.txt`, SHA-256
`c95bae1d1ce0235ecccd3560b772ec1efb97f348a79f0fbe0a634f0c2ccefe2c`.
The complete applicable NOTICE is retained verbatim in
`Blueprint/D5/S3/Geometry/ProbabilityTransport/CostCoupling.scribe.cs`, SHA-256
of the original artifact
`e1e1c75e234e0e62b4018f6197a303f3bb7b2923de99730faaa85fa46d285a39`.
Per-file Miller copyright, author and modification notices are retained.

Equivalent coverage in the receiving pinned Mathlib replaces the corresponding
selected source transplant when its hypotheses and conclusions match.
