---
bibkey: atlas2026dilworth
authors: ATLAS contributors; Meta Platforms, Inc. and affiliates
year: 2026
title: "Dilworth's decomposition theorem"
doi: null
url: https://github.com/facebookresearch/atlas-lean/blob/98c0ecc1f951837620cbd8e75c6ce27942f496c0/MathlibExt/Combinatorics/Order/Dilworth.lean
claim: "Every finite partial order admits a finite chain cover with at most its maximum antichain cardinality many chains."
strata_touched:
  - D5/S3/Combinatorics/SweepDimension/FiniteDilworth
license: "Apache-2.0 with the preserved ML intended-use preface"
triage: anchor
---

# Finite Dilworth supplier

## Verified locator

https://github.com/facebookresearch/atlas-lean/blob/98c0ecc1f951837620cbd8e75c6ce27942f496c0/MathlibExt/Combinatorics/Order/Dilworth.lean

The supplied source has SHA-256
`ac035dff21ba97054b6ab814a193121e8a331ae0a6753d638a03a0a0c260e9a4`.
The retained dependency closure proves the finite chain-cover theorem by induction,
splitting at a maximum antichain and gluing covers. The unused minimum-cover
cardinality API is omitted. The supplied proof bodies are preserved; the module
header and namespace are adapted, and the cover-existence consequence is exposed.
This is classical Dilworth mathematics, not a new open-problem resolution.

The source and consumer use Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The narrow A17.2 transplant changes
no dependency pin. The source copyright is preserved in the Lean source. The complete root LICENSE,
including its intended-use preface, is preserved at
`docs/reports/lovasz-suppliers/atlas-LICENSE.txt`. That license has
SHA-256 `fc78801eadec58b04e0d5cabe735eb6808e23f47b0cb92b89b55792019b54131`,
matching the already retained ATLAS license. No root NOTICE is supplied.

Retire the transplant when the consumer's actually adopted Mathlib pin supplies
an equivalent finite-poset chain-cover theorem, and replace its callers with
direct applications of that theorem.
