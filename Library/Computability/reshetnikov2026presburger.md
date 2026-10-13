---
bibkey: reshetnikov2026presburger
authors: Vladimir Reshetnikov
year: 2026
title: ProveIt executable integer Presburger arithmetic
doi: null
url: https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic
claim: Executable Cooper elimination and exact integer-formula decision contracts.
strata_touched:
  - D5/S0/Computability/PresburgerSyntax
  - D5/S0/Computability/PresburgerNormalForm
  - D5/S0/Computability/PresburgerCooper
  - D5/S0/Computability/PresburgerElimination
  - D5/S0/Computability/PresburgerDecision
license: MIT-0
triage: anchor
---

# Executable integer Presburger supplier

## Verified locator

Vladimir Reshetnikov, *ProveIt*, immutable revision
`ec9ab2ffd49f8861022d6f3d4c30205545a3386d`:
https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic

The MIT-0 license is preserved verbatim in
`docs/reports/presburger-suppliers/ProveIt-LICENSE.txt`.
The five source modules correspond respectively to
`D5/S0/Computability/PresburgerSyntax.lean`, `PresburgerNormalForm.lean`,
`PresburgerCooper.lean`, `PresburgerElimination.lean` and `PresburgerDecision.lean`.
The transplant omits exactly two declarations from the original sources:
`PresburgerArithmetic.Affine.dot_nil_left` and
`PresburgerArithmetic.Affine.eval_tail`. Every retained declaration has its
original type; the namespace is unchanged. Five simp steps explicitly unfold
the original `Affine.dot`: the nil branches of `dot_map_neg` and `dot_map_mul`,
the nil and `bs = []` branches of `dot_coeffAdd`, and `eval_const`.
Apart from these five mechanical elaboration adaptations, every retained
statement and proof body matches the original source exactly. Import routes
refer to these canonical modules; headers record each original source hash.
The supplied algorithm is Cooper elimination over integer affine expressions,
with executable `Formula.decideHolds` and its exact correctness equivalence.
The native Nat bridge is a separate structural semantic translation.

The upstream toolchain is Lean v4.32.0. This repository pins Lean v4.33.0
and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
The differing toolchains exclude the pinned dependency route; these modules
are a source transplant, not a new package pin. No upstream Lake manifest
pin is asserted.

Delete this transplant and import the supplier directly once this repository's
own pinned Mathlib contains equivalent executable supplier interfaces and
correctness declarations. An abstract decidability theorem, acceptance into
an upstream branch, or an unpinned release does not satisfy this condition.
