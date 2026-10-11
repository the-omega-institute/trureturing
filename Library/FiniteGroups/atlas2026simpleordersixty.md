---
bibkey: atlas2026simpleordersixty
authors: Moonshine-in-Kansas/atlas contributors
year: 2026
title: Elementary recognition of a nonabelian simple group of order sixty
doi: null
url: https://github.com/Moonshine-in-Kansas/atlas/blob/1bc46341457aab119f667c43b6ce7216cbb899b6/Atlas/GroupTheory/SimpleOrderSixty.lean
claim: Every finite nonabelian simple group of cardinality sixty admits an actual multiplicative equivalence to the alternating group on Fin 5, constructed using Sylow counting and the action on five cosets.
strata_touched:
  - D5/S3/FiniteGroups/SimpleOrderSixty
license: Apache-2.0
triage: anchor
---

# Simple groups of order sixty

This is a software proof source, not a claimed journal publication. The theorem
is classical; neither mathematical novelty nor priority is asserted.
The source's declaration `Atlas.GroupTheory.smallSimpleOrder60EquivAlt5`
constructs a multiplicative equivalence for an arbitrary type G with group,
finiteness and simplicity instances, cardinality sixty and noncommutativity.
It assumes no classification function and specifies no images of chosen generators.

## Verified locator

- Repository: https://github.com/Moonshine-in-Kansas/atlas
- Immutable revision: `1bc46341457aab119f667c43b6ce7216cbb899b6`.
- URL: https://github.com/Moonshine-in-Kansas/atlas/blob/1bc46341457aab119f667c43b6ce7216cbb899b6/Atlas/GroupTheory/SimpleOrderSixty.lean
- Locator: `Atlas.GroupTheory.smallSimpleOrder60EquivAlt5`, lines 13–18.
- Supporting source files in the same revision and directory:
  `DisjointSubgroupCounting.lean`, `SmallIndexSimple.lean`,
  `CenterSimpleQuotient.lean`, `SimpleOrderSixtySylow.lean`,
  `SimpleIndexFiveAlternating.lean`.

## Source migration and retirement

The upstream pins Lean 4.34.0-rc2 and Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`; this repository pins Lean 4.33.0
and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
These unequal pins preclude the dependency form of spec A17.2.
The selected original recognition closure is therefore migrated as source.
All retained proof bodies and original declaration names are unchanged;
only import routing, concatenation and the canonical header are adapted.
All five local prime-instance names are already present in the primary source. The unused
`center_eq_of_simple_quotient` is omitted.
The complete original Apache-2.0 license accompanies the code at
`docs/reports/licenses/atlas-simple-order-sixty.md`; the primary tree has no NOTICE.

Retire the migrated recognition declarations when this repository's own pinned
Mathlib revision supplies an equivalent full finite nonabelian simple-order-sixty
recognition declaration returning a multiplicative equivalence to the alternating
group on Fin 5. Replace consumers with that pinned declaration and remove migrated
helpers when no live consumer remains. Acceptance on an unpinned upstream branch
does not trigger this rule.

The proof constructs an index-five subgroup, makes its coset action faithful by
simplicity, kills the sign character, and obtains surjectivity from equal finite
cardinalities. It supplies no marked-generator, surface, genus or geometric
completion assertion.
