# The original local cell proof

## Abstract

The original local cell proof

Cell weights, all actual path constraints and across-cell constraints are distinct data. The received proofs bound a cell, classify tight cells and bound three-cell blocks with one or two selected hubs. These local lemmas alone do not assert a graph parameter or an all-length assembly.

**Definition 1.1 (Cell).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.Cell`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.Cell` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: structure Cell.

**Definition 1.2 (Cell.weight).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.weight`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.weight` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Cell.weight (cell : Cell) : Nat.

**Definition 1.3 (Valid).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.Valid`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.Valid` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Valid (cell : Cell) (evenHub oddHub : Nat) : Prop.

**Definition 1.4 (Across).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.Across`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.Across` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Across (first second : Cell) : Prop.

**Theorem 1.5 (cell cap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.cell_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.cell_cap` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cell_cap (cell : Cell) (evenHub oddHub : Nat) (hvalid : Valid cell evenHub oddHub) : cell.weight ≤ 3.

**Theorem 1.6 (one hub tight).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.one_hub_tight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.one_hub_tight` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem one_hub_tight (cell : Cell) (hvalid : Valid cell 1 0) (htight : cell.weight = 3) : (cell.cut = 0 ∧ cell.leafLeft = 1 ∧ cell.leafRight = 1 ∧ cell.highLeft = 0 ∧ cell.highRight = 1) ∨ (cell.cut = 1 ∧ cell.leafLeft = 0 ∧ cell.highLeft = 1 ∧ cell.highRight + cell.leafRight = 1).

**Theorem 1.7 (two hub tight).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.two_hub_tight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.two_hub_tight` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem two_hub_tight (cell : Cell) (hvalid : Valid cell 1 1) (htight : cell.weight = 3) : cell.cut = 1 ∧ cell.leafLeft = 0 ∧ cell.leafRight = 0 ∧ cell.highLeft = 1 ∧ cell.highRight = 1.

**Theorem 1.8 (one hub next cut).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.one_hub_next_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.one_hub_next_cut` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem one_hub_next_cut (first second : Cell) (hfirst : Valid first 1 0) (hsecond : Valid second 1 0) (htightFirst : first.weight = 3) (htightSecond : second.weight = 3) (hacross : Across first second) : second.cut = 0.

**Theorem 1.9 (one hub block).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.one_hub_block`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.one_hub_block` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem one_hub_block (first middle last : Cell) (hfirst : Valid first 1 0) (hmiddle : Valid middle 1 0) (hlast : Valid last 1 0) (hfirstAcross : Across first middle) (hlastAcross : Across middle last) (hhub : middle.leafLeft + last.leafLeft + 1 ≤ 2) : 3 + first.weight + middle.weight + last.weight + 1 ≤ 12.

**Theorem 1.10 (two hub block).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.two_hub_block`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.two_hub_block` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem two_hub_block (first middle last : Cell) (hfirst : Valid first 1 1) (hmiddle : Valid middle 1 1) (hlast : Valid last 1 1) (hfirstAcross : Across first middle) (hlastAcross : Across middle last) : 3 + first.weight + middle.weight + last.weight + 2 ≤ 13 ∧ (3 + first.weight + middle.weight + last.weight + 2 = 13 → first.weight = 3 ∧ middle.weight = 2 ∧ last.weight = 3).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.Across`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.Cell`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.Valid`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.cell_cap`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.one_hub_block`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.one_hub_next_cut`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.one_hub_tight`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.two_hub_block`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.two_hub_tight`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.weight`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/LongCoreWord](LongCoreWord.md)
