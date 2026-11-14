# Exact all-length long-core omission scores

## Abstract

Exact all-length long-core omission scores

Actual induced path constraints extract the original Cell and Across premises from every dissociation selection. Pair-full indicators implement the score-preserving normalization. A score-thirteen open cell contains both matched boundary H pairs; the actual H seam excludes neighboring exceptional cells, including a singleton. Symbolic permutation summation gives the upper bound and the separated A/B word has exactly floor(k/2) A cells, attaining score twelve k plus floor(k/2) for every length. This is the open-H long core, distinct from ClosedCore.

**Definition 1.1 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph : SimpleGraph (Fin 20).

**Definition 1.2 (bit).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.bit`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.bit` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def bit (S : Finset (Fin 20)) (f : Bool) (v : Fin 20) : ℕ.

**Definition 1.3 (full).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.full`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.full` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def full (S : Finset (Fin 20)) (f : Bool) (a b : Fin 20) : ℕ.

**Definition 1.4 (cell).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.cell`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.cell` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def cell (S : Finset (Fin 20)) (f : Bool) : Fin 3 → Cell.

**Definition 1.5 (omitted).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.omitted`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.omitted` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def omitted (S : Finset (Fin 20)) (f : Bool) : ℕ.

**Theorem 1.6 (local bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.local_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.local_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem local_bound (S : Finset (Fin 20)) (hS : IsKIndependent graph 2 S) : S.card+omitted S false≤13 ∧ (S.card+omitted S false=13 → 0∈S ∧ 1∈S ∧ 4∈S ∧ 5∈S).

**Definition 1.7 (slice).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.slice`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.slice` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def slice (S : Finset (I × Fin 20)) (i : I) : Finset (Fin 20).

**Definition 1.8 (omissions).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.omissions`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.omissions` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def omissions (S : Finset (I × Fin 20)) : ℕ.

**Theorem 1.9 (exceptional exclusion).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.exceptional_exclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.exceptional_exclusion` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem exceptional_exclusion (e : Equiv.Perm I) (S : Finset (I × Fin 20)) (hS : IsKIndependent (LongCoreWord.graph e) 2 S) (i : I) : ¬ ( (slice S i).card+omitted (slice S i) false=13 ∧ (slice S (e i)).card+omitted (slice S (e i)) false=13).

**Theorem 1.10 (score bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.score_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.score_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem score_bound (e : Equiv.Perm I) (S : Finset (I × Fin 20)) (hS : IsKIndependent (LongCoreWord.graph e) 2 S) : S.card+omissions S≤12*Fintype.card I+Fintype.card I/2.

**Definition 1.11 (cyclicWord).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.cyclicWord`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.cyclicWord` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def cyclicWord {k : ℕ} (i : Fin k) : Bool.

**Theorem 1.12 (cyclicWord separated).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.cyclicWord_separated`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.cyclicWord_separated` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cyclicWord_separated (k : ℕ) : ∀ i : Fin k, ¬ (cyclicWord i=true ∧ cyclicWord (finRotate k i)=true).

**Theorem 1.13 (cyclicWord count).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.cyclicWord_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.cyclicWord_count` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cyclicWord_count (k : ℕ) : (Finset.univ.filter (fun i : Fin k => cyclicWord i=true)).card=k/2.

**Theorem 1.14 (cyclic score).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.cyclic_score`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.cyclic_score` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cyclic_score (k : ℕ) : (∀ S : Finset (Fin k × Fin 20), IsKIndependent (LongCoreWord.graph (finRotate k)) 2 S → S.card+omissions S≤12*k+k/2) ∧ ∃ S : Finset (Fin k × Fin 20), IsKIndependent (LongCoreWord.graph (finRotate k)) 2 S ∧ S.card+omissions S=12*k+k/2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.bit`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.cell`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.cyclicWord`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.cyclicWord_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.cyclicWord_separated`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.cyclic_score`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.exceptional_exclusion`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.full`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.local_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.omissions`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.omitted`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.score_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.slice`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/ClosedModule](ClosedModule.md)
