# Regular perfect and total perfect subgroup codes

## Abstract

Full finite abelian regular-code criteria on actual loopless sum graphs.

**Definition 1.1 (The subgroup of squares).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.squareSubgroup`

*Formalization.* `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.squareSubgroup` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

In an abelian group the squaring homomorphism has subgroup image. This is the actual set of ambient squares, with no square premise imposed on a witness subgroup.

**Theorem 1.2 (The exact square-set carrier).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.squares_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.squares_eq` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

The carrier of the squaring image equals the elementwise square set. The separate finite Sylow/Frattini identity Sq(G)=Phi(Q)K remains an additional correspondence obligation.

**Theorem 1.3 (A normalized transversal avoiding all nonidentity squares).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.square_free_normalized`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.square_free_normalized` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

If H contains an ambient nonsquare z, modify each nonidentity square representative t to tz, leaving 1 fixed. Every representative stays in its original H-coset, uniqueness is preserved, and all nonidentity representatives are ambient nonsquares. This is a construction for all cosets, not a supplied transversal premise.

**Theorem 1.4 (The full regular PC criterion).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.perfect_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.perfect_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For every subgroup H of every finite abelian G, a regular sum graph with H perfect exists exactly when H is trivial, H contains an ambient nonsquare, or H equals Sq(G). The trivial subgroup is perfect in CS(G,G), the complete simple graph. Omitting that alternative would misstate the retained nontrivial-H antecedent Zhang 5.3. Witness graphs may change during normalization.

**Theorem 1.5 (The corrected regular TPC criterion).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.total_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.total_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

A subgroup H of a finite abelian G has a regular total-code witness exactly when H contains an ambient nonsquare or Sq(G) has two elements and lies in H. In the latter necessity branch H=Sq(G) and |H|=2. Sufficiency constructs an actual square-free transversal or inserts the two ambient squares into a normalized transversal. This is the universal Proposition 3.2 argument; reported finite tables do not prove this criterion.

**Theorem 1.6 (An actual nonsquare).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.even_nonsquare`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.even_nonsquare` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

Cauchy's theorem gives a nontrivial kernel element of the finite squaring map; noninjectivity implies nonsurjectivity and hence a nonsquare. The consumer is the total-code construction for even H.

**Theorem 1.7 (Every even abelian subgroup has a total-code witness).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.even_total_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.even_total_exists` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For every even-order H in a finite abelian G, an actual H-nonsquare and an abelian perfect-code transversal give total perfect coding through the surviving singleton sufficiency. The nonsquare need not be an ambient nonsquare, and no regularity conclusion follows. This retains Zhang 5.4, separately from the corrected regular criterion and all missing enumeration provenance.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.even_nonsquare`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.even_total_exists`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.perfect_iff`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.squareSubgroup`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.square_free_normalized`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.squares_eq`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.total_iff`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/NormalSubgroupCriterion](NormalSubgroupCriterion.md)
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal](PerfectCodeTransversal.md)
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/Regularity](Regularity.md)
