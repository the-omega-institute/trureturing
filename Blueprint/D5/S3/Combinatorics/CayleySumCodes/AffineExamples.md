# Retained constructions and exact corrected examples

## Abstract

AffineExamples in the actual loopless sum graphs.

**Theorem 1.1 (Composition of affine permutations).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.action_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.action_mul` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

The multiplication (s,b)(t,c)=(st,b+sc) agrees with composition on every field element.

**Theorem 1.2 (The full faithful affine action).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.action_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.action_injective` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

The field action is injective; the full multiplier and offset are retained.

**Theorem 1.3 (The actual nontranslation conjugacy classes).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.conjugate_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.conjugate_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For every nonidentity multiplier s, its full affine conjugacy class is exactly the multiplier fiber. This binds the source unions of classes in both retained constructions.

**Theorem 1.4 (The corrected normal connection set).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.connection_normal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.connection_normal` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

The connection is the identity together with every affine negation, over the entire field.

**Theorem 1.5 (The corrected subgroup total codes).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.total_code`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.total_code` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For every finite field of odd characteristic whose units square to 1 or -1, the full complement fixing zero is a total perfect code of the actual loopless graph. The F3 and F5 specializations are the two original examples, not a claim for arbitrary q.

**Theorem 1.6 (The precise connectedness distinction).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.connected_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.connected_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For this actual affine connection, connectedness holds exactly when all units are signs. Thus the F3 example is connected and the F5 example is disconnected. Generation alone is not used as a converse connectedness criterion.

**Theorem 1.7 (Normal multiplier-transversal connections).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.transversalConnection_normal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.transversalConnection_normal` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

All affine elements whose multiplier lies in the chosen transversal form a normal subset.

**Theorem 1.8 (The complete retained affine total construction).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.total_construction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.total_construction` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For every finite field, every multiplicative subgroup H and every actual left coset transversal T, if its internal representative a0 is a nonsquare of H, the full union of the chosen multiplier classes admits the embedded H as a total code. This includes all original q-1=s*t, t>1, H=<c^s> parameters of Zhang Theorem 5.13. No code property is assumed in the hypotheses.

**Theorem 1.9 (Normal perfect-code connections).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.perfectConnection_normal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.perfectConnection_normal` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

Remove the internal multiplier class and add all nonidentity translations, exactly as in the source construction.

**Theorem 1.10 (The complete retained affine perfect construction).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.perfect_construction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.perfect_construction` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

Every actual multiplier transversal gives the specified perfect-code connection, independently of a nonsquare or total-code assumption.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.action_injective`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.action_mul`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.conjugate_iff`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.connected_iff`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.connection_normal`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.perfectConnection_normal`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.perfect_construction`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.total_code`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.total_construction`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.transversalConnection_normal`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/CodeCentralizers](CodeCentralizers.md)
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal](PerfectCodeTransversal.md)
