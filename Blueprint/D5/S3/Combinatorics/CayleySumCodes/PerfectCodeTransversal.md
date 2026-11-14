# Perfect codes and identity-containing normal transversals

## Abstract

Normalized perfect subgroup codes in normal-connection sum graphs.

For every group G, subgroup H and g,t in G, t inverse times g belongs to H exactly when g inverse times t belongs to H. Inversion in H exchanges these two elements. This is the membership conversion used in the transversal code construction.

For every group G, subgroup H and left transversal T containing 1, any t in both T and H equals 1. Both t and 1 represent the identity H-coset, so the unique representative property identifies them. The same fact supplies the normalized square-free construction in the abelian regular-code criterion.

**Definition 1.1 (Closed neighborhoods).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.IsPerfectCode`

*Formalization.* `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.IsPerfectCode` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

A perfect code has exactly one code vertex in each closed neighborhood, including the vertex itself. A total perfect code instead uses open neighborhoods, so the predicates and their transversal criteria differ.

**Theorem 1.2 (Constructing the witness graph).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.of_transversal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.of_transversal` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

A specified conjugation-invariant left transversal T containing 1 gives a perfect subgroup code with connection set T without 1. Inside H the only closed-neighborhood code vertex is the vertex itself; outside H uniqueness follows from the actual coset representative. This retains the normalized perfect-code antecedent of Jun-Yang Zhang, Lemma 3.1; the supplied arXiv v1 and final publisher article remain distinct source identities. No graph equality under identity deletion is asserted.

**Theorem 1.3 (Normalizing an arbitrary witness).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.normalized_transversal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.normalized_transversal` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For an arbitrary perfect-code connection set Y, its intersection with H is contained in {1}, and need not be empty. Remove 1 and insert 1 as the H-coset representative to get an actual normal left transversal. This supplies the perfect-code part of correction Proposition 4.1 and repairs the arbitrary-witness disjointness inference; it does not identify the old and normalized graphs.

**Theorem 1.4 (The normalized existential equivalence).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.exists_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.exists_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

A subgroup has some perfect-code sum graph with normal connection set if and only if it has an identity-containing normal left transversal. The existential witnesses may change; this is not a fixed-connection-set equivalence or a quotient code-inheritance claim.

**Theorem 1.5 (Normal subgroups admit normalization).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.normal_exists_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.normal_exists_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For normal H, NLT is equivalent to existence of a perfect-code sum graph. The representative of H in a normal transversal is central in G. Translating the whole transversal by its inverse preserves conjugation invariance and gives a representative equal to 1. The proof does not extend this normalization to nonnormal H or claim equality of the original and constructed graphs.

**Theorem 1.6 (Every abelian subgroup has a witness).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.abelian_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.abelian_exists` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

Every subgroup of an abelian group has a perfect-code sum-graph witness. Choose an actual left transversal containing 1; in an abelian group every subset is conjugation invariant. The construction does not require finiteness and supplies the finite case retained from Zhang Theorem 5.1. It claims neither regularity nor total perfect coding for arbitrary subgroup order.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.IsPerfectCode`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.abelian_exists`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.exists_iff`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.normal_exists_iff`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.normalized_transversal`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.of_transversal`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/NormalTransversal](NormalTransversal.md)
