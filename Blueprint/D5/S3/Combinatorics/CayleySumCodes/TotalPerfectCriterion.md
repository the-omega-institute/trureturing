# The missing two-element case in a loopless sum graph

## Abstract

The exact fixed-connection-set two-case criterion for total perfect subgroup codes.

**Definition 1.1 (A normal subset).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion.NormalSubset`

*Formalization.* `D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion.NormalSubset` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

Y is stable under conjugation a*x*a^-1 for every a in the group. It need not be a subgroup, inverse closed, or disjoint from the identity.

**Definition 1.2 (The actual Cayley sum graph).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion.sumGraph`

*Formalization.* `D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion.sumGraph` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

The vertices are the group elements. Distinct g,h are adjacent exactly when g*h belongs to Y. Conjugation invariance makes this symmetric. Equality is always excluded, including when g*g belongs to Y. This is the sum graph of the source, with no inverse closure hypothesis.

**Definition 1.3 (Total perfect codes).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion.IsTotalPerfectCode`

*Formalization.* `D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion.IsTotalPerfectCode` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

Every vertex g has exactly one open neighbor in C. This condition applies also to g in C; self-neighbors never count. The predicate is stated with existence and uniqueness in the actual SimpleGraph, not a count supplied as a hypothesis.

**Definition 1.4 (Squares in the subgroup).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion.squares`

*Formalization.* `D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion.squares` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

The square set consists of h*h for h in H, viewed in the ambient group. A nonsquare of H can be a square of the ambient group. No subgroup structure is imposed on this set in a noncommutative group.

**Theorem 1.5 (Both directions and both cases).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For every finite group G, every subgroup H, and every fixed normal subset Y, H is a total perfect code precisely when each outside left coset gH meets Y once and one of two conditions holds. Either Y intersect H is a singleton {z} whose element is a nonsquare of H; or Y intersect H has two elements and contains every square of H. H need not be normal. Coset membership is the exact condition g^-1*y in H.

Multiplication h maps to g*h is a bijection between the open H-neighbors of g and (Y intersect gH) with g*g erased. If g is outside H, the erased element was absent already. If g is in H, the slice is Y intersect H. At g=1 the unique-neighbor condition forces its size to be one or two. In size one no subgroup square can be that element; in size two every subgroup square must be one of the two elements. These same bijections prove sufficiency in both cases.

The primary source is Theorem 2.1 in both public versions of Ma, Nikandish and Zhang, with version identities distinguished in the library note. The two-element branch corrects the antecedent total-code necessity. The surviving transversal sufficiency is not refuted. Quantifying Y gives the corresponding existence criterion. Index-cardinality formulas, induced-matching parity, actual Q8/D8 and order-32 examples, normalized perfect codes and the later classification/equivalence outcomes remain separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion.IsTotalPerfectCode`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion.NormalSubset`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion.result`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion.squares`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion.sumGraph`
