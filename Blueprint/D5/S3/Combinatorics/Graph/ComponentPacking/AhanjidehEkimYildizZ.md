# The extremal matching number for odd degrees

## Abstract

The least matching number of an almost regular, triangle-free, factor-critical graph has an exact formula for every odd degree at least twenty-one.

**Definition 1.1 (The least admissible matching number).**

$$\forall d: \mathbb{N}, \operatorname{Z}\left(d\right) = \operatorname{sInf}\left(\ \{m: \mathbb{N} \mid \exists n: \mathbb{N}, \exists G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), (\operatorname{ite}\left(\operatorname{Even}\left(d\right), \operatorname{IsRegularOfDegree}\left(G, d\right), \operatorname{IsAlmostRegular}\left(G, d\right)\right)) \land ((\operatorname{CliqueFree}\left(G, 3\right)) \land ((\operatorname{IsFactorCritical}\left(G\right)) \land (\operatorname{matchingNumber}\left(G\right) = m)))\ \}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZ.Z` (`✓ std3`).

*Citation.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Definition 4.2, page 8: “For any d ≥ 2, let Z(d) be the smallest natural number n such that there exists a d-regular (if d is even) or almost d-regular (if d is odd) triangle-free and factor-critical graph G with ν(G) = n.” Finite graphs have carrier Fin n. The matching number is DimerVirialFourthDifferenceRefutation.matchingNumber; the minimum is the infimum in the natural numbers. The formula defines Z for every natural d, and the theorem uses only odd d at least 21.

**Definition 1.2 (Conjecture 6.5).**

$$(claim) \Leftrightarrow (\forall d: \mathbb{N}, (21 \le d) \Rightarrow ((\operatorname{Odd}\left(d\right)) \Rightarrow (\operatorname{Z}\left(d\right) = \operatorname{Nat}.\operatorname{div}\left(5 \cdot (d + 1), 4\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZ.claim` (`✓ std3`).

*Citation.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Conjecture 6.5, page 20: “For d ≥ 21 and odd, we have Z(d) = ⌊5(d + 1)/4⌋.” The natural-number quotient is floor division. The degree d ranges over all natural numbers satisfying both hypotheses.

**Theorem 1.3 (The conjectured equality).**

$$\forall d: \mathbb{N}, (21 \le d) \Rightarrow ((\operatorname{Odd}\left(d\right)) \Rightarrow (\operatorname{Z}\left(d\right) = \operatorname{Nat}.\operatorname{div}\left(5 \cdot (d + 1), 4\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZ.result` (`✓ std3`). ∎

*Resolves.* `Problems/ahanjideh-ekim-yildiz-2022-z-of-d-conjecture-6-5` (proved) by `D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZ.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ahanjideh-ekim-yildiz-2022-z-of-d-conjecture-6-5","declaration_gid":"D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZ.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

A triangle-free graph below the proposed extremal order admits a pentagon partition through the three-eighths minimum-degree theorem. The exceptional degree 23 and order 59 is handled by deleting the deficient vertex and extending the partition. The cyclic missing-edge incidence inequalities rule out total slack one and three. The almost regular pentagon constructions attain the remaining matching number.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZ.Z`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZ.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZ.result`
- Dependency: [D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZUpper](AhanjidehEkimYildizZUpper.md)
- Dependency: [D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching](FactorCriticalMatching.md)
- Dependency: [D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction](PentagonMissingEdgeObstruction.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations](../Walks/DenseTriangleFreeConfigurations.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/HaggkvistPentagonHomomorphism](../Walks/HaggkvistPentagonHomomorphism.md)
- Dependency: [D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation](../../../StatisticalMechanics/DimerVirialFourthDifferenceRefutation.md)
