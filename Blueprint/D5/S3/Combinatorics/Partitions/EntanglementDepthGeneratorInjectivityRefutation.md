# Noninteger parameters do not ensure injectivity on integer partitions

## Abstract

Distinct partitions have equal power sums at exponent one half and equal entanglement dimensions at base five halves.

**Definition 1.1 (The real power sum).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(q: \mathbb{R}\right), \left(\forall \left(\xi: \operatorname{Nat.Partition}\left(n\right)\right), \left(\left(\operatorname{D5.S3.Combinatorics.Partitions.EntanglementDepthGeneratorInjectivityRefutation.powerSum}\left(\left(n := n\right), q, \xi\right): \mathbb{R}\right) = \operatorname{Multiset.sum}\left(\operatorname{Multiset.map}\left(\lambda \left(x: \mathbb{N}\right) \mapsto \left(\left(\operatorname{Nat.cast}\left(x\right): \mathbb{R}\right)^{q}\right), \operatorname{Nat.Partition.parts}\left(\xi\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.powerSum` (`✓ std3`).

*Citation.* Szilárd Szalay; Géza Tóth (2025). *Alternatives of entanglement depth and metrological entanglement criteria*. DOI: [10.22331/q-2025-04-18-1718](https://doi.org/10.22331/q-2025-04-18-1718). URL: <https://arxiv.org/abs/2408.15350v3>.

*Commentary.*

For a partition ξ of the natural number n and a real exponent q, powerSum sums the qth powers of the parts, including every repeated part with its multiplicity. Each natural part is cast to a real number before taking the real power. This is the power sum s_q of equation (sq), depths.tex lines 1903–1907. The source describes integer partitions as multisets of positive parts summing to n at lines 464–466; Nat.Partition n supplies this domain, including the empty partition at n = 0.

**Definition 1.2 (The entanglement dimension).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(d: \mathbb{R}\right), \left(\forall \left(\xi: \operatorname{Nat.Partition}\left(n\right)\right), \left(\left(\operatorname{D5.S3.Combinatorics.Partitions.EntanglementDepthGeneratorInjectivityRefutation.entanglementDimension}\left(\left(n := n\right), d, \xi\right): \mathbb{R}\right) = \operatorname{Multiset.sum}\left(\operatorname{Multiset.map}\left(\lambda \left(x: \mathbb{N}\right) \mapsto \left(d^{x}\right), \operatorname{Nat.Partition.parts}\left(\xi\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.entanglementDimension` (`✓ std3`).

*Citation.* Szilárd Szalay; Géza Tóth (2025). *Alternatives of entanglement depth and metrological entanglement criteria*. DOI: [10.22331/q-2025-04-18-1718](https://doi.org/10.22331/q-2025-04-18-1718). URL: <https://arxiv.org/abs/2408.15350v3>.

*Commentary.*

For a real base d and a partition ξ of n, entanglementDimension sums d raised to each natural part, with multiplicity. The exponent remains a natural number. This is the function Dim_d of equation (Dimd), depths.tex lines 2306–2312. The definition permits every real d. The source's physical dimension satisfies d ≥ 2; for noninteger d the source treats d as a mathematical parameter at lines 2445–2447.

**Definition 1.3 (The disjunction of the two injectivity expectations).**

$$\left(\operatorname{D5.S3.Combinatorics.Partitions.EntanglementDepthGeneratorInjectivityRefutation.claim}: \operatorname{Prop}\right) = \left(\left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(q: \mathbb{R}\right), \left(\left(\forall \left(k: \mathbb{N}\right), \left(\left(\operatorname{Nat.cast}\left(k\right): \mathbb{R}\right) \ne q\right)\right) \to \left(\operatorname{Function.Injective}\left(\operatorname{D5.S3.Combinatorics.Partitions.EntanglementDepthGeneratorInjectivityRefutation.powerSum}\left(\left(n := n\right), q\right)\right)\right)\right)\right)\right) \lor \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(d: \mathbb{R}\right), \left(\left(\left(\operatorname{Nat.cast}\left(\left(2: \mathbb{N}\right)\right): \mathbb{R}\right) \le d\right) \to \left(\left(\forall \left(k: \mathbb{N}\right), \left(\left(\operatorname{Nat.cast}\left(k\right): \mathbb{R}\right) \ne d\right)\right) \to \left(\operatorname{Function.Injective}\left(\operatorname{D5.S3.Combinatorics.Partitions.EntanglementDepthGeneratorInjectivityRefutation.entanglementDimension}\left(\left(n := n\right), d\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Szilárd Szalay; Géza Tóth (2025). *Alternatives of entanglement depth and metrological entanglement criteria*. DOI: [10.22331/q-2025-04-18-1718](https://doi.org/10.22331/q-2025-04-18-1718). URL: <https://arxiv.org/abs/2408.15350v3>.

*Commentary.*

The claim is the disjunction of two universal assertions suggested by Section 4.7, depths.tex lines 2437 and 2445–2447. The first asserts injectivity of powerSum on every Nat.Partition n for every real q unequal to the real cast of every natural k. The second asserts injectivity of entanglementDimension on every Nat.Partition n for every real d at least the real cast of the natural number two and unequal to the real cast of every natural k. Injectivity means that equality of values forces equality of the two partitions.

**Theorem 1.4 (Both universal injectivity assertions fail).**

$$\neg \left(\operatorname{D5.S3.Combinatorics.Partitions.EntanglementDepthGeneratorInjectivityRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/szalay-toth-2025-entanglement-depth-generator-injectivity` (refuted) by `D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"szalay-toth-2025-entanglement-depth-generator-injectivity","declaration_gid":"D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Szilárd Szalay; Géza Tóth (2025). *Alternatives of entanglement depth and metrological entanglement criteria*. DOI: [10.22331/q-2025-04-18-1718](https://doi.org/10.22331/q-2025-04-18-1718). URL: <https://arxiv.org/abs/2408.15350v3>.

*Commentary.*

Take the partitions {9, 1, 1, 1} and {4, 4, 4} of 12. Also take the partition of 26 with two parts equal to 3 and twenty parts equal to 1, and the partition of 26 with thirteen parts equal to 2. All parts are positive, and their sums are respectively 9 + 1 + 1 + 1 = 12, 4 + 4 + 4 = 12, 3 + 3 + 20 = 26 and 13 · 2 = 26. The last partition is the specialization n = 26, y = 13, z = 0 of partition126, whose parts are n − 2y − 6z copies of 1, y copies of 2 and z copies of 6.

The inequality half_noninteger says that an integer cast to the reals plus one half cannot equal the real cast of an integer. Apply it at integer shifts 0 and 2 and include each natural number into the integers. Reversing the inequalities shows that every natural cast differs from 1/2 and from 5/2.

The first pair of partitions is distinct because 9 belongs to the first multiset and not to the second. The second pair is distinct because 3 belongs to the partition with two threes and not to the partition with thirteen twos.

For real a and p, rpow_square_half gives (a²)^(p/2) = |a|^p. Use a = 3, p = 1 and then a = 2, p = 1. Positivity of 3 and 2 yields 9^(1/2) = 3 and 4^(1/2) = 2. Since 1^(1/2) = 1, the first pair has powerSum values 3 + 1 + 1 + 1 = 6 and 2 + 2 + 2 = 6.

At base 5/2, the second pair has entanglementDimension values 2 · (5/2)³ + 20 · (5/2) = 325/4 and 13 · (5/2)² = 325/4. These are equal by rational arithmetic.

Assume the disjunction claim and consider its two alternatives. The first alternative, at n = 12 and q = 1/2, would make the equal powerSum values force equality of the first pair, contradicting their distinctness. For the second alternative use n = 26 and d = 5/2. The base satisfies 2 ≤ 5/2 and is unequal to every natural cast. Injectivity would make the equal entanglementDimension values force equality of the second pair, again contradicting distinctness. Thus neither alternative holds.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.entanglementDimension`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.powerSum`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.result`
- Dependency: [D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture](../../../S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.md)
- Dependency: [D5/S3/Analytic/BesselProductOrderLogConvexity/Result](../../Analytic/BesselProductOrderLogConvexity/Result.md)
- Dependency: [D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation](../../Quantum/NormCompression/StrictSpectralPolyaRefutation.md)
