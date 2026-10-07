# Silver-Slope Abelian Periods

## Abstract

Literal definitions and the silver-slope abelian-period conjecture.

The definitions below use Boolean Parikh vectors, the contained-head and contained-tail convention, lower mechanical factors, and the Pell recurrence P₀=0, P₁=1, Pₖ₊₂=2Pₖ₊₁+Pₖ. The source denominators are P(k+1), and their predecessors are P(k).

**Definition 1.1 (The silver slope).**

$$\operatorname{silverSlope}() = \sqrt{2} - 1.$$

*Formalization.* `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.silverSlope` (`✓ std3`).

*Citation.* J. Peltomäki (2020). *Abelian periods of factors of Sturmian words*. DOI: [10.1016/j.jnt.2020.04.007](https://doi.org/10.1016/j.jnt.2020.04.007). URL: <https://arxiv.org/abs/1905.06138>.

*Commentary.*

The slope is the positive quadratic irrational √2−1.

**Definition 1.2 (An abelian block decomposition with contained ends).**

$$\forall w \in \operatorname{List}(\operatorname{Bool}()),\; \forall m \in \mathbb{N},\; \operatorname{AbelianDecomposition}(w, m) \Leftrightarrow \left(0 < m \land \left(\exists head \in \operatorname{List}(\operatorname{Bool}()),\; \exists tail \in \operatorname{List}(\operatorname{Bool}()),\; \exists blocks \in \operatorname{List}(\operatorname{List}(\operatorname{Bool}())),\; blocks \ne [] \land \left(w = \operatorname{append}(\operatorname{append}(head, \operatorname{flatten}(blocks)), tail) \land \left(\left(\forall b \in \operatorname{List}(\operatorname{Bool}()),\; b \in blocks \Rightarrow \operatorname{length}(b) = m\right) \land \left(\left(\forall a \in \operatorname{List}(\operatorname{Bool}()),\; a \in blocks \Rightarrow \left(\forall b \in \operatorname{List}(\operatorname{Bool}()),\; b \in blocks \Rightarrow \operatorname{parikh}(a) = \operatorname{parikh}(b)\right)\right) \land \left(\exists p \in \operatorname{Prod}(\mathbb{N}, \mathbb{N}),\; \left(\forall b \in \operatorname{List}(\operatorname{Bool}()),\; b \in blocks \Rightarrow \operatorname{parikh}(b) = p\right) \land \left(\operatorname{parikh}(head) < p \land \operatorname{parikh}(tail) < p\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.AbelianDecomposition` (`✓ std3`).

*Citation.* J. Peltomäki (2020). *Abelian periods of factors of Sturmian words*. DOI: [10.1016/j.jnt.2020.04.007](https://doi.org/10.1016/j.jnt.2020.04.007). URL: <https://arxiv.org/abs/1905.06138>.

*Commentary.*

Verbatim source (arXiv v3, p. 7): If 𝒫 and 𝒬 are two Parikh vectors and 𝒫 is componentwise less than or equal to 𝒬 but is not equal to 𝒬, then we say that 𝒫 is contained in 𝒬.

Verbatim Definition 2.4 (arXiv v3, p. 8): An abelian decomposition of a word w is a factorization w = u₀u₁⋯uₙ₋₁uₙ such that n ≥ 2, the words u₁, …, uₙ₋₁ have a common Parikh vector 𝒫 (i.e., they are abelian equivalent), and the Parikh vectors of u₀ and uₙ are contained in 𝒫.

The word has a positive block length, a nonempty list of equal-length blocks with a common Parikh vector, and head and tail vectors properly contained in that common vector. The symbol < is the componentwise strict order on ℕ × ℕ: both coordinates are bounded and the vectors are unequal. This is the source's contained relation.

**Definition 1.3 (An abelian period).**

$$\forall w \in \operatorname{List}(\operatorname{Bool}()),\; \forall m \in \mathbb{N},\; \operatorname{AbelianPeriod}(w, m) = \operatorname{AbelianDecomposition}(w, m)$$

*Formalization.* `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.AbelianPeriod` (`✓ std3`).

*Citation.* J. Peltomäki (2020). *Abelian periods of factors of Sturmian words*. DOI: [10.1016/j.jnt.2020.04.007](https://doi.org/10.1016/j.jnt.2020.04.007). URL: <https://arxiv.org/abs/1905.06138>.

*Commentary.*

Verbatim Definition 2.4 (arXiv v3, p. 8): The common length m of the words u₁, …, uₙ₋₁ is called an abelian period of w.

An abelian period is exactly an abelian decomposition at that block length.

**Definition 1.4 (The least abelian period when one exists).**

$$\forall w \in \operatorname{List}(\operatorname{Bool}()),\; \operatorname{minAbelianPeriod}(w) = \operatorname{if}(h: \exists m \in \mathbb{N},\; \operatorname{AbelianPeriod}(w, m), Nat.find(h), 0)$$

*Formalization.* `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.minAbelianPeriod` (`✓ std3`).

*Citation.* J. Peltomäki (2020). *Abelian periods of factors of Sturmian words*. DOI: [10.1016/j.jnt.2020.04.007](https://doi.org/10.1016/j.jnt.2020.04.007). URL: <https://arxiv.org/abs/1905.06138>.

*Commentary.*

Verbatim Definition 2.4 (arXiv v3, p. 8): The minimum abelian period (i.e., the shortest) of w is denoted by μw.

Nat.find selects the least abelian period, with value zero for a word having no abelian period.

**Definition 1.5 (Minimum periods of nonempty lower mechanical factors).**

$$\forall alpha \in \mathbb{R},\; \forall rho \in \mathbb{R},\; \operatorname{abelianPeriodSet}(alpha, rho) = \{m \in \mathbb{N} \mid \exists n \in \mathbb{N},\; \exists i \in \mathbb{N},\; (0 < n \land \operatorname{minAbelianPeriod}(\operatorname{lowerMechanicalFactor}(alpha, rho, n, i)) = m)\}$$

*Formalization.* `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.abelianPeriodSet` (`✓ std3`).

*Citation.* J. Peltomäki (2020). *Abelian periods of factors of Sturmian words*. DOI: [10.1016/j.jnt.2020.04.007](https://doi.org/10.1016/j.jnt.2020.04.007). URL: <https://arxiv.org/abs/1905.06138>.

*Commentary.*

Verbatim source (arXiv v3, p. 2): The abelian period set of an infinite word w is defined as the set of minimum abelian periods of its nonempty factors.

The set contains exactly the minimum periods of factors with positive length.

**Definition 1.6 (The silver-slope period set).**

$$\operatorname{silverAbelianPeriodSet}() = \operatorname{abelianPeriodSet}(\operatorname{silverSlope}(), 0).$$

*Formalization.* `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.silverAbelianPeriodSet` (`✓ std3`).

*Citation.* J. Peltomäki (2020). *Abelian periods of factors of Sturmian words*. DOI: [10.1016/j.jnt.2020.04.007](https://doi.org/10.1016/j.jnt.2020.04.007). URL: <https://arxiv.org/abs/1905.06138>.

*Commentary.*

This specializes the period-set definition to the silver slope and zero intercept.

**Definition 1.7 (The three silver-slope candidate families).**

$$\operatorname{silverCandidateSet}() = \{m \in \mathbb{N} \mid (\exists k \in \mathbb{N},\; (m = \operatorname{P}(k + 1))) \lor (\exists k \in \mathbb{N},\; (m = 2 \times \operatorname{P}(k + 1))) \lor (\exists k \in \mathbb{N},\; (1 \leq k \land m = \operatorname{P}(k + 1) + \operatorname{P}(k)))\}.$$

*Formalization.* `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.silverCandidateSet` (`✓ std3`).

*Citation.* J. Peltomäki (2020). *Abelian periods of factors of Sturmian words*. DOI: [10.1016/j.jnt.2020.04.007](https://doi.org/10.1016/j.jnt.2020.04.007). URL: <https://arxiv.org/abs/1905.06138>.

*Commentary.*

The candidate periods are P(k+1), 2P(k+1), and P(k+1)+P(k) for k≥1 in the last family.

## References

- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.AbelianDecomposition`
- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.AbelianPeriod`
- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.abelianPeriodSet`
- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.minAbelianPeriod`
- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.silverAbelianPeriodSet`
- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.silverCandidateSet`
- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.silverSlope`
- Dependency: [D5/S1/Recurrence/PellCompanionGcd](../../Recurrence/PellCompanionGcd.md)
- Dependency: [D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd](../Complexity/ThueMorseReducedAbelianOdd.md)
- Dependency: [D5/S1/Words/Mechanical/MechanicalFactorComplexity](MechanicalFactorComplexity.md)
