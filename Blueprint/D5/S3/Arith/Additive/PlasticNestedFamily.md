# The original nested plastic family

## Abstract

The complete original plastic nested-family theorem, with exact sumset and product counts and comparison to the actual golden-ratio powers.

Fix a real r > 1 with r³ = r + 1. Let E(n) = {0,3} ∪ [5,n+2] over the integers, B(r,n) = {rᵉ : e ∈ E(n)}, φ = (1+√5)/2, and G(n) = {φᵉ : 0 ≤ e ≤ n−1, e an integer}. All sets in the formula are actual finite subsets of the reals. The same B(r,n) supplies every clause. The next exponent set is {0,3} ∪ [5,n+3], exactly E(n+1). Natural indices n ≥ 7 parametrize every original integer index n ≥ 7. Write M(n) = n(n+1)/2 and C(n) = n−1+(n−8)₊+(n−9)₊+(n−11)₊+1[n≥8]+1[n≥10]. The symbol (x)₊ means max(x,0); Lean's natural subtractions implement these positive parts. Write S(r) = {r⁰,r³,r⁵,r⁶,r⁷,r⁸,r⁹}.

**Theorem 1.1 (Theorem 2.1: all scales in the same family).**

$$\forall (r : \mathbb{R}), (1 < r) \Rightarrow ((r^{3} = r + 1) \Rightarrow (\forall (n : \mathbb{N}), (7 \le n) \Rightarrow ((\operatorname{B}\left(r, n\right) \subset \operatorname{B}\left(r, n + 1\right)) \land ((((((\lvert \operatorname{B}\left(r, n\right)\rvert  = n) \land (\lvert \operatorname{B}\left(r, n\right) \cdot \operatorname{B}\left(r, n\right)\rvert  = 2 \cdot n + 2)) \land (\lvert \operatorname{B}\left(r, n\right) \cdot \operatorname{B}\left(r, n\right)\rvert  \le 3 \cdot n - 4)) \land (\lvert \operatorname{B}\left(r, n\right) + \operatorname{B}\left(r, n\right)\rvert  = \operatorname{M}\left(n\right) - \operatorname{C}\left(n\right))) \land (\lvert \operatorname{B}\left(r, n\right) + \operatorname{B}\left(r, n\right)\rvert  \le \lvert \operatorname{G}\left(n\right) + \operatorname{G}\left(n\right)\rvert  - 2)) \land ((n = 7) \Rightarrow (\operatorname{B}\left(r, n\right) = \operatorname{S}\left(r\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/PlasticNestedFamily.whole_theorem_two_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

The exponent map is strictly increasing, so E(n) has n distinct images and its new endpoint proves strict nesting. The actual exponent sumset is {0,3} ∪ [5,2n+4], giving the exact product cardinality 2n+2. The collision module gives the exact actual sumset count, including all boundary terms. For the golden-ratio comparison, normalization of an equal sum gives only (d,a,b)=(3,2,2). The sum map is therefore injective on the sorted pairs excluding outer gap three. There are M(n)−(n−3) such pairs, so |G(n)+G(n)| ≥ M(n)−(n−3). Since C(n) ≥ n−1, the claimed separation by two follows. The seven-point member is identified by its exact exponent set, using the same r. This identification does not reprove the existing frozen seven-point refutation. The real-root assumptions are retained; root existence is already supplied by plastic_root in SumProductGoldenMinimizerRefutation.

## References

- Truth anchor: `D5/S3/Arith/Additive/PlasticNestedFamily.whole_theorem_two_one`
- Dependency: [D5/S3/Arith/Additive/PlasticPowerCollisions](PlasticPowerCollisions.md)
