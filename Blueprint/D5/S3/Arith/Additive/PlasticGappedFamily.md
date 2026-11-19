# A gapped family of plastic powers

## Abstract

Removing exponent one gives an exact nonconsecutive family and a strict nine-point sumset comparison.

Let F(n) = {0} ∪ [2,n] over the integers, where an interval with upper endpoint below its lower endpoint is empty. For a real r, let A(r,n) = {rᵉ : e ∈ F(n)} and P(r) = {rᵉ : 0 ≤ e ≤ 8, e an integer}. For a finite integer set E, C(E) denotes the sum of the four literal translation counts: starting points t in E for which {t+2,t+3,t+4}, {t+3,t+5,t+6}, {t+5,t+7}, or {t+5,t+8,t+9}, respectively, lie in E. This is the same count used in the plastic collision identity. Write L(n) = n(n+1)/2−4n+26. Every real-power assertion retains r > 1 and r³ = r + 1. Natural n ≥ 10 parametrizes the full integer range in question.

**Definition 1.1 (The exponent family).**

$$\forall (n : \mathbb{N}), \operatorname{F}\left(n\right) = \operatorname{Union}\left(\operatorname{Singleton}\left(0\right), \operatorname{IccZ}\left(2, n\right)\right)$$

*Formalization.* `D5/S3/Arith/Additive/PlasticGappedFamily.family` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Union and Singleton have their usual set meanings, and IccZ is the closed integer interval. The integer one is deliberately absent, but both zero and two are present once n is at least two.

**Theorem 1.2 (Exact counts and the nine-point obstruction).**

$$(\forall (n : \mathbb{N}), (10 \le n) \Rightarrow (((\lvert \operatorname{F}\left(n\right)\rvert  = n) \land ((0 \in \operatorname{F}\left(n\right)) \land ((\neg 1 \in \operatorname{F}\left(n\right)) \land (2 \in \operatorname{F}\left(n\right))))) \land ((\operatorname{C}\left(\operatorname{F}\left(n\right)\right) = 4 \cdot n - 26) \land (\forall (r : \mathbb{R}), (1 < r) \Rightarrow ((r^{3} = r + 1) \Rightarrow ((\lvert \operatorname{A}\left(r, n\right)\rvert  = n) \land (\lvert \operatorname{A}\left(r, n\right) + \operatorname{A}\left(r, n\right)\rvert  = \operatorname{L}\left(n\right)))))))) \land (\forall (r : \mathbb{R}), (1 < r) \Rightarrow ((r^{3} = r + 1) \Rightarrow ((\lvert \operatorname{A}\left(r, 9\right)\rvert  = 9) \land ((\lvert \operatorname{P}\left(r\right)\rvert  = 9) \land ((\lvert \operatorname{A}\left(r, 9\right) + \operatorname{A}\left(r, 9\right)\rvert  = 34) \land ((\lvert \operatorname{P}\left(r\right) + \operatorname{P}\left(r\right)\rvert  = 35) \land (\lvert \operatorname{A}\left(r, 9\right) + \operatorname{A}\left(r, 9\right)\rvert  < \lvert \operatorname{P}\left(r\right) + \operatorname{P}\left(r\right)\rvert )))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/PlasticGappedFamily.whole_proposition_five_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

For n ≥ 10, the four starting-point sets in F(n) are exactly {0} ∪ [2,n−4], {0} ∪ [2,n−6], {0} ∪ [2,n−7], and {0} ∪ [2,n−9]. Their cardinalities are n−4, n−6, n−7, and n−9, even at the empty-interval boundary n=10. The existing plastic collision identity then gives the actual sumset formula. Strict increase of rᵉ ensures that the power images have the stated cardinality. For n=9 the four counts are 5,3,2,1, whereas the consecutive exponent set [0,8] has counts 5,3,2,0. Subtracting these counts from the 45 unordered pairs gives 34 and 35 distinct sums. The absent interior exponent witnesses that F(n) is not an integer interval. This result establishes the explicit family and its exact counts; it does not classify every equality case or independently establish a global minimum over arbitrary exponent sets. The cited Bérczes work supports the reused collision mechanism, not a priority claim for this gapped-family result.

## References

- Truth anchor: `D5/S3/Arith/Additive/PlasticGappedFamily.family`
- Truth anchor: `D5/S3/Arith/Additive/PlasticGappedFamily.whole_proposition_five_one`
- Dependency: [D5/S3/Arith/Additive/PlasticPowerCollisions](PlasticPowerCollisions.md)
