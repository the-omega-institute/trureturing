# Beta Thirteen

## Abstract

The frontier base has a conjugate of modulus above one, so it lies outside the Pisot region and outside the d-bonacci family.

This is the precondition of the frontier claim, not the claim itself. A Pisot base has every conjugate of modulus below one; this base does not, and it also exceeds two, whereas every d-bonacci Perron root lies below two. The two facts together place it outside both families that the tower machinery covers.

**Theorem 1.1 (The frontier base lies outside the Pisot region).**

$$\left(\mathit{betaThirteen}^{2} = \mathit{betaThirteen} + 3 \land 2 < \mathit{betaThirteen}\right) \land \left(\mathit{betaThirteenConjugate}^{2} = \mathit{betaThirteenConjugate} + 3 \land 1 < \left|\mathit{betaThirteenConjugate}\right|\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisotFrontier/BetaThirteen.betaThirteen_is_outside_the_pisot_region` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stated concretely as a modulus bound rather than through a Pisot predicate, because the pinned Mathlib has no such predicate. The linear growth of the gap alphabet at this base is measured but not proved here.

## References

- Truth anchor: `D5/S0/Tower/NonPisotFrontier/BetaThirteen.betaThirteen_is_outside_the_pisot_region`
- Dependency: [D5/S0/Tower/DBonacci/PerronRoot](../DBonacci/PerronRoot.md)
