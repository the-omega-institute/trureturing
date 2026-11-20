# Fractional orbit weights on finite probability grids

## Abstract

Exact seed budgets with fractional orbit weights on permutation-equivariant probability grids.

**Theorem 1.1 (Sharp support budget when the scaled weights may be fractional).**

$$\forall k q n, 2 \le k \land 0 < q \land \operatorname{PrimeDivisibility}\left(k, (k-1)\cdot q\right) \Rightarrow (\operatorname{SeedBudget}\left(k, (k-1)\cdot q, \operatorname{factorial}\left(k\right)\cdot(n+1)\right) \iff q+1 \le (\operatorname{gcd}\left(k, q\right)+1)\cdot(k+1)^n)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/FractionalGridSupport.fractional_grid_budget_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take at least two labels and a positive natural number q. The denominator m is (k minus one) times q. PrimeDivisibility means every prime at most k divides m. The budget is k factorial times n plus one, with n plus one as the orbit count. SeedBudget uses the same shared calibrating law.

The prime-cycle test forces regular seed orbits. Profiles with k minus one tied labels require all q plus one integer levels. The weights of the orbit digits sum to q divided by k. Its reduced denominator is k divided by the greatest common divisor of k and q. Apply the integer-level capacity bound to these weights and the tied profiles.

For attainment, write q divided by k as A divided by b in lowest terms. Use the common fractional allocation construction with numerator total A and denominator b. For every profile, the integer group demands and the number of blocks satisfy the allocation balance. The stabilizer readout and transport along profile orbits then give one equivariant law. With eight labels and q equal to 210 or 270, the greatest common divisor is two. The first feasible budgets use three and four regular orbits, respectively, giving support sizes 120960 and 161280.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/FractionalGridSupport.fractional_grid_budget_iff`
- Dependency: [D5/S3/Combinatorics/SubsetSpectrum/AdditiveDigitCapacity](../../Combinatorics/SubsetSpectrum/AdditiveDigitCapacity.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/PermutationGridSupport](PermutationGridSupport.md)
