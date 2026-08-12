# The Green Class Has Content-Independent Measure n to the Minus m

## Abstract

The green class pinning m coordinates has uniform product measure exactly n^(-m).

**Theorem 1.1 (The green class measure is n to the minus m).**

$$\mu(G(T)) = n^{-m}$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/GreenClassMeasure.greenClass_measure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equip the space of infinite strings N -> O over a finite nonempty alphabet O with the uniform product measure (each coordinate independent and uniform). Write n = card O for the alphabet size and m = |S| for the size of the finite support S. The green class G(S, t) = { x : x agrees with the target t on S } (a finite test suite pins the coordinates in S, the rest free) has measure exactly n^(-m): stringMeasure O (greenClass S t) = (card O)^(-1) ^ |S|. This is an exact equality together with a strict positive lower bound (the measure is positive, the '正测'/green-class positivity). The value depends only on the budget m = |S|, not on the pinned content t — the residual uncertainty of a finite certificate is content-independent.

The green class is the cylinder Set.pi S (fun i => { t i }); Measure.infinitePi_pi evaluates it under the infinite product measure as the product over i in S of the per-coordinate uniform singleton mass, each equal to (card O)^(-1) (PMF.uniformOfFintype), and Finset.prod_const folds the constant over S to (card O)^(-1) ^ |S|. Positivity then follows since (card O)^(-1) > 0.

This records the green-class positive-measure clause for the uniform product measure over a single finite nonempty alphabet. The constant-way conservation clause of the source (countable name families pin a null anonymous set) is covered elsewhere (NamingSystem dark-side conservation); the varying-marginal generalization (non-uniform coordinate marginals, where the value becomes the product over i in S of the pinned singleton masses mu_i({t i}), positive exactly when each pinned singleton has positive marginal mass) and the sibling metric diameter formula diam G = 2^(-gamma(S)) are not covered.

## References

- Truth anchor: `D5/S0/Naming/GreenClassMeasure.greenClass_measure`
