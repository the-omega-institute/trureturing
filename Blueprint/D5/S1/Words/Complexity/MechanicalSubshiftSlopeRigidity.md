# Density and Slope Rigidity of Mechanical Subshifts

## Abstract

Every member of a lower mechanical word subshift has the slope's true-letter density, so equality of two such subshifts forces equality of their slopes.

Fix a real slope alpha in the half-open interval from zero to one and an arbitrary real intercept rho. Every finite prefix of a subshift member is a factor of the base lower mechanical word. Consequently its true count inherits the base window discrepancy, and its asymptotic density recovers alpha without an irrationality assumption.

**Theorem 1.1 (Every subshift member has discrepancy below one).**

$$\left|\operatorname{wordPrefixTrueCount}\left(y, n\right) - n \cdot alpha\right| < 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/MechanicalSubshiftSlopeRigidity.mechanical_wordSubshift_member_true_discrepancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership realizes the length-n prefix as a factor beginning at some natural index. Equality of the factor letters identifies the two filtered true-count sets, so the public lower-mechanical window discrepancy applies directly.

**Theorem 1.2 (Every subshift member has density equal to the slope).**

$$\lim_{n \to \infty} \frac{\operatorname{wordPrefixTrueCount}\left(y, n\right)}{n} = alpha$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/MechanicalSubshiftSlopeRigidity.mechanical_wordSubshift_member_true_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive prefix lengths, the discrepancy estimate traps the density between alpha minus one over n and alpha plus one over n. Both bounds tend to alpha, and the squeeze theorem gives the asserted limit.

**Theorem 1.3 (Equal mechanical subshifts have equal slopes).**

$$\operatorname{wordSubshift}\left(\operatorname{lowerMechanicalWord}\left(alpha, rho\right)\right) = \operatorname{wordSubshift}\left(\operatorname{lowerMechanicalWord}\left(beta, sigma\right)\right) \Rightarrow alpha = beta$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/MechanicalSubshiftSlopeRigidity.mechanical_wordSubshift_slope_eq_of_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower mechanical word at slope alpha belongs to its own subshift. Subshift equality makes that same word a member of the beta subshift, so its prefix density tends to both alpha and beta. Uniqueness of limits forces equality.

## References

- Truth anchor: `D5/S1/Words/Complexity/MechanicalSubshiftSlopeRigidity.mechanical_wordSubshift_member_true_density`
- Truth anchor: `D5/S1/Words/Complexity/MechanicalSubshiftSlopeRigidity.mechanical_wordSubshift_member_true_discrepancy`
- Truth anchor: `D5/S1/Words/Complexity/MechanicalSubshiftSlopeRigidity.mechanical_wordSubshift_slope_eq_of_eq`
- Dependency: [D5/S1/Words/Complexity/SubshiftHausdorffDimension](SubshiftHausdorffDimension.md)
- Dependency: [D5/S1/Words/Mechanical/MechanicalDensity](../Mechanical/MechanicalDensity.md)
