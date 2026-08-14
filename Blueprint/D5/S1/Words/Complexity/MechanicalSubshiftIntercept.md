# Intercept Independence of Irrational Mechanical Subshifts

## Abstract

At an irrational slope, every intercept gives the same lower mechanical factor language and subshift, while equality of subshifts is equivalent to equality of slopes.

Fix an irrational real slope alpha in the half-open interval from zero to one. Finite breakpoint cells identify factors across arbitrary real intercepts, so both the finite language and its prefix-language subshift depend only on the slope.

**Theorem 1.1 (The mechanical subshift is independent of the intercept).**

$$0 \leq \alpha < 1 \land \operatorname{Irrational}(\alpha) \Rightarrow X_{\alpha, \sigma} = X_{\alpha, \rho}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/MechanicalSubshiftIntercept.wordSubshift_intercept_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The word at the second intercept belongs to the subshift generated at the first intercept. Irrational mechanical minimality then identifies the two generated subshifts.

**Theorem 1.2 (The finite factor language is independent of the intercept).**

$$\operatorname{Irrational}(\alpha) \Rightarrow F_{\alpha, \rho}(n) = F_{\alpha, \sigma}(n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/MechanicalSubshiftIntercept.lowerMechanicalFactorSet_intercept_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each factor occurrence, a right-stable phase interval preserves all breakpoint comparisons through its length. Density of irrational rotation supplies a matching phase at the other intercept; symmetry gives equality of the two factor sets.

**Theorem 1.3 (Mechanical subshifts coincide exactly at equal slopes).**

$$0 \leq \alpha < 1 \land 0 \leq beta < 1 \land \operatorname{Irrational}(\alpha) \Rightarrow (X_{\alpha, \rho} = X_{beta, \sigma} \iff \alpha = beta)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/MechanicalSubshiftIntercept.wordSubshift_eq_iff_slope_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subshift equality forces slope equality by true-letter density rigidity. Conversely, after identifying the slopes, intercept independence gives the required subshift equality.

## References

- Truth anchor: `D5/S1/Words/Complexity/MechanicalSubshiftIntercept.lowerMechanicalFactorSet_intercept_independent`
- Truth anchor: `D5/S1/Words/Complexity/MechanicalSubshiftIntercept.wordSubshift_eq_iff_slope_eq`
- Truth anchor: `D5/S1/Words/Complexity/MechanicalSubshiftIntercept.wordSubshift_intercept_independent`
- Dependency: [D5/S1/Words/Complexity/MechanicalSubshiftMinimality](MechanicalSubshiftMinimality.md)
- Dependency: [D5/S1/Words/Complexity/MechanicalSubshiftSlopeRigidity](MechanicalSubshiftSlopeRigidity.md)
