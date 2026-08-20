# Orbit Witness

## Abstract

After four greedy steps the conjugate coordinate is four plus the square root of thirteen, one beyond the escape threshold.

The four digit bounds are wide, the tightest margin being about three tenths, so the two bounds on the square root of thirteen suffice and no numeric approximation of the base is needed. Each remainder is carried as an integer pair against one and the base, and the step is closed by the quadratic the base satisfies.

**Theorem 1.1 (The fourth conjugate iterate passes the threshold).**

$$\mathit{conjugateStep4} = 4 + \operatorname{sqrt}\left(13\right) \land 3 + \operatorname{sqrt}\left(13\right) < \left|\mathit{conjugateStep4}\right|$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisotFrontier/OrbitWitness.first_four_digits_and_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The third iterate sits exactly on the threshold in absolute value and the fourth is exactly one beyond it, both as closed algebraic values rather than approximations.

## References

- Truth anchor: `D5/S0/Tower/NonPisotFrontier/OrbitWitness.first_four_digits_and_witness`
- Dependency: [D5/S0/Tower/NonPisotFrontier/ConjugateBridge](ConjugateBridge.md)
