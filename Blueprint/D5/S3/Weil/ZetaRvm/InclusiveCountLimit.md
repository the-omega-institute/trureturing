# Inclusive zero counts at the cutoff

## Abstract

Bounds at zero-free heights extend to the inclusive zero count with the same envelope.

The count N(T) includes all nontrivial zeta zeros with 0 < Im ρ ≤ T and their analytic multiplicities. A good height is a height that is not a nontrivial zero ordinate.

**Theorem 1.1 (The count immediately to the right).**

Lean statement: `D5/S3/Weil/ZetaRvm/InclusiveCountLimit.eventually_goodHeight_and_count_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaRvm/InclusiveCountLimit.eventually_goodHeight_and_count_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordinates in (T,T+1] form a finite set that excludes T. Its complement contains a neighborhood of T. In a sufficiently short interval immediately to the right, every height is good and the set of zeros counted in (0,t] is exactly the set counted in (0,T]. Equality of the sets preserves every multiplicity.

**Theorem 1.2 (Transfer of a right-continuous bound).**

Lean statement: `D5/S3/Weil/ZetaRvm/InclusiveCountLimit.abs_ncount_sub_le_of_goodHeight`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaRvm/InclusiveCountLimit.abs_ncount_sub_le_of_goodHeight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose M and E are right-continuous at each T ≥ T₀. If |N(t)−M(t)| ≤ E(t) at every good height t ≥ T₀, the same inequality holds at every T ≥ T₀.

Take a right limit along heights at which N(t) equals N(T). Continuity of subtraction and absolute value gives the limiting discrepancy. Closedness of the real order preserves the bound. The argument retains the full multiplicity at T and requires no assumption about a symmetric convention for the argument of zeta.

## References

- Truth anchor: `D5/S3/Weil/ZetaRvm/InclusiveCountLimit.abs_ncount_sub_le_of_goodHeight`
- Truth anchor: `D5/S3/Weil/ZetaRvm/InclusiveCountLimit.eventually_goodHeight_and_count_eq`
- Dependency: [D5/S3/Weil/ZetaRvm/Defs](Defs.md)
