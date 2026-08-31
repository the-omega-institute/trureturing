# Golden Local Euler Trichotomy

## Abstract

The neutral and quadratic charge denominator specializes to split, inert, and ramified golden local Euler forms.

**Theorem 1.1 (Split Charge Gives a Squared Linear Denominator).**

$$\forall X: \mathbb{R},\\{}(\operatorname{goldenLocalDenominator}\left(1, X\right) = {1 - X}^{2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenLocalEulerTrichotomy.split_local_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting charge plus one makes both linear denominator factors equal, yielding the square of one minus X.

The equality is polynomial and remains independent of any convergence interpretation of X.

**Theorem 1.2 (Inert Charge Gives a Quadratic Denominator).**

$$\forall X: \mathbb{R},\\{}(\operatorname{goldenLocalDenominator}\left(-1, X\right) = 1 - {X}^{2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenLocalEulerTrichotomy.inert_local_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting charge minus one multiplies one minus X by one plus X, giving one minus X squared.

This algebraic factor fusion does not assert that X is a prime monomial.

**Theorem 1.3 (Ramified Charge Leaves One Linear Denominator).**

$$\forall X: \mathbb{R},\\{}(\operatorname{goldenLocalDenominator}\left(0, X\right) = 1 - X).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenLocalEulerTrichotomy.ramified_local_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At zero charge the quadratic-channel factor is one, leaving the neutral factor one minus X.

The statement records the ramified specialization only at the level of the totalized real denominator.

**Theorem 1.4 (The Split Local Factor Is the Inverse Squared Denominator).**

$$\forall X: \mathbb{R},\\{}(\operatorname{goldenLocalFactor}\left(1, X\right) = {{1 - X}^{2}}^{-1}).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenLocalEulerTrichotomy.split_local_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The totalized split local factor is the reciprocal of the squared linear denominator.

Because inversion is totalized over the reals, no nonvanishing premise is claimed or required.

**Theorem 1.5 (The Inert Local Factor Is the Inverse Quadratic Denominator).**

$$\forall X: \mathbb{R},\\{}(\operatorname{goldenLocalFactor}\left(-1, X\right) = {1 - {X}^{2}}^{-1}).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenLocalEulerTrichotomy.inert_local_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The totalized inert local factor is the reciprocal of one minus X squared.

The equality specializes the definition and makes no analytic assertion about an Euler product.

**Theorem 1.6 (The Ramified Local Factor Is the Inverse Linear Denominator).**

$$\forall X: \mathbb{R},\\{}(\operatorname{goldenLocalFactor}\left(0, X\right) = {1 - X}^{-1}).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenLocalEulerTrichotomy.ramified_local_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The totalized ramified local factor is the reciprocal of one minus X.

This completes the three charge specializations without adding a prime-classification claim.

## References

- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenLocalEulerTrichotomy.inert_local_denominator`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenLocalEulerTrichotomy.inert_local_factor`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenLocalEulerTrichotomy.ramified_local_denominator`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenLocalEulerTrichotomy.ramified_local_factor`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenLocalEulerTrichotomy.split_local_denominator`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenLocalEulerTrichotomy.split_local_factor`
