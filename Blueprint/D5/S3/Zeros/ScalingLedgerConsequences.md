# Coordinatewise Scaling Consequences

## Abstract

Factor coordinatewise spectral coefficients and prove exact scaling rigidity.

The three theorems formalize all three mathematical clauses of the coordinatewise scaling definition: the displayed coefficient factorization, absolute unboundedness along multiples of a positive-length address, and invariance of coefficient norm under a unit-modulus rotation. This module does not authorize an address-dependent inverse scaling register, which remains the separate governance clause of the following source theorem.

**Theorem 1.1 (Every coefficient has the three exact factors).**

$$\forall a,\delta,t,\quad Z_{1/2+\delta+it}(a)=e^{-\ell(a)/2}e^{-it\ell(a)}e^{-\delta\ell(a)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ScalingLedgerConsequences.half_density_phase_scaling_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a spectral parameter with real displacement delta and imaginary coordinate t, the exponential coefficient splits into its half-density, unit-phase, and real-scaling exponentials. The theorem is pointwise at one ledger address and does not assert a statement about an analytically continued sum.

**Theorem 1.2 (Off-line scaling is unbounded along address multiples).**

$$\ell(a)>0\land\Re(s)\neq\frac12\Rightarrow\forall B\in\mathbb{R},\ \exists m\in\mathbb{N},\ B<\left|\Lambda_s(ma)\right|$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ScalingLedgerConsequences.scaling_ledger_unbounded_on_multiples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any positive-length address and any spectral parameter off the critical line, every real bound is exceeded by the absolute scaling entry at some natural multiple of that address. This proves genuine unboundedness, not merely the linear formula from which it follows.

**Theorem 1.3 (Unit rotations preserve every coefficient norm).**

$$\left\Vert u\right\Vert=1\Rightarrow\left\Vert uZ_s(a)\right\Vert=\left\Vert Z_s(a)\right\Vert$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ScalingLedgerConsequences.unit_rotation_preserves_coefficient_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by any complex factor of norm one leaves the norm of the actual labeled coefficient unchanged. The claim is uniform in the ledger, spectral parameter, and address.
