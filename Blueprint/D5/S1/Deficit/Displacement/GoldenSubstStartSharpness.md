# Golden Substitution-Start Sharpness

## Abstract

The golden substitution-start error has an exact fractional-part form, and both endpoints of its window are sharp.

**Theorem 1.1 (The substitution-start error has an exact fractional-part form).**

$$\forall v\in\mathbb{N},\ \operatorname{start}(v) - \varphi v = \varphi^{-1} - \{(v+1)\varphi\}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.golden_subst_start_error_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Beatty formula writes the substitution start as floor((v+1) phi) minus one. Splitting a real number into its integer floor and fractional part, then using phi minus one equals phi inverse, gives the displayed equality exactly.

**Theorem 1.2 (Every substitution-start error lies in the golden window).**

$$\forall v\in\mathbb{N},\ -\varphi^{-2} \leq \operatorname{start}(v) - \varphi v \leq \varphi^{-1}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.golden_subst_start_error_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fractional part is nonnegative and strictly less than one. Applying these two bounds to the exact error formula gives the closed interval from minus phi inverse squared to phi inverse; the identity phi inverse squared plus phi inverse equals one identifies the lower endpoint.

**Theorem 1.3 (Odd Fibonacci indices expose a negative conjugate power).**

$$\forall k\in\mathbb{N},\ \operatorname{Odd}(k) \implies \{Fib(k)\varphi\} = -\psi^{k}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.fract_fib_mul_goldenRatio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's exact Fibonacci residual says Fib(k+1) minus phi times Fib(k) equals psi to the kth power. For odd k that power lies strictly between minus one and zero, so its negative is already the canonical fractional representative.

**Theorem 1.4 (Even Fibonacci indices expose the complementary conjugate power).**

$$\forall k\in\mathbb{N},\ \operatorname{Even}(k) \implies \{Fib(k)\varphi\} = 1 - \psi^{k}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.fract_fib_mul_goldenRatio_of_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For even k the conjugate power is positive and at most one. Shifting the integer part of the same Fibonacci residual down by one leaves one minus psi to the kth power in the canonical half-open fractional interval, including k equal to zero.

**Theorem 1.5 (The upper golden endpoint is sharp).**

$$\forall epsilon\in\mathbb{R},\ epsilon>0 \implies \exists v\in\mathbb{N},\ \varphi^{-1} - epsilon < \operatorname{start}(v) - \varphi v$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.golden_subst_start_error_upper_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose v plus one to be Fib(k) with k odd. The exact odd-index formula makes the gap below phi inverse equal to the positive power phi inverse to k. Such powers become smaller than every positive epsilon, proving the upper endpoint sharp.

**Theorem 1.6 (The lower golden endpoint is sharp).**

$$\forall epsilon\in\mathbb{R},\ epsilon>0 \implies \exists v\in\mathbb{N},\ \operatorname{start}(v) - \varphi v < -\varphi^{-2} + epsilon$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.golden_subst_start_error_lower_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose v plus one to be Fib(k) with k positive and even. The complementary fractional-part formula places the error exactly phi inverse to k above minus phi inverse squared. These powers fall below every positive epsilon, so the lower endpoint is sharp as well. Thus both endpoints of the stated window are proven sharp.

## References

- Truth anchor: `D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.fract_fib_mul_goldenRatio`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.fract_fib_mul_goldenRatio_of_even`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.golden_subst_start_error_eq`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.golden_subst_start_error_lower_sharp`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.golden_subst_start_error_upper_sharp`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.golden_subst_start_error_window`
- Dependency: [D5/S1/Deficit/Displacement/GoldenContractionRadicalBound](GoldenContractionRadicalBound.md)
