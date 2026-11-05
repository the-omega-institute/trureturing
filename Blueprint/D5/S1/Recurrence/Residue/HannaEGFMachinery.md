# Integral EGF recurrences and residual transfer

## Abstract

Integral derivative-substitution recurrences transfer exact residual divisibility to all coefficients.

All series below are rational formal power series. The existing eCoeff(F,n) is n! times coeff(n,F), and Integral(F) means that these coefficients are integers. The binomial convolution and its powers are taken from ExponentialImplicitParityPeriodThree. No analytic convergence is asserted.

**Definition 1.1 (Derivative-substitution operator).**

$$\forall f \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \forall k \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall r \in Bool,\; \operatorname{sourceRhs}\left(f, k, p, r\right) = \operatorname{PowerSeries}.\operatorname{subst}\left(f, X \cdot \operatorname{ite}\left(r = true, \operatorname{Inv}.\operatorname{inv}\left(\operatorname{PowerSeries}.\operatorname{derivative}\left(f\right)\right), \operatorname{PowerSeries}.\operatorname{derivative}\left(f\right)^{k}\right)\right)^{p}$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaEGFMachinery.sourceRhs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a rational formal series f, natural k and p, and Boolean r, the true branch uses the inverse derivative. The false branch uses its kth power. Substitution precedes the pth power.

**Definition 1.2 (Divisibility of all exponential coefficients).**

$$\forall m \in \mathbb{N},\; \forall F \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{Multiple}\left(m, F\right) \Leftrightarrow \left(\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; \operatorname{eCoeff}\left(F, n\right) = (m: \mathbb{Q}) \cdot (z: \mathbb{Q})\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaEGFMachinery.Multiple` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiple(m,F) means that each factorial-normalized rational coefficient of F is m times an integer. Both integer witnesses and the natural modulus are cast into Rat.

**Theorem 1.3 (Transfer from a divisible residual).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \forall F \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \forall k \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall r \in Bool,\; \operatorname{constantCoeff}\left(A\right) = 1 \Rightarrow \left(\operatorname{PowerSeries}.\operatorname{derivative}\left(A\right) = \operatorname{sourceRhs}\left(A, k, p, r\right) \Rightarrow \left(\forall f \in \mathbb{N} \to \mathbb{Z},\; \left(\forall n \in \mathbb{N},\; \operatorname{eCoeff}\left(F, n\right) = (f\left(n\right): \mathbb{Q})\right) \Rightarrow \left(f\left(0\right) = 1 \Rightarrow \left(\left(r = true \Rightarrow \operatorname{constantCoeff}\left(\operatorname{PowerSeries}.\operatorname{derivative}\left(F\right)\right) = 1\right) \Rightarrow \left(\left(\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; \operatorname{eCoeff}\left(\operatorname{PowerSeries}.\operatorname{derivative}\left(F\right) - \operatorname{sourceRhs}\left(F, k, p, r\right), n\right) = (m: \mathbb{Q}) \cdot (z: \mathbb{Q})\right) \Rightarrow \left(\exists a \in \mathbb{N} \to \mathbb{Z},\; \left(\forall n \in \mathbb{N},\; \operatorname{eCoeff}\left(A, n\right) = (a\left(n\right): \mathbb{Q})\right) \land \left(\forall n \in \mathbb{N},\; (m: \mathbb{Z}) \mid a\left(n\right) - f\left(n\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaEGFMachinery.residual_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An integral approximate solution and an exact solution with constant coefficient one have the same exponential coefficients modulo m when the derivative-substitution residual is divisible by m. The reciprocal branch also requires derivative constant coefficient one for the approximate solution.

**Theorem 1.4 (Differentiation preserves integrality).**

$$\forall F \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{Integral}\left(F\right) \Rightarrow \operatorname{Integral}\left(\operatorname{PowerSeries}.\operatorname{derivative}\left(F\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaEGFMachinery.integral_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integral(F) is the existing predicate that every eCoeff(F,n) is an integer. This implication holds for all rational formal series under the displayed hypotheses.

**Theorem 1.5 (Powers preserve integrality).**

$$\forall F \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \forall k \in \mathbb{N},\; \operatorname{Integral}\left(F\right) \Rightarrow \operatorname{Integral}\left(F^{k}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaEGFMachinery.integral_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integral(F) is the existing predicate that every eCoeff(F,n) is an integer. This implication holds for all rational formal series under the displayed hypotheses.

**Theorem 1.6 (Multiplication by X preserves integrality).**

$$\forall F \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{Integral}\left(F\right) \Rightarrow \operatorname{Integral}\left(X \cdot F\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaEGFMachinery.integral_X_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integral(F) is the existing predicate that every eCoeff(F,n) is an integer. This implication holds for all rational formal series under the displayed hypotheses.

**Theorem 1.7 (Normalized inversion preserves integrality).**

$$\forall F \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{Integral}\left(F\right) \Rightarrow \left(\operatorname{constantCoeff}\left(F\right) = 1 \Rightarrow \operatorname{Integral}\left(\operatorname{Inv}.\operatorname{inv}\left(F\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaEGFMachinery.integral_inv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integral(F) is the existing predicate that every eCoeff(F,n) is an integer. This implication holds for all rational formal series under the displayed hypotheses.

**Theorem 1.8 (Subtraction preserves integrality).**

$$\forall F \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \forall G \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{Integral}\left(F\right) \Rightarrow \left(\operatorname{Integral}\left(G\right) \Rightarrow \operatorname{Integral}\left(F - G\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaEGFMachinery.integral_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtract the integer witnesses of the two factorial-normalized coefficients.

**Theorem 1.9 (Cancellation of an integral unit).**

$$\forall U \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \forall V \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \forall m \in \mathbb{N},\; \operatorname{Integral}\left(U\right) \Rightarrow \left(\operatorname{Integral}\left(V\right) \Rightarrow \left(\operatorname{constantCoeff}\left(U\right) = 1 \Rightarrow \left(\operatorname{Multiple}\left(m, U \cdot V\right) \Rightarrow \operatorname{Multiple}\left(m, V\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaEGFMachinery.multiple_cancel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In binomial convolution the degree-n term of the unknown sequence has coefficient one. Induction therefore cancels an integral series with constant coefficient one modulo every natural modulus.

**Theorem 1.10 (Finite certificates imply all-degree divisibility).**

$$\forall a \in \operatorname{List}\left(\mathbb{Q}\right),\; \forall z \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall m \in \mathbb{N},\; \left(\forall n \in \operatorname{Fin}\left(\operatorname{List}.\operatorname{length}\left(a\right)\right),\; (\operatorname{Nat}.\operatorname{factorial}\left(\operatorname{val}\left(n\right)\right): \mathbb{Q}) \cdot a[\operatorname{val}\left(n\right)]! = (m: \mathbb{Q}) \cdot (z[\operatorname{val}\left(n\right)]!: \mathbb{Q})\right) \Rightarrow \operatorname{Multiple}\left(m, (\operatorname{Polynomial}.\operatorname{ofCoeffList}\left(a\right): \operatorname{PowerSeries}\left(\mathbb{Q}\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaEGFMachinery.finite_multiple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each list entry is checked after multiplying by its index factorial. Beyond the list length the coefficient vanishes. The notation a[n]! is Lean list indexing with the default value outside the list.

**Theorem 1.11 (Clearing powers of a normalized inverse).**

$$\forall U \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{constantCoeff}\left(U\right) = 1 \Rightarrow \left(\forall n \in \mathbb{N},\; \forall j \in \mathbb{N},\; j \le n \Rightarrow U^{n} \cdot \left(X \cdot \operatorname{Inv}.\operatorname{inv}\left(U\right)\right)^{j} = X^{j} \cdot U^{n - j}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaEGFMachinery.clear_inverse_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When j is at most n, multiplication by U to the nth power clears all j inverse factors. The subtraction n-j is natural subtraction.

**Definition 1.12 (The exponential composition coefficient sum).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{expSum}\left(k, n\right) = \sum_{{j \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)}} (\operatorname{Nat}.\operatorname{choose}\left(n, j\right): \mathbb{Z}) \cdot (k \cdot j: \mathbb{Z})^{n - j}$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaEGFMachinery.expSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This integer binomial sum is the factorial-normalized coefficient of exp(X exp(k X)). Every index is natural; the inner casts and the exponent are displayed explicitly.

**Theorem 1.13 (Every divisor of k gives a unit residue).**

$$\forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; m \mid k \Rightarrow (m: \mathbb{Z}) \mid \operatorname{expSum}\left(k, n\right) - 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaEGFMachinery.expSum_mod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The terminal term is one and each earlier term contains a positive power of a multiple of m.

**Theorem 1.14 (The fourth-power exponential coefficient is one modulo eight).**

$$\forall n \in \mathbb{N},\; (8: \mathbb{Z}) \mid \operatorname{expSum}\left(4, n\right) - 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaEGFMachinery.expSum_four_mod_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The penultimate term is 4 n (n-1), divisible by eight; each earlier term contains a square of a multiple of four.

**Theorem 1.15 (A binomial-sum residue controls the exponential residual).**

$$\forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; \left(\forall n \in \mathbb{N},\; (m: \mathbb{Z}) \mid \operatorname{expSum}\left(k, n\right) - 1\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; \operatorname{eCoeff}\left(\operatorname{PowerSeries}.\operatorname{derivative}\left(\operatorname{PowerSeries}.\operatorname{exp}\left(\mathbb{Q}\right)\right) - \operatorname{PowerSeries}.\operatorname{subst}\left(\operatorname{PowerSeries}.\operatorname{exp}\left(\mathbb{Q}\right), X \cdot \operatorname{PowerSeries}.\operatorname{derivative}\left(\operatorname{PowerSeries}.\operatorname{exp}\left(\mathbb{Q}\right)\right)^{k}\right), n\right) = (m: \mathbb{Q}) \cdot (z: \mathbb{Q})\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaEGFMachinery.exp_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every exponential coefficient of the derivative of exp is one. Subtracting the computed composition coefficient converts the integer divisibility into the stated rational residual identity.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/HannaEGFMachinery.Multiple`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaEGFMachinery.clear_inverse_power`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaEGFMachinery.expSum`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaEGFMachinery.expSum_four_mod_eight`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaEGFMachinery.expSum_mod`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaEGFMachinery.exp_residual`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaEGFMachinery.finite_multiple`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaEGFMachinery.integral_X_mul`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaEGFMachinery.integral_derivative`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaEGFMachinery.integral_inv`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaEGFMachinery.integral_pow`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaEGFMachinery.integral_sub`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaEGFMachinery.multiple_cancel`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaEGFMachinery.residual_transfer`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaEGFMachinery.sourceRhs`
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](../Invariants/PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](../Invariants/UnitReversionSquareParity.md)
- Dependency: [D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree](../Parity/ExponentialImplicitParityPeriodThree.md)
- Dependency: [D5/S1/Recurrence/Residue/IntegralEGFComposition](IntegralEGFComposition.md)
- Dependency: [D5/S1/Recurrence/Residue/QuarticEGFFixedPoint](QuarticEGFFixedPoint.md)
