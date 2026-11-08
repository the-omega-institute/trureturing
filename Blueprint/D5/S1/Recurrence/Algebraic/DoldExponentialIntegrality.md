# Dold Congruences and Formal Exponential Integrality

## Abstract

Dold prime-power congruences imply integrality of a formal exponential.

**Definition 1.1 (Rational coefficients with coprime denominator).**

$$\forall r: \mathbb{N}, \forall q: \mathbb{Q}, \operatorname{IsRIntegralRat}\left(r, q\right) \iff \operatorname{Nat.Coprime}\left(\operatorname{Rat.den}\left(q\right), r\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.IsRIntegralRat` (`✓ std3`).

*Citation.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

The reduced positive denominator of q is coprime to r.

**Theorem 1.2 (Zero has coprime denominator).**

$$\forall r: \mathbb{N}, \operatorname{IsRIntegralRat}\left(r, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.zero` (`✓ std3`). ∎

*Citation.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

Zero has denominator one.

**Theorem 1.3 (One has coprime denominator).**

$$\forall r: \mathbb{N}, \operatorname{IsRIntegralRat}\left(r, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.one_coprime` (`✓ std3`). ∎

*Citation.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

One has denominator one.

**Theorem 1.4 (Addition preserves coprime denominators).**

$$\forall r: \mathbb{N}, \forall q1: \mathbb{Q}, \forall q2: \mathbb{Q}, (\operatorname{IsRIntegralRat}\left(r, q1\right)) \implies ((\operatorname{IsRIntegralRat}\left(r, q2\right)) \implies (\operatorname{IsRIntegralRat}\left(r, q1 + q2\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.add` (`✓ std3`). ∎

*Citation.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

The denominator of a sum divides the product of the denominators.

**Theorem 1.5 (Negation preserves coprime denominators).**

$$\forall r: \mathbb{N}, \forall q: \mathbb{Q}, (\operatorname{IsRIntegralRat}\left(r, q\right)) \implies (\operatorname{IsRIntegralRat}\left(r, -q\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.neg` (`✓ std3`). ∎

*Citation.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

Negation preserves the reduced denominator.

**Theorem 1.6 (Multiplication preserves coprime denominators).**

$$\forall r: \mathbb{N}, \forall q1: \mathbb{Q}, \forall q2: \mathbb{Q}, (\operatorname{IsRIntegralRat}\left(r, q1\right)) \implies ((\operatorname{IsRIntegralRat}\left(r, q2\right)) \implies (\operatorname{IsRIntegralRat}\left(r, q1 \cdot q2\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.mul_coprime` (`✓ std3`). ∎

*Citation.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

The denominator of a product divides the product of the denominators.

**Theorem 1.7 (Derivative of a substituted exponential).**

$$\forall h: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(h\right) = 0) \implies (\operatorname{derivative}\left(\operatorname{subst}\left(h, \operatorname{exp}\left(\mathbb{Q}\right)\right)\right) = \operatorname{subst}\left(h, \operatorname{exp}\left(\mathbb{Q}\right)\right) \cdot \operatorname{derivative}\left(h\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_derivative` (`✓ std3`). ∎

*Citation.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

Formal differentiation of exp(h) gives exp(h) times the derivative of h.

**Definition 1.8 (Coefficientwise local integrality).**

$$\forall r: \mathbb{N}, \forall f: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsRIntegralPS}\left(r, f\right) = \forall n: \mathbb{N}, \operatorname{IsRIntegralRat}\left(r, \operatorname{coeff}\left(n, f\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.IsRIntegralPS` (`✓ std3`).

*Citation.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

Every coefficient has denominator coprime to r.

**Theorem 1.9 (Finite sums preserve local integrality).**

$$\forall r: \mathbb{N}, \forall I: Type*, \forall s: \operatorname{Finset}\left(I\right), \forall f: I \to \mathbb{Q}, (\forall i: I, (i \in s) \implies (\operatorname{IsRIntegralRat}\left(r, f\left(i\right)\right))) \implies (\operatorname{IsRIntegralRat}\left(r, \operatorname{Finset.sum}\left(s, (fun i: I \mapsto f\left(i\right))\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.local_integral_sum` (`✓ std3`). ∎

*Citation.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

A finite sum of rationals with denominators coprime to r again has denominator coprime to r.

**Theorem 1.10 (The formal exponential has constant one).**

$$\forall h: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(h\right) = 0) \implies (\operatorname{constantCoeff}\left(\operatorname{subst}\left(h, \operatorname{exp}\left(\mathbb{Q}\right)\right)\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

A zero-constant formal input gives constant coefficient one after exponential substitution.

**Theorem 1.11 (Local integrality at all primes is integral).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\forall p: \mathbb{N}, (\operatorname{Nat.Prime}\left(p\right)) \implies (\operatorname{IsRIntegralPS}\left(p, f\right))) \implies (\operatorname{HannaLogarithmicPowerClosure.IntegralSeries}\left(f\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.integral_of_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

A rational denominator coprime to every prime equals one.

**Theorem 1.12 (The sufficient Dieudonne-Dwork criterion).**

$$\forall p: \mathbb{N}, (\operatorname{Nat.Prime}\left(p\right)) \implies (\forall h: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(h\right) = 0) \implies ((\operatorname{IsRIntegralPS}\left(p, h - \operatorname{C}\left(\operatorname{Inv.inv}\left((p: \mathbb{Q})\right)\right) \cdot \operatorname{subst}\left(X^{p}, h\right)\right)) \implies (\operatorname{IsRIntegralPS}\left(p, \operatorname{subst}\left(h, \operatorname{exp}\left(\mathbb{Q}\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.local_exp_of_log_difference` (`✓ std3`). ∎

*Citation.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

For each prime p, local integrality of h-p inverse times h(X^p) implies local integrality of exp(h). The input h has constant coefficient zero.

**Theorem 1.13 (Cancelling a natural denominator locally).**

$$\forall p: \mathbb{N}, (\operatorname{Nat.Prime}\left(p\right)) \implies (\forall z: \mathbb{Z}, \forall n: \mathbb{N}, (n \neq 0) \implies (((p: \mathbb{Z})^{\operatorname{padicValNat}\left(p, n\right)} \mid z) \implies (\operatorname{IsRIntegralRat}\left(p, \frac{(z: \mathbb{Q})}{(n: \mathbb{Q})}\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.local_int_div_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

If p to the valuation of nonzero n divides the integer z, then z/n has denominator coprime to p.

**Definition 1.14 (Prime-power congruences).**

$$\forall c: \mathbb{N} \to \mathbb{Z}, \operatorname{Dold}\left(c\right) \iff (\forall p: \mathbb{N}, (\operatorname{Nat.Prime}\left(p\right)) \implies (\forall m: \mathbb{N}, (m \neq 0) \implies ((p: \mathbb{Z})^{\operatorname{padicValNat}\left(p, m\right) + 1} \mid (c\left(p \cdot m\right) - c\left(m\right)))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.Dold` (`✓ std3`).

*Citation.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

Dold(c) requires divisibility by p to the valuation of m plus one for every prime p and every nonzero natural m.

**Definition 1.15 (The rational logarithmic input).**

$$\forall c: \mathbb{N} \to \mathbb{Z}, \operatorname{logInput}\left(c\right) = \operatorname{mk}\left((fun n: \mathbb{N} \mapsto \frac{(c\left(n\right): \mathbb{Q})}{(n: \mathbb{Q})})\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.logInput` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

The degree-n input coefficient is c(n)/n over the rationals; rational division makes the constant coefficient zero.

**Theorem 1.16 (Scaling the input takes powers).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies (\forall n: \mathbb{N}, \operatorname{subst}\left(\operatorname{HSMul.hSMul}\left(n, f\right), \operatorname{exp}\left(\mathbb{Q}\right)\right) = \operatorname{subst}\left(f, \operatorname{exp}\left(\mathbb{Q}\right)\right)^{n})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_nsmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

Substitution into PowerSeries.exp_pow_eq_rescale_exp gives the natural-scaling identity.

**Theorem 1.17 (Exponential of a sum).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \forall g: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies ((\operatorname{constantCoeff}\left(g\right) = 0) \implies (\operatorname{subst}\left(f + g, \operatorname{exp}\left(\mathbb{Q}\right)\right) = \operatorname{subst}\left(f, \operatorname{exp}\left(\mathbb{Q}\right)\right) \cdot \operatorname{subst}\left(g, \operatorname{exp}\left(\mathbb{Q}\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two rational formal series with zero constant coefficients, substituting their sum into the exponential gives the product of the two substituted exponentials.

**Theorem 1.18 (Dold congruences imply integrality).**

$$\forall c: \mathbb{N} \to \mathbb{Z}, (\operatorname{Dold}\left(c\right)) \implies (\forall n: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{coeff}\left(n, \operatorname{subst}\left(\operatorname{logInput}\left(c\right), \operatorname{exp}\left(\mathbb{Q}\right)\right)\right) = (z: \mathbb{Q}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.integral_exp_of_dold` (`✓ std3`). ∎

*Citation.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

Apply the sufficient Dieudonne-Dwork criterion at each prime. The Dold congruences make the logarithmic difference locally integral; a rational coefficient integral at every prime has denominator one. The local-integrality induction is adapted from AINTLIB.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.Dold`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.IsRIntegralPS`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.IsRIntegralRat`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.add`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_add`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_constant`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_derivative`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_nsmul`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.integral_exp_of_dold`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.integral_of_local`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.local_exp_of_log_difference`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.local_int_div_nat`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.local_integral_sum`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.logInput`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.mul_coprime`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.neg`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.one_coprime`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.zero`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure](HannaLogarithmicPowerClosure.md)
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](../Invariants/CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport](../LinearRows/LinearExponentDyadicSupport.md)
- Dependency: [D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence](../Residue/ParametricExponentialSquareCongruence.md)
