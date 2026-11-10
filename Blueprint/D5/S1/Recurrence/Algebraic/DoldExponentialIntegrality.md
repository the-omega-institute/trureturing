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

**Definition 1.8 (Prime-power congruences).**

$$\forall c: \mathbb{N} \to \mathbb{Z}, \operatorname{Dold}\left(c\right) \iff (\forall p: \mathbb{N}, (\operatorname{Nat.Prime}\left(p\right)) \implies (\forall m: \mathbb{N}, (m \neq 0) \implies ((p: \mathbb{Z})^{\operatorname{padicValNat}\left(p, m\right) + 1} \mid (c\left(p \cdot m\right) - c\left(m\right)))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.Dold` (`✓ std3`).

*Citation.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

Dold(c) requires divisibility by p to the valuation of m plus one for every prime p and every nonzero natural m.

**Definition 1.9 (The rational logarithmic input).**

$$\forall c: \mathbb{N} \to \mathbb{Z}, \operatorname{logInput}\left(c\right) = \operatorname{mk}\left((fun n: \mathbb{N} \mapsto \frac{(c\left(n\right): \mathbb{Q})}{(n: \mathbb{Q})})\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.logInput` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

The degree-n input coefficient is c(n)/n over the rationals; rational division makes the constant coefficient zero.

**Theorem 1.10 (Scaling the input takes powers).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies (\forall n: \mathbb{N}, \operatorname{subst}\left(\operatorname{HSMul.hSMul}\left(n, f\right), \operatorname{exp}\left(\mathbb{Q}\right)\right) = \operatorname{subst}\left(f, \operatorname{exp}\left(\mathbb{Q}\right)\right)^{n})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_nsmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

Substitution into PowerSeries.exp_pow_eq_rescale_exp gives the natural-scaling identity.

**Theorem 1.11 (Exponential of a sum).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \forall g: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies ((\operatorname{constantCoeff}\left(g\right) = 0) \implies (\operatorname{subst}\left(f + g, \operatorname{exp}\left(\mathbb{Q}\right)\right) = \operatorname{subst}\left(f, \operatorname{exp}\left(\mathbb{Q}\right)\right) \cdot \operatorname{subst}\left(g, \operatorname{exp}\left(\mathbb{Q}\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two rational formal series with zero constant coefficients, substituting their sum into the exponential gives the product of the two substituted exponentials.

**Theorem 1.12 (Dold congruences imply integrality).**

$$\forall c: \mathbb{N} \to \mathbb{Z}, (\operatorname{Dold}\left(c\right)) \implies (\forall n: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{coeff}\left(n, \operatorname{subst}\left(\operatorname{logInput}\left(c\right), \operatorname{exp}\left(\mathbb{Q}\right)\right)\right) = (z: \mathbb{Q}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.integral_exp_of_dold` (`✓ std3`). ∎

*Citation.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

Apply the sufficient Dieudonne-Dwork criterion at each prime. The Dold congruences make the logarithmic difference locally integral; a rational coefficient integral at every prime has denominator one. The local-integrality induction is adapted from AINTLIB.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.Dold`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.IsRIntegralRat`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.add`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_add`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_derivative`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_nsmul`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.integral_exp_of_dold`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.logInput`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.mul_coprime`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.neg`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.one_coprime`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.zero`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure](HannaLogarithmicPowerClosure.md)
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](../Invariants/CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport](../LinearRows/LinearExponentDyadicSupport.md)
- Dependency: [D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence](../Residue/ParametricExponentialSquareCongruence.md)
