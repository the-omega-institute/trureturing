# Dold Congruences and Formal Exponential Integrality

## Abstract

Dold prime-power congruences imply integrality of a formal exponential.

**Definition 1.1 (Prime-power congruences).**

$$\forall c: \mathbb{N} \to \mathbb{Z}, \operatorname{Dold}\left(c\right) \iff (\forall p: \mathbb{N}, (\operatorname{Nat.Prime}\left(p\right)) \implies (\forall m: \mathbb{N}, (m \neq 0) \implies ((p: \mathbb{Z})^{\operatorname{padicValNat}\left(p, m\right) + 1} \mid (c\left(p \cdot m\right) - c\left(m\right)))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.Dold` (`✓ std3`).

*Citation.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

Dold(c) requires divisibility by p to the valuation of m plus one for every prime p and every nonzero natural m.

**Definition 1.2 (The rational logarithmic input).**

$$\forall c: \mathbb{N} \to \mathbb{Z}, \operatorname{logInput}\left(c\right) = \operatorname{mk}\left((fun n: \mathbb{N} \mapsto \frac{(c\left(n\right): \mathbb{Q})}{(n: \mathbb{Q})})\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.logInput` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

The degree-n input coefficient is c(n)/n over the rationals; rational division makes the constant coefficient zero.

**Theorem 1.3 (Scaling the input takes powers).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies (\forall n: \mathbb{N}, \operatorname{subst}\left(\operatorname{HSMul.hSMul}\left(n, f\right), \operatorname{exp}\left(\mathbb{Q}\right)\right) = \operatorname{subst}\left(f, \operatorname{exp}\left(\mathbb{Q}\right)\right)^{n})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_nsmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

The zero-constant inputs satisfy the exponential addition law. Induction on n gives the identity for natural scalar multiplication.

**Theorem 1.4 (Dold congruences imply integrality).**

$$\forall c: \mathbb{N} \to \mathbb{Z}, (\operatorname{Dold}\left(c\right)) \implies (\forall n: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{coeff}\left(n, \operatorname{subst}\left(\operatorname{logInput}\left(c\right), \operatorname{exp}\left(\mathbb{Q}\right)\right)\right) = (z: \mathbb{Q}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.integral_exp_of_dold` (`✓ std3`). ∎

*Citation.* AINTLIB contributors (2026). *AINTLIB rational local integrality and the Dieudonne-Dwork criterion*. URL: <https://github.com/CBirkbeck/AINTLIB/blob/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/DieudonneDwork/DieudonneDworkCriterion.lean>.

*Commentary.*

Apply the sufficient Dieudonne-Dwork criterion at each prime. The Dold congruences make the logarithmic difference locally integral; a rational coefficient integral at every prime has denominator one. The local-integrality induction is adapted from AINTLIB.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.Dold`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_nsmul`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.integral_exp_of_dold`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.logInput`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure](HannaLogarithmicPowerClosure.md)
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](../Invariants/CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport](../LinearRows/LinearExponentDyadicSupport.md)
- Dependency: [D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence](../Residue/ParametricExponentialSquareCongruence.md)
