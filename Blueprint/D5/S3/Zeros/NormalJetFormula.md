# Normal Jet Formula

## Abstract

The conjugate Taylor channels determine every even normal jet and its first three values.

**Definition 1.1 (Normal Taylor channel).**

Lean statement: `D5/S3/Zeros/NormalJetFormula.normalTaylorChannel`

*Formalization.* `D5/S3/Zeros/NormalJetFormula.normalTaylorChannel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a supplied real function, evaluation point, and complex direction, this formal power series has nth coefficient equal to the nth iterated derivative at that point times the nth directional phase divided by n factorial.

**Definition 1.2 (Normal intensity series).**

Lean statement: `D5/S3/Zeros/NormalJetFormula.normalIntensitySeries`

*Formalization.* `D5/S3/Zeros/NormalJetFormula.normalIntensitySeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formal normal intensity is constructed as the Cauchy product of the Taylor channels in directions minus i and plus i.

**Definition 1.3 (Even normal coefficient).**

Lean statement: `D5/S3/Zeros/NormalJetFormula.normalJet`

*Formalization.* `D5/S3/Zeros/NormalJetFormula.normalJet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At depth m, the normal jet is the real part of coefficient 2m in the constructed normal intensity series. It is not defined by the closed convolution formula proved below.

**Theorem 1.4 (The normal jet convolution and its first three values).**

$$\begin{gathered}\forall Xi: \mathbb{R} \to \mathbb{R}, t: \mathbb{R},\\{}(\forall m: \mathbb{N}, \operatorname{normalJet}\left(Xi, t, m\right) = \sum_{j=0}^{2m} \frac{(-1)^{m + j}}{\operatorname{factorial}\left(j\right) \cdot \operatorname{factorial}\left(2m - j\right)} \cdot \operatorname{iteratedDeriv}\left(j, Xi, t\right) \cdot \operatorname{iteratedDeriv}\left(2m - j, Xi, t\right)) \land\\{}\operatorname{normalJet}\left(Xi, t, 0\right) = \operatorname{Xi}\left(t\right)^{2} \land\\{}\operatorname{normalJet}\left(Xi, t, 1\right) = \operatorname{iteratedDeriv}\left(1, Xi, t\right)^{2} - \operatorname{Xi}\left(t\right) \cdot \operatorname{iteratedDeriv}\left(2, Xi, t\right) \land\\{}\operatorname{normalJet}\left(Xi, t, 2\right) = \frac{1}{4} \cdot \operatorname{iteratedDeriv}\left(2, Xi, t\right)^{2} - \frac{1}{3} \cdot \operatorname{iteratedDeriv}\left(1, Xi, t\right) \cdot \operatorname{iteratedDeriv}\left(3, Xi, t\right) + \frac{1}{12} \cdot \operatorname{Xi}\left(t\right) \cdot \operatorname{iteratedDeriv}\left(4, Xi, t\right) \land\\{}\frac{\Re{\operatorname{coeff}\left(0, \operatorname{derivative}\left(\mathbb{C}, \operatorname{derivative}\left(\mathbb{C}, \operatorname{normalIntensitySeries}\left(Xi, t\right)\right)\right)\right)}}{2} = \operatorname{iteratedDeriv}\left(1, Xi, t\right)^{2} - \operatorname{Xi}\left(t\right) \cdot \operatorname{iteratedDeriv}\left(2, Xi, t\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NormalJetFormula.normal_jet_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real function Xi and every real point t, the public statement gives the signed factorial convolution of Xi's iterated derivatives at arbitrary depth, then states the depth zero, one, and two expansions and the half-second-derivative identity as four additional public conjuncts.

The proof reads the coefficient of the Cauchy product of the two Taylor channels. The phase product is minus one to the power m+j, and two formal derivatives multiply coefficient two by two factorial. Thus the normal jet is constructed from channel semantics rather than defined to equal the target sum.

Repository body-shape and name searches found no existing normal-jet owner. Pinned mathlib supplies PowerSeries.mk, coeff_mul, the antidiagonal-to-range identity, derivative, and coeff_derivative; the deposited theorem directly applies those primitives.

## References

- Truth anchor: `D5/S3/Zeros/NormalJetFormula.normalIntensitySeries`
- Truth anchor: `D5/S3/Zeros/NormalJetFormula.normalJet`
- Truth anchor: `D5/S3/Zeros/NormalJetFormula.normalTaylorChannel`
- Truth anchor: `D5/S3/Zeros/NormalJetFormula.normal_jet_formula`
