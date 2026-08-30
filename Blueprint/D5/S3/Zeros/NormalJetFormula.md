# Normal Jet Formula

## Abstract

The actual completed-xi normal intensity determines every even Taylor coefficient.

**Definition 1.1 (Critical-line xi reading).**

Lean statement: `D5/S3/Zeros/NormalJetFormula.criticalXi`

*Formalization.* `D5/S3/Zeros/NormalJetFormula.criticalXi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a real ordinate t, this is the real part of the canonical completed-xi owner xiReading evaluated at one-half plus i times t. The imported conjugate-reflection theorem proves that this value is real.

**Definition 1.2 (Actual normal intensity).**

Lean statement: `D5/S3/Zeros/NormalJetFormula.normalIntensity`

*Formalization.* `D5/S3/Zeros/NormalJetFormula.normalIntensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real displacement delta and ordinate t, this is the complex norm squared of the canonical xiReading at one-half plus delta plus i times t. It is the source intensity itself, not a manufactured formal series.

**Definition 1.3 (Even normal Taylor coefficient).**

Lean statement: `D5/S3/Zeros/NormalJetFormula.normalJet`

*Formalization.* `D5/S3/Zeros/NormalJetFormula.normalJet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At depth m, the normal jet is the real iterated derivative of order 2m of the actual normal intensity at displacement zero, divided by 2m factorial. It is not defined by the convolution formula below.

**Theorem 1.4 (The completed-xi normal jet formula).**

$$\begin{gathered}\forall t: \mathbb{R},\\{}(\forall m: \mathbb{N}, \operatorname{normalJet}\left(t, m\right) = \sum_{j=0}^{2m} \frac{(-1)^{m + j}}{\operatorname{factorial}\left(j\right) \cdot \operatorname{factorial}\left(2m - j\right)} \cdot \operatorname{iteratedDeriv}\left(j, criticalXi, t\right) \cdot \operatorname{iteratedDeriv}\left(2m - j, criticalXi, t\right)) \land\\{}\operatorname{normalJet}\left(t, 0\right) = \operatorname{criticalXi}\left(t\right)^{2} \land\\{}\operatorname{normalJet}\left(t, 1\right) = \operatorname{iteratedDeriv}\left(1, criticalXi, t\right)^{2} - \operatorname{criticalXi}\left(t\right) \cdot \operatorname{iteratedDeriv}\left(2, criticalXi, t\right) \land\\{}\operatorname{normalJet}\left(t, 2\right) = \frac{1}{4} \cdot \operatorname{iteratedDeriv}\left(2, criticalXi, t\right)^{2} - \frac{1}{3} \cdot \operatorname{iteratedDeriv}\left(1, criticalXi, t\right) \cdot \operatorname{iteratedDeriv}\left(3, criticalXi, t\right) + \frac{1}{12} \cdot \operatorname{criticalXi}\left(t\right) \cdot \operatorname{iteratedDeriv}\left(4, criticalXi, t\right) \land\\{}\frac{\operatorname{iteratedDeriv}\left(2, (delta \mapsto \operatorname{normalIntensity}\left(delta, t\right)), 0\right)}{2} = \operatorname{iteratedDeriv}\left(1, criticalXi, t\right)^{2} - \operatorname{criticalXi}\left(t\right) \cdot \operatorname{iteratedDeriv}\left(2, criticalXi, t\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NormalJetFormula.normal_jet_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real ordinate, the first public conjunct gives every even Taylor coefficient of the actual completed-xi intensity as the signed factorial convolution of critical-line derivatives. Four further public conjuncts state the depth zero, one, and two cases and one half of the actual second displacement derivative.

The proof uses the frozen differentiability of xiReading and its frozen conjugate-reflection identity. A private entire extension identifies the product of the two affine critical-line channels with the real norm-squared intensity before the iterated product rule is applied.

Pinned mathlib supplies the iterated Leibniz rule, affine derivative laws, and the real-to-complex derivative bridges. No analyticity premise is added to the theorem because the canonical xiReading owner already proves global complex differentiability.

## References

- Truth anchor: `D5/S3/Zeros/NormalJetFormula.criticalXi`
- Truth anchor: `D5/S3/Zeros/NormalJetFormula.normalIntensity`
- Truth anchor: `D5/S3/Zeros/NormalJetFormula.normalJet`
- Truth anchor: `D5/S3/Zeros/NormalJetFormula.normal_jet_formula`
- Dependency: [D5/S3/Zeros/CompletedZeta](CompletedZeta.md)
- Dependency: [D5/S3/Zeros/Symmetry/ZetaConjugationCovariance](Symmetry/ZetaConjugationCovariance.md)
