# Golden Germ Structural Simple Pole

## Abstract

The second-order golden germ has a genuine simple structural pole.

**Theorem 1.1 (The second extracted zeta factor gives a simple pole).**

$$\begin{aligned}H: \mathbb{C} \to \mathbb{C},\\\forall s\in \mathbb{C}, \operatorname{H}(s) := \prod_{p\in \operatorname{Primes}(\mathbb{N})}(1 - p^{-s \times \varphi^{3}}) \times (1 + p^{-s \times \varphi^{2}})^{-1} \times \sum_{v\in \mathbb{N}}p^{-s \times \operatorname{o5Beta}(v)},\\F: \mathbb{C} \to \mathbb{C},\\\forall s\in \mathbb{C}, \operatorname{F}(s) := \operatorname{riemannZeta}(\varphi^{2} \times s) \times \operatorname{riemannZeta}(\varphi^{3} \times s) \times (\operatorname{riemannZeta}(2 \times \varphi^{2} \times s))^{-1} \times \operatorname{H}(s),\\\operatorname{MeromorphicAt}(F, \frac{1}{\varphi^{3}}) \land\\\operatorname{meromorphicOrderAt}(F, \frac{1}{\varphi^{3}}) = -1 \land\\\operatorname{Tendsto}(F, \operatorname{nhdsWithin}(\frac{1}{\varphi^{3}}, \mathbb{C} \setminus \{\frac{1}{\varphi^{3}}\}), \operatorname{cobounded}(\mathbb{C})).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/GoldenGermStructuralSimplePole.golden_germ_structural_simple_pole` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set a equal to one over phi cubed. In the frozen second-order factorization, zeta at phi cubed times s is the pole factor; the product of zeta at phi squared times s, the reciprocal zeta factor at twice phi squared times s, and H is the regular multiplier.

GoldenGermSecondNormalizedFactorRegularity makes H analytic and nonzero at a. GoldenAuxiliaryZetaNonzero supplies the nonzero value zeta of one over phi, and the standard right-half-plane zeta theorem supplies nonvanishing at two over phi, where the concrete inequality one less than two over phi is verified.

Transporting the residue-one extension through multiplication by phi cubed yields an analytic nonzero residue. The resulting punctured normal form has exponent minus one, so the germ is meromorphic of exact order minus one and tends to the cobounded filter.

The real point a is exactly D5.X_Frontier.Hearts.structuralPole by that frontier definition, which is one over phi cubed. The Lean module deliberately uses the numeric point and does not import the open Hearts module.

Within the golden Euler-germ extraction ladder associated with OACTC parts 580 and 581, this closes the local boundary left by the second extracted zeta factor on the RH-route O-5 control line. It does not prove O-5, does not prove RH, and makes no claim about zeros or other points.

## References

- Truth anchor: `D5/S3/Analytic/Isolation/GoldenGermStructuralSimplePole.golden_germ_structural_simple_pole`
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderFactorization](../EulerGerm/GoldenGermSecondOrderFactorization.md)
- Dependency: [D5/S3/Analytic/Isolation/GoldenAuxiliaryZetaNonzero](GoldenAuxiliaryZetaNonzero.md)
- Dependency: [D5/S3/Analytic/Isolation/GoldenGermZetaSimplePole](GoldenGermZetaSimplePole.md)
- Dependency: [D5/S3/Analytic/Regularity/GoldenGermSecondNormalizedFactorRegularity](../Regularity/GoldenGermSecondNormalizedFactorRegularity.md)
