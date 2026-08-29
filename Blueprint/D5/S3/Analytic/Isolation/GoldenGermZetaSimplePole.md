# Golden Germ Zeta Simple Pole

## Abstract

The golden germ zeta function has a genuine simple pole at one over phi squared.

**Theorem 1.1 (The golden germ zeta function has a simple boundary pole).**

$$\begin{aligned}germZeta: \mathbb{C} \to \mathbb{C},\\\forall s\in \mathbb{C}, \operatorname{germZeta}(s) := \operatorname{riemannZeta}(\varphi^{2} \times s) \times \prod_{p\in \operatorname{Primes}(\mathbb{N})}(1 - p^{-s \times \varphi^{2}}) \times \sum_{v\in \mathbb{N}}p^{-s \times \operatorname{o5Beta}(v)},\\\operatorname{MeromorphicAt}(germZeta, \frac{1}{\varphi^{2}}) \land\\\operatorname{meromorphicOrderAt}(germZeta, \frac{1}{\varphi^{2}}) = -1 \land\\\operatorname{Tendsto}(germZeta, \operatorname{nhdsWithin}(\frac{1}{\varphi^{2}}, \mathbb{C} \setminus \{\frac{1}{\varphi^{2}}\}), \operatorname{cobounded}(\mathbb{C})).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/GoldenGermZetaSimplePole.golden_germ_zeta_simple_pole` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set a equal to one over phi squared and let G be the normalized prime product. The residue function is the analytic extension of (z-1) zeta(z), evaluated at phi squared times s, multiplied by G(s) over phi squared.

Pinned Mathlib supplies the zeta residue, the removable-singularity extension mechanism, the meromorphic local normal form, and the order criterion. GoldenGermNormalizedFactorRegularity makes G analytic at a, while GoldenGermZetaBoundary makes G(a) nonzero.

The residue function is therefore analytic and nonzero at a, with value G(a) over phi squared. On the punctured neighborhood, the germ equals (s-a)^(-1) times this residue function. Its meromorphic order is consequently minus one, and the negative order criterion gives convergence to the cobounded filter.

STOPPING JUSTIFICATION: this theorem closes the boundary singularity question left open by GoldenGermZetaBoundary, using the regularity input supplied by GoldenGermNormalizedFactorRegularity. It says nothing about other points, nothing about the zero set, and nothing about the germ away from the displayed punctured neighborhood.

## References

- Truth anchor: `D5/S3/Analytic/Isolation/GoldenGermZetaSimplePole.golden_germ_zeta_simple_pole`
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermZetaBoundary](../EulerGerm/GoldenGermZetaBoundary.md)
- Dependency: [D5/S3/Analytic/Regularity/GoldenGermNormalizedFactorRegularity](../Regularity/GoldenGermNormalizedFactorRegularity.md)
