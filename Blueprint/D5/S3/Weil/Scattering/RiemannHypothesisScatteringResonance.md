# Riemann Hypothesis in Scattering Resonance Coordinates

## Abstract

The Riemann hypothesis is equivalent to the quarter-line scattering resonance condition and to its reflected three-quarter-line antiresonance condition.

**Theorem 1.1 (RH has the quarter-line resonance and three-quarter-line zero forms).**

$$\begin{gathered}(RH \Leftrightarrow \forall s\in \mathbb{C},\ \operatorname{Pole}_{\phi}(s) \Rightarrow \Re(s)=\frac{1}{4}) \land\\\operatorname{EventuallyEq}_{\operatorname{codiscrete}(\mathbb{C})}(\phi(s)\phi(1-s), 1) \land\\(\forall \rho\in \mathbb{C},\ \operatorname{IsNontrivialZero}(\rho) \Rightarrow \operatorname{Zero}_{\phi}(1-s_{\rho})) \land\\(RH \Leftrightarrow \forall s\in \mathbb{C},\ \operatorname{Zero}_{\phi}(s) \Rightarrow \Re(s)=\frac{3}{4}) \land\\(\forall \rho\in \mathbb{C},\ \Re(\rho)=\frac{1}{2} \Rightarrow \Re(s_{\rho})=\frac{1}{4}) \land\\(\forall \rho\in \mathbb{C},\ \Re(\rho)=\frac{1}{2} \Rightarrow \Re(1-s_{\rho})=\frac{3}{4}). \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Scattering/RiemannHypothesisScatteringResonance.riemann_hypothesis_scattering_resonance_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here Phi(s) is the concrete completed-zeta ratio Lambda(2s-1)/Lambda(2s). Pole_Phi(s) means that its completed-zeta denominator vanishes, Zero_Phi(s) means that its numerator vanishes, and s_rho is rho/2. These are the named Lean definitions, not abstract replacement carriers.

The displayed conjunction retains all six Lean leaves. Both RH biconditionals contribute their forward and reverse assertions; the last two leaves separately retain the resonance and antiresonance coordinates of the final boxed split.

The product Phi(s)Phi(1-s)=1 is stated as an eventual equality on the codiscrete complex filter. This is the Lean formulation of the meromorphic identity: it removes only the discrete zero and pole locus, rather than falsely asserting an equality of totalized division values at exceptional points.

The reflected-zero leaf uses the completed-zeta functional equation. The two reverse implications additionally use the pinned exterior zero-free theorems and Gamma-factor zero classification to recover mathlib's full RiemannHypothesis predicate.

## References

- Truth anchor: `D5/S3/Weil/Scattering/RiemannHypothesisScatteringResonance.riemann_hypothesis_scattering_resonance_form`
- Dependency: [D5/S3/Weil/Scattering/CompletedZetaScatteringCollapse](CompletedZetaScatteringCollapse.md)
