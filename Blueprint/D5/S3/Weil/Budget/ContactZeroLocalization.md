# Contact-Zero Localization

## Abstract

Vague convergence of finite contact spectra localizes an indexed positive atom near every enumerated zero ordinate.

**Theorem 1.1 (Finite contact spectra localize positive atoms).**

$$\begin{aligned}\forall Z: \operatorname{ZeroData}(), n0: \mathbb{N},\\M: \mathbb{N} \to \mathbb{N}, G: \mathbb{N} \to \mathbb{R} \to \mathbb{C},\\tau: \forall n: \mathbb{N}, \operatorname{Fin}(\operatorname{apply}(M, n)) \to \operatorname{Subtype}(xi: \mathbb{R}, \operatorname{apply}(\operatorname{apply}(G, n), xi) = 0),\\c: \forall n: \mathbb{N}, \operatorname{Fin}(\operatorname{apply}(M, n)) \to ENNReal,\\U: \operatorname{Set}(\mathbb{R}), \operatorname{IsOpen}(U) \land \operatorname{mem}(\operatorname{im}(\operatorname{zero}(Z, n0)), U) \land\\\forall phi \in \mathbb{R} \to \mathbb{R},\; \operatorname{Continuous}(phi) \land \operatorname{HasCompactSupport}(phi) \land (\forall xi \in \mathbb{R},\; 0 \leq \operatorname{apply}(phi, xi)) \Rightarrow \operatorname{Tendsto}((n: \mathbb{N} \mapsto \operatorname{lintegral}(\operatorname{sumMeasure}((j: \operatorname{Fin}(\operatorname{apply}(M, n)) \mapsto \operatorname{apply}(\operatorname{apply}(c, n), j) \cdot \operatorname{dirac}(\operatorname{val}(\operatorname{apply}(\operatorname{apply}(tau, n), j))))), (xi: \mathbb{R} \mapsto \operatorname{ofReal}(\operatorname{apply}(phi, xi))))), \operatorname{atTop}(), \operatorname{nhds}(\operatorname{lintegral}(\operatorname{zeroCountingMeasure}(Z), (xi: \mathbb{R} \mapsto \operatorname{ofReal}(\operatorname{apply}(phi, xi)))))) \Rightarrow\\\operatorname{EventuallyAtTop}((n: \mathbb{N} \mapsto \exists j \in \operatorname{Fin}(\operatorname{apply}(M, n)),\; 0 < \operatorname{apply}(\operatorname{apply}(c, n), j) \land \operatorname{mem}(\operatorname{val}(\operatorname{apply}(\operatorname{apply}(tau, n), j)), U))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/ContactZeroLocalization.contact_zero_localization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed contact atoms are indexed directly. Their subtype records the transform-zero equation, and the residual measure is the corresponding finite positive Dirac sum.

A compactly supported smooth bump at the selected ordinate has positive integral against the multiplicity-weighted target measure. Vague convergence makes its residual integral eventually positive.

Expanding that residual integral as a finite sum produces an indexed positive-weight atom in the bump support and hence in the chosen open neighborhood. No separate isolation premise is needed.

## References

- Truth anchor: `D5/S3/Weil/Budget/ContactZeroLocalization.contact_zero_localization`
- Dependency: [D5/S3/Weil/Budget/GroundStateZeroLocalization](GroundStateZeroLocalization.md)
