# Finite Closure of First-Event Effect Spaces

## Abstract

For a general no-click instrument on a d-dimensional space, the real spaces spanned by the identity and the first-event effects stop growing within d^2 rounds, and the stable space is invariant under the dual no-click map.

**Definition 1.1 (Click effects).**

$$B_{x} = \sum_{\operatorname{lab}(i) = x} L_{i}^{*} L_{i}$$

*Formalization.* `D5/S3/Quantum/Measurement/GeneralInstrumentEffectClosure.clickEffect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The click Kraus operator L_i records the readable outcome lab(i); the effect of outcome x collects all click operators with that label.

**Definition 1.2 (Effect spaces).**

$$V_{N} = \operatorname{span}_{\mathbb{R}}(\{I\} \cup \{\mathcal{A}^{n}(B_{x}) \mid n < N, x \in \xi\})$$

*Formalization.* `D5/S3/Quantum/Measurement/GeneralInstrumentEffectClosure.effectSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real linear span, inside the complex d by d matrices, of the identity and the effects of all first clicks within the first N rounds.

**Theorem 1.3 (Finite closure of the effect spaces).**

$$d \geq 1 \land \sum_{a \in \alpha} Q_{a}^{*} Q_{a} + \sum_{i \in \iota} L_{i}^{*} L_{i} = I \Rightarrow\\{}\exists N_{*}, 1 \leq N_{*} \leq d^{2},\quad \forall N \geq N_{*}, V_{N} = V_{N_{*}},\quad \mathcal{A}(V_{N_{*}}) \subseteq V_{N_{*}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/GeneralInstrumentEffectClosure.effectSpace_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let alpha and iota be finite, let Q_a be the no-click and L_i the click Kraus operators with the completeness relation and d >= 1. Since A(I) = I minus the sum of the click effects and A applied to A^n(B_x) is A^{n+1}(B_x), the spaces satisfy V_{N+1} = V_1 + A(V_N); so one equality V_{k+1} = V_k persists for all later N, and it also shows A(V_k) inside V_k. Every generator is Hermitian, and the Hermitian d by d matrices form a real space of dimension d^2, so every V_N has real dimension at most d^2. As V_1 contains the identity and each strict step raises the dimension, some k between 1 and d^2 satisfies V_{k+1} = V_k.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/GeneralInstrumentEffectClosure.clickEffect`
- Truth anchor: `D5/S3/Quantum/Measurement/GeneralInstrumentEffectClosure.effectSpace`
- Truth anchor: `D5/S3/Quantum/Measurement/GeneralInstrumentEffectClosure.effectSpace_closure`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
- Dependency: [D5/S3/Quantum/Measurement/GeneralInstrumentDarkClosure](GeneralInstrumentDarkClosure.md)
- Dependency: [D5/S3/Quantum/PredictionDepth/FiniteSequentialWordCertificate](../PredictionDepth/FiniteSequentialWordCertificate.md)
