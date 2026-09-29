# Finite Closure of Dark Directions for General Instruments

## Abstract

For a general no-click instrument on a d-dimensional space, the dark layers are the kernels of the survival defects, they stop changing after d steps, and the last layer is the largest subspace that every click operator annihilates and every no-click operator maps into itself.

**Definition 1.1 (The dual no-click map).**

$$\mathcal{A}(X) = \sum_{a \in \alpha} Q_{a}^{*} X Q_{a}$$

*Formalization.* `D5/S3/Quantum/Measurement/GeneralInstrumentDarkClosure.noClickDual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The no-click operation acts by the Kraus operators Q_a, labelled by the finite unread set alpha; its dual on effects is the map above.

**Definition 1.2 (Survival effects).**

$$S_{0} = I,\qquad S_{n+1} = \mathcal{A}(S_{n})$$

*Formalization.* `D5/S3/Quantum/Measurement/GeneralInstrumentDarkClosure.survival` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The n-step survival effect is the n-fold dual no-click map applied to the identity.

**Definition 1.3 (Dark layers).**

$$D_{0} = \mathbb{C}^{d},\qquad D_{n+1} = \{v \in \mathbb{C}^{d} \mid L_{i} v = 0 \text{ for all }i, Q_{a} v \in D_{n} \text{ for all }a\}$$

*Formalization.* `D5/S3/Quantum/Measurement/GeneralInstrumentDarkClosure.darkLayer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vector lies in the next layer when no click operator L_i sees it and every unread no-click branch sends it into the current layer.

**Theorem 1.4 (Finite closure of the dark layers).**

$$\sum_{a \in \alpha} Q_{a}^{*} Q_{a} + \sum_{i \in \iota} L_{i}^{*} L_{i} = I \Rightarrow\\{}\forall n, D_{n} = \operatorname{ker}(I-S_{n}),\quad \forall n \geq d, D_{n} = D_{d},\\{}L_{i} D_{d} = 0, Q_{a} D_{d} \subseteq D_{d} \text{ for all }i, a,\\{}\forall V \subseteq \mathbb{C}^{d}, (L_{i} V = 0 \land Q_{a} V \subseteq V \text{ for all }i, a) \Rightarrow V \subseteq D_{d}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/GeneralInstrumentDarkClosure.darkLayer_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let alpha and iota be finite, let Q_a be the no-click and L_i the click Kraus operators on the d-dimensional space, and assume the completeness relation. The defect I - S_{n+1} equals the sum of L_i^* L_i and of Q_a^* (I - S_n) Q_a, so every defect is positive semidefinite, and the kernel of a sum of positive semidefinite operators is the intersection of their kernels. By induction the kernel of I - S_n is the n-th dark layer. The layers decrease; one equality between consecutive layers persists forever, and every strict step lowers the dimension, so the layers are constant from n = d on. The stable layer is annihilated by every L_i and mapped into itself by every Q_a, and by induction every subspace with these two properties lies in every layer.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/GeneralInstrumentDarkClosure.darkLayer`
- Truth anchor: `D5/S3/Quantum/Measurement/GeneralInstrumentDarkClosure.darkLayer_closure`
- Truth anchor: `D5/S3/Quantum/Measurement/GeneralInstrumentDarkClosure.noClickDual`
- Truth anchor: `D5/S3/Quantum/Measurement/GeneralInstrumentDarkClosure.survival`
