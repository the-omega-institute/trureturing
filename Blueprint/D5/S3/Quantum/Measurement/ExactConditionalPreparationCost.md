# Exact Conditional Preparation Cost

## Abstract

Exact universal conditional preparation is a scalar square-root filter, with optimal worst-case success equal to the spectral endpoint ratio.

**Definition 1.1 (Kraus action).**

$$\operatorname{krausAction}(K, X) = \sum_{j \in \operatorname{Fin}(m)} K(j) \cdot X \cdot \operatorname{star}(K(j))$$

*Formalization.* `D5/S3/Quantum/Measurement/ExactConditionalPreparationCost.krausAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite Kraus family sends a matrix to the sum of its conjugated branches.

**Definition 1.2 (Exact conditional preparation contract).**

$$\forall rho: \operatorname{Matrix}(Iota, Iota, \mathbb{C}), (\operatorname{PosSemidef}(rho) \land \\{}\operatorname{Tr}(rho) = 1) \Rightarrow 0 < \operatorname{Re}(\operatorname{Tr}(\operatorname{krausAction}(K, rho))) \land \\{}\operatorname{Im}(\operatorname{Tr}(\operatorname{krausAction}(K, rho))) = 0 \land \\{}\operatorname{krausAction}(K, rho) = \operatorname{Tr}(\operatorname{krausAction}(K, rho)) / \operatorname{Tr}(R \cdot rho) \cdot \operatorname{sqrt}(R) \cdot rho \cdot \operatorname{sqrt}(R)$$

*Formalization.* `D5/S3/Quantum/Measurement/ExactConditionalPreparationCost.ExactPreparationContract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On every positive trace-one input, the output has positive real trace, zero imaginary trace, and is the normalized positive-square-root sandwich associated with the effect.

**Definition 1.3 (Trace-nonincreasing Kraus family).**

$$\operatorname{PosSemidef}(I - \sum_{j \in \operatorname{Fin}(m)} \operatorname{star}(K(j)) \cdot K(j))$$

*Formalization.* `D5/S3/Quantum/Measurement/ExactConditionalPreparationCost.TraceNonincreasing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Kraus family is trace-nonincreasing when the identity minus its total effect is positive semidefinite.

**Definition 1.4 (Least eigenvalue).**

$$\operatorname{leastEigenvalue}(R) = \operatorname{inf}(\operatorname{eigenvalues}(R))$$

*Formalization.* `D5/S3/Quantum/Measurement/ExactConditionalPreparationCost.leastEigenvalue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The least eigenvalue is the infimum of the finite Hermitian eigenvalue family.

**Definition 1.5 (Greatest eigenvalue).**

$$\operatorname{greatestEigenvalue}(R) = \operatorname{sup}(\operatorname{eigenvalues}(R))$$

*Formalization.* `D5/S3/Quantum/Measurement/ExactConditionalPreparationCost.greatestEigenvalue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The greatest eigenvalue is the supremum of the finite Hermitian eigenvalue family.

**Theorem 1.6 (Rigidity, optimal cost, and determinism).**

$$\forall Iota: \operatorname{Type}, \operatorname{Fintype}(Iota), \operatorname{DecidableEq}(Iota), \operatorname{Nonempty}(Iota),\\{}R: \operatorname{Matrix}(Iota, Iota, \mathbb{C}), \operatorname{PosDef}(R),\\{}\forall m: \mathbb{N}, \forall K: (\operatorname{Fin}(m)) \to \operatorname{Matrix}(Iota, Iota, \mathbb{C}), (\operatorname{ExactPreparationContract}(R, K)) \Rightarrow \exists c: \mathbb{R}, 0 < c \land \\{}\forall X: \operatorname{Matrix}(Iota, Iota, \mathbb{C}), \operatorname{krausAction}(K, X) = c \cdot \operatorname{sqrt}(R) \cdot X \cdot \operatorname{sqrt}(R) \land \\{}\forall m: \mathbb{N}, \forall K: (\operatorname{Fin}(m)) \to \operatorname{Matrix}(Iota, Iota, \mathbb{C}), \forall c: \mathbb{R}, (0 < c) \Rightarrow (\forall X: \operatorname{Matrix}(Iota, Iota, \mathbb{C}), \operatorname{krausAction}(K, X) = c \cdot \operatorname{sqrt}(R) \cdot X \cdot \operatorname{sqrt}(R)) \Rightarrow \operatorname{TraceNonincreasing}(K) \iff \operatorname{PosSemidef}(I - c \cdot R) \land \\{}\forall m: \mathbb{N}, \forall K: (\operatorname{Fin}(m)) \to \operatorname{Matrix}(Iota, Iota, \mathbb{C}), (\operatorname{ExactPreparationContract}(R, K)) \Rightarrow (\operatorname{TraceNonincreasing}(K)) \Rightarrow \exists rho: \operatorname{Matrix}(Iota, Iota, \mathbb{C}), \operatorname{PosSemidef}(rho) \land \\{}\operatorname{Tr}(rho) = 1 \land \\{}\operatorname{Re}(\operatorname{Tr}(\operatorname{krausAction}(K, rho))) \le \operatorname{leastEigenvalue}(R) / \operatorname{greatestEigenvalue}(R) \land \\{}\operatorname{let} Kopt(j) = 1 / \sqrt{\operatorname{greatestEigenvalue}(R)} \cdot \operatorname{sqrt}(R); \operatorname{ExactPreparationContract}(R, Kopt) \land \\{}\operatorname{TraceNonincreasing}(Kopt) \land \\{}\forall rho: \operatorname{Matrix}(Iota, Iota, \mathbb{C}), (\operatorname{PosSemidef}(rho) \land \\{}\operatorname{Tr}(rho) = 1) \Rightarrow \operatorname{leastEigenvalue}(R) / \operatorname{greatestEigenvalue}(R) \le \operatorname{Re}(\operatorname{Tr}(\operatorname{krausAction}(Kopt, rho))) \land \\{}(\exists m: \mathbb{N}, \exists K: (\operatorname{Fin}(m)) \to \operatorname{Matrix}(Iota, Iota, \mathbb{C}), \operatorname{ExactPreparationContract}(R, K) \land \\{}\operatorname{TraceNonincreasing}(K) \land \\{}\forall rho: \operatorname{Matrix}(Iota, Iota, \mathbb{C}), (\operatorname{PosSemidef}(rho) \land \\{}\operatorname{Tr}(rho) = 1) \Rightarrow \operatorname{Tr}(\operatorname{krausAction}(K, rho)) = 1) \iff \exists lambda: \mathbb{R}, 0 < lambda \land \\{}R = lambda \cdot I.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ExactConditionalPreparationCost.exact_conditional_preparation_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every exact universal preparation family is a positive scalar multiple of the square-root sandwich channel. Its total effect is the same scalar multiple of the prescribed effect, so trace nonincrease bounds the scalar by the reciprocal largest eigenvalue. A largest-eigenvalue input gives the upper bound, while the reciprocal-square-root filter attains the least-to-largest eigenvalue ratio. Deterministic preparation is possible exactly when the effect is a positive scalar identity.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/ExactConditionalPreparationCost.ExactPreparationContract`
- Truth anchor: `D5/S3/Quantum/Measurement/ExactConditionalPreparationCost.TraceNonincreasing`
- Truth anchor: `D5/S3/Quantum/Measurement/ExactConditionalPreparationCost.exact_conditional_preparation_cost`
- Truth anchor: `D5/S3/Quantum/Measurement/ExactConditionalPreparationCost.greatestEigenvalue`
- Truth anchor: `D5/S3/Quantum/Measurement/ExactConditionalPreparationCost.krausAction`
- Truth anchor: `D5/S3/Quantum/Measurement/ExactConditionalPreparationCost.leastEigenvalue`
- Dependency: [D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal](FiniteKrausInstrumentBornMarginal.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
