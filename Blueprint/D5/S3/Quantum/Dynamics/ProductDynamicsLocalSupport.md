# Product Dynamics Local Support

## Abstract

Product pullbacks preserve exact local support or lower it within the active factors.

**Theorem 1.1 (Product pullbacks cannot create support outside the active set).**

$$\begin{gathered}\forall \iota: \operatorname{Type}(), \operatorname{DecidableEq}(\iota),\\{}M: \iota \to \operatorname{Type}(),\\{}(\forall i: \iota, \operatorname{AddCommGroup}(M\left(i\right)) \land \operatorname{Module}(\mathbb{R}, M\left(i\right))),\\{}I: \prod_{i: \iota} M\left(i\right), tr: \prod_{i: \iota} \operatorname{LinearMap}(\mathbb{R}, M\left(i\right), \mathbb{R}),\\{}(\forall i: \iota, tr\left(i\right)\left(I\left(i\right)\right) = 1),\\{}phi: \prod_{i: \iota} \operatorname{LinearMap}(\mathbb{R}, M\left(i\right), M\left(i\right)),\\{}(\forall i: \iota, phi\left(i\right)\left(I\left(i\right)\right) = I\left(i\right)),\\{}S: \operatorname{Finset}(\iota),\\{}\text{let } U: \prod_{i: \iota} \operatorname{Submodule}(\mathbb{R}, M\left(i\right)) := i \mapsto \operatorname{span}(\mathbb{R}, \{I\left(i\right)\});\\{}Z: \prod_{i: \iota} \operatorname{Submodule}(\mathbb{R}, M\left(i\right)) := i \mapsto \operatorname{ker}(tr\left(i\right));\\{}V: \operatorname{Finset}(\iota) \to \operatorname{Submodule}(\mathbb{R}, \operatorname{PiTensorProduct}(\mathbb{R}, M)) := R \mapsto \operatorname{range}(\operatorname{PiTensorMapIncl}(\mathbb{R}, \operatorname{factorFamily}(i \mapsto \operatorname{ifMem}(i, R, Z\left(i\right), U\left(i\right)))));\\{}pullback: \operatorname{LinearMap}(\mathbb{R}, \operatorname{PiTensorProduct}(\mathbb{R}, M), \operatorname{PiTensorProduct}(\mathbb{R}, M)) := \operatorname{PiTensorMap}(\mathbb{R}, phi);\\{}(\forall A: \operatorname{PiTensorProduct}(\mathbb{R}, M), A \in V\left(S\right) \Rightarrow pullback\left(A\right) \in \operatorname{iSup}(\{T: \operatorname{Finset}(\iota) \mid T \subseteq S\}, T \mapsto V\left(T\right))) \land\\{}((\forall i: \iota, \operatorname{map}(phi\left(i\right), Z\left(i\right)) \subseteq Z\left(i\right)) \Rightarrow\\{}\forall A: \operatorname{PiTensorProduct}(\mathbb{R}, M), A \in V\left(S\right) \Rightarrow pullback\left(A\right) \in V\left(S\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/ProductDynamicsLocalSupport.product_pullback_local_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A normalized identity direction and a local trace map construct the scalar sector U as its real span and the trace-zero sector Z as the trace kernel. No abstract sector decomposition is assumed.

The dynamics is the canonical tensor map induced by the local linear pullbacks. Scalar-sector invariance prevents a new active factor; multilinearity expands every active local sum over subsets of S.

If the local pullbacks also preserve every Z sector, the same restriction map factors the product pullback through the original sector V(S).

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/ProductDynamicsLocalSupport.product_pullback_local_support`
