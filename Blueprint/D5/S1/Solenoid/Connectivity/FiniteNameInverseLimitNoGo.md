# Finite-Name Inverse-Limit No-Go

## Abstract

Continuous finite-name inverse-limit readings of a connected space are constant.

**Theorem 1.1 (A finite-name inverse limit cannot distinguish a connected space).**

$$\forall X: \operatorname{Type},\ [\operatorname{TopologicalSpace}(X)], [\operatorname{ConnectedSpace}(X)],\ finiteNames: \operatorname{Functor}(\operatorname{Opposite}(\mathbb{N}), FintypeCat),\ name: X \to \operatorname{ProfiniteLimit}(\operatorname{toProfinite}(finiteNames)), \operatorname{Continuous}(name) \Rightarrow\\{\forall x, y: X, \operatorname{name}(x) = \operatorname{name}(y)} \land\\{\forall x0: X, \operatorname{range}(name) = \{\operatorname{name}(x0)\}} \land\\{\operatorname{Injective}(name) \Rightarrow \operatorname{Subsingleton}(X)}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/Connectivity/FiniteNameInverseLimitNoGo.finite_name_inverse_limit_no_go` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let finiteNames be a sequential diagram of finite sets, each carrying its discrete topology, and let name map a connected space X continuously into the canonical profinite limit of that diagram.

Every two values of name coincide. Consequently its range is exactly the singleton containing the value at any chosen point of X; if name is also injective, X itself is a subsingleton.

Pinned Mathlib supplies the canonical profinite limit cone and the exact theorem that a continuous map from a connected space to a totally disconnected space is constant. Repository search found only single-discrete-target and particular-product specializations.

## References

- Truth anchor: `D5/S1/Solenoid/Connectivity/FiniteNameInverseLimitNoGo.finite_name_inverse_limit_no_go`
