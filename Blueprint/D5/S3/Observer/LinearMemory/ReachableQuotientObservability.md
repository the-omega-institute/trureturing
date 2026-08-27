# Reachable Quotient Observability

## Abstract

Zero future output identifies the zero class in the reachable-state quotient.

**Theorem 1.1 (The reachable quotient is observable).**

$$\begin{aligned}\forall K, State, Input, Output: \operatorname{Type},\\{}[\operatorname{Field}(K)], [\operatorname{AddCommGroup}(State)], [\operatorname{Module}(K, State)],\\{}[\operatorname{AddCommGroup}(Input)], [\operatorname{Module}(K, Input)], [\operatorname{AddCommGroup}(Output)], [\operatorname{Module}(K, Output)],\\\forall A: \operatorname{LinearMap}(K, State, State), B: \operatorname{LinearMap}(K, Input, State), C: \operatorname{LinearMap}(K, State, Output),\\{}let R: \operatorname{Submodule}(K, State) = \operatorname{span}(K, \operatorname{range}({\Lambda p: \operatorname{Prod}(\mathbb{N}, Input), \operatorname{A^{{\operatorname{fst}(p)}}}(\operatorname{B}(\operatorname{snd}(p)))}));\\{}let N: \operatorname{Submodule}(K, State) = \operatorname{iInf}({\Lambda k: \mathbb{N}, \operatorname{ker}(\operatorname{comp}(C, A^{{k}}))});\\{}let D: \operatorname{Submodule}(K, R) = \operatorname{comap}(\operatorname{subtype}(R), N);\\{}\forall x: R, (\forall k: \mathbb{N}, \operatorname{C}(\operatorname{A^{{k}}}(x)) = 0) \Rightarrow \operatorname{mkQ}(D, x) = 0.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/ReachableQuotientObservability.reachable_quotient_observability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reachable carrier is the span of all iterated input directions. The hidden carrier is the intersection of every future readout kernel, and the residual is its pullback to the reachable carrier.

If every future output of a reachable representative is zero, that representative belongs to the hidden carrier. Membership in the residual then makes its canonical quotient class zero.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/ReachableQuotientObservability.reachable_quotient_observability`
- Dependency: [D5/S3/Observer/Linear/ReachableObservableQuotientDescent](../Linear/ReachableObservableQuotientDescent.md)
