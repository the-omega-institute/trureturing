# Reachable Observable Quotient Descent

## Abstract

Reachable-state dynamics, inputs, and outputs descend to the observable quotient.

**Theorem 1.1 (The reachable observable quotient carries the induced system).**

$$\begin{aligned}\forall K, State, Input, Output: \operatorname{Type},\\{}[\operatorname{Field}(K)], [\operatorname{AddCommGroup}(State)], [\operatorname{Module}(K, State)],\\{}[\operatorname{AddCommGroup}(Input)], [\operatorname{Module}(K, Input)], [\operatorname{AddCommGroup}(Output)], [\operatorname{Module}(K, Output)],\\\forall A: \operatorname{LinearMap}(K, State, State), B: \operatorname{LinearMap}(K, Input, State), C: \operatorname{LinearMap}(K, State, Output),\\{}let R: \operatorname{Submodule}(K, State) = \operatorname{span}(K, \operatorname{range}({\Lambda p: \operatorname{Prod}(\mathbb{N}, Input), \operatorname{A^{{\operatorname{fst}(p)}}}(\operatorname{B}(\operatorname{snd}(p)))}));\\{}let N: \operatorname{Submodule}(K, State) = \operatorname{iInf}({\Lambda k: \mathbb{N}, \operatorname{ker}(\operatorname{comp}(C, A^{{k}}))});\\{}let D: \operatorname{Submodule}(K, R) = \operatorname{comap}(\operatorname{subtype}(R), N);\\{}\operatorname{MapsTo}(A, R, R) \land \operatorname{MapsTo}(A, N, N) \land\\{}\operatorname{range}(B) \subseteq R \land D \subseteq \operatorname{ker}(\operatorname{domRestrict}(C, R)) \land\\{}\exists! barA: \operatorname{LinearMap}(K, \operatorname{Quotient}(R, D), \operatorname{Quotient}(R, D)), \forall x: R, hAx: \operatorname{A}(x) \in R, \operatorname{barA}(\operatorname{mkQ}(D, x)) = \operatorname{mkQ}(D, \operatorname{subtype}(\operatorname{A}(x), hAx)) \land\\{}\exists! barB: \operatorname{LinearMap}(K, Input, \operatorname{Quotient}(R, D)), \forall u: Input, hBu: \operatorname{B}(u) \in R, \operatorname{barB}(u) = \operatorname{mkQ}(D, \operatorname{subtype}(\operatorname{B}(u), hBu)) \land\\{}\exists! barC: \operatorname{LinearMap}(K, \operatorname{Quotient}(R, D), Output), \forall x: R, \operatorname{barC}(\operatorname{mkQ}(D, x)) = \operatorname{C}(x).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReachableObservableQuotientDescent.reachable_observable_quotient_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reachable carrier is constructed as the span of all iterated input directions, while the hidden carrier is the intersection of all future output kernels.

Both invariance clauses and the input-range and output-kernel clauses are public. The three quotient maps are characterized by their computations on canonical quotient representatives.

## References

- Truth anchor: `D5/S3/Observer/Linear/ReachableObservableQuotientDescent.reachable_observable_quotient_descent`
