# Hankel Gramian Singular Values

## Abstract

The positive Hankel singular values are the square roots of the controllability-observability Gramian-product spectrum.

**Theorem 1.1 (Hankel and Gramian-product spectra agree).**

$$\begin{gathered}\forall K, V, Y: Type, S, O, n,\\{}\operatorname{RCLike}(K) \land \operatorname{NormedAddCommGroup}(V) \land \operatorname{InnerProductSpace}(K, V) \land \operatorname{FiniteDimensional}(K, V),\\{}\operatorname{NormedAddCommGroup}(Y) \land \operatorname{InnerProductSpace}(K, Y) \land \operatorname{FiniteDimensional}(K, Y) \land S \in \operatorname{LinearMap}(K, V, V) \land O \in \operatorname{LinearMap}(K, V, Y),\\{}\operatorname{adjoint}(S) = S \land \operatorname{Injective}(S) \land \operatorname{Injective}(O) \land n \in N \land \operatorname{finrank}(K, V) = n \Rightarrow\\{}\operatorname{let}(H, \operatorname{comp}(O, S)), \operatorname{let}(P, \operatorname{comp}(S, \operatorname{comp}(\operatorname{comp}(\operatorname{adjoint}(O), O), S))),\\{}\exists hP: \operatorname{IsSymmetric}(P), \forall i \in \operatorname{Fin}(n), 0 < \operatorname{singularValue}(H, i) \land \operatorname{singularValue}(H, i) = \operatorname{sqrt}(\operatorname{eigenvalue}(hP, n, i)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/HankelGramianSingularValues.hankel_gramian_singular_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Hankel map is constructed by composing the controllability root with future output. Self-adjointness identifies its adjoint-square with the displayed Gramian product; injectivity makes every indexed singular value positive.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/HankelGramianSingularValues.hankel_gramian_singular_values`
