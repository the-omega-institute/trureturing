# Future Readout Quotient

## Abstract

The all-future kernel quotient is the coarsest linear future-readout quotient and carries unique induced dynamics.

**Theorem 1.1 (The future-readout quotient is coarsest and has unique dynamics).**

$$\begin{gathered}\forall K: \operatorname{Type}, V: \operatorname{Type}, Y: \operatorname{Type},\\{}T: \operatorname{LinearMap}(K, V, V), C: \operatorname{LinearMap}(K, V, Y),\\{}(\operatorname{RCLike}(K) \land \operatorname{NormedAddCommGroup}(V) \land \operatorname{InnerProductSpace}(K, V) \land \operatorname{FiniteDimensional}(K, V) \land\\{}\operatorname{NormedAddCommGroup}(Y) \land \operatorname{InnerProductSpace}(K, Y) \land \operatorname{FiniteDimensional}(K, Y)) \Rightarrow\\{}N_{\infty} := \operatorname{iInf}(k, \operatorname{ker}(C \circ T^{k}));\\{}(\exists Cbar: Nat \to \operatorname{LinearMap}(K, \operatorname{Quotient}(V, N_{\infty}), Y),\\{}\forall k: Nat, x: V, Cbar_{k}(\operatorname{mkQ}(N_{\infty})(x)) = C(T^{k}(x))) \land\\{}(\forall Q: \operatorname{Type},\\{}(\operatorname{AddCommGroup}(Q) \land \operatorname{Module}(K, Q)) \Rightarrow\\{}\forall q: \operatorname{LinearMap}(K, V, Q),\\{}(\forall x: V, y: V, q(x) = q(y) \Rightarrow\\{}\forall k: Nat, C(T^{k}(x)) = C(T^{k}(y))) \Rightarrow\\{}\exists! Phi: \operatorname{LinearMap}(K, \operatorname{range}(q), \operatorname{Quotient}(V, N_{\infty})), \operatorname{mkQ}(N_{\infty}) = Phi \circ \operatorname{rangeRestrict}(q)) \land\\{}(\exists! Tbar: \operatorname{LinearMap}(K, \operatorname{Quotient}(V, N_{\infty}), \operatorname{Quotient}(V, N_{\infty})),\\{}\forall x: V, Tbar(\operatorname{mkQ}(N_{\infty})(x)) = \operatorname{mkQ}(N_{\infty})(T(x))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Dynamics/FutureReadoutQuotient.future_readout_quotient_is_coarsest_with_unique_dynamics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V and Y be finite-dimensional inner-product spaces over a real or complex scalar field. A linear map T evolves V, and a linear map C supplies each readout.

The hidden subspace is constructed from the source semantics as the intersection of the kernels of C after every forward power of T. Every future readout therefore descends through its canonical linear quotient.

For any linear summary that determines all of those future readouts, the canonical quotient projection factors uniquely through the summary's effective range. This is the public universal property expressing that the quotient is coarsest.

Invariance of the all-future kernel under T makes T descend to the quotient. Surjectivity of the canonical quotient projection then forces that induced linear dynamics to be unique.

## References

- Truth anchor: `D5/S3/ObserverMemory/Dynamics/FutureReadoutQuotient.future_readout_quotient_is_coarsest_with_unique_dynamics`
- Dependency: [D5/S3/ObserverMemory/Dynamics/MaximalUnobservableSubspace](MaximalUnobservableSubspace.md)
