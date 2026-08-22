# Finite Record Pinching Idempotence

## Abstract

A finite complete orthogonal projection family defines an idempotent unread-record map.

**Theorem 1.1 (Finite complete record pinching is idempotent).**

$$\forall n, K, \operatorname{Finite}\left(n\right), \operatorname{Finite}\left(K\right),\\P: K \to M_{n}(\mathbb{C}),\\(\forall k\in K, P_{k}^{*} = P_{k} \land P_{k}P_{k} = P_{k}) \land\\(\forall k, l\in K, k \neq l \Rightarrow P_{k}P_{l} = 0) \land\\\sum_{k\in K} P_{k} = I,\\E: M_{n}(\mathbb{C}) \to M_{n}(\mathbb{C}), E(\rho):=\sum_{k\in K} P_{k} \rho P_{k},\\E \circ E = E.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning/FiniteRecordPinchingIdempotence.finite_record_pinching_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be a finite family of complex matrix projections. Each P_k is self-adjoint and idempotent, distinct projections are pairwise orthogonal, and their sum is the identity.

The unread-record map sends rho to the sum of the diagonal compressions P_k rho P_k. Applying it twice introduces two projection indices; orthogonality removes every cross term and projection idempotence retains each diagonal term, so the two functions are equal.

The proof directly applies the frozen pointwise idempotence theorem and uses function extensionality only to expose the source claim as an equality of endomorphisms.

## References

- Truth anchor: `D5/S3/Observer/Conditioning/FiniteRecordPinchingIdempotence.finite_record_pinching_idempotent`
- Dependency: [D5/S3/Observer/Conditioning](../Conditioning.md)
