# Inverse Blaschke History Deletion

## Abstract

The adjoint of an inner isometry is a coisometry that deletes exactly its finite model-space histories, with index equal to their dimension.

**Theorem 1.1 (Inverse inner factors delete the model-space history).**

$$T := V^{*},\quad K := (\operatorname{ran}\left(V\right))^{\perp},\quad P_{K} := I - V V^{*},\\{}\operatorname{Isometry}(V) \land \operatorname{dim}(K) = m \longrightarrow T T^{*} = I \land T^{*} T = I - P_{K},\\{}\operatorname{ran}(P_{K}) = \ker(T) = K \land \operatorname{Surjective}(T) \land \operatorname{Fredholm}(T) \land \operatorname{ind}(T) = m,\\{}H / \operatorname{ran}\left(V\right) \equiv K.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/InverseBlaschkeHistoryDeletion.inverse_blaschke_history_deletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be an isometry on a complete real or complex Hilbert space. Set T equal to its adjoint, let K be the orthogonal complement of the range of V, and suppose K has finite dimension m. Then T is a coisometry, its initial projection is the identity minus the orthogonal projection onto K, and its kernel is exactly K.

The defect I minus VV-star is proved to be a star projection whose range is K. Surjectivity follows from T composed with V being the identity. Consequently T is Fredholm with index m, while Mathlib's quotientEquivOrthogonal explicitly identifies the cokernel of V with the same model space K.

The source statement referred directly to finite Blaschke products, Hardy-space Toeplitz operators, and their model spaces, for which the repository has no construction. The formal theorem therefore states the exact operator data supplied by that analytic setting: isometry of V and finite model-space dimension. No Toeplitz or Blaschke result is assumed under an opaque name.

## References

- Truth anchor: `D5/S3/Zeros/ShiftOperators/InverseBlaschkeHistoryDeletion.inverse_blaschke_history_deletion`
