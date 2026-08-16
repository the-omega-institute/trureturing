# Double Orthogonal Complement and Closure

## Abstract

Double orthogonal complementation equals topological closure in a Hilbert space.

**Theorem 1.1 (Double orthogonal complement equals closure).**

$$\forall k, E: \operatorname{Type},\ [\operatorname{RCLike}(k)],\ [\operatorname{NormedAddCommGroup}(E)],\ [\operatorname{InnerProductSpace}_{k}(E)],\ [\operatorname{CompleteSpace}(E)],\ M: \operatorname{Submodule}_{k}(E),\ \operatorname{orthogonal}\left(\operatorname{orthogonal}\left(M\right)\right) = \operatorname{topologicalClosure}\left(M\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/DoubleOrthogonalClosure.double_orthogonal_complement_eq_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be a real-or-complex scalar field, E a complete inner-product space over k, and M an arbitrary linear subspace. Taking the orthogonal complement twice produces exactly the topological closure of M.

This closes the primary boxed equality in qdo-v1 theorem/28.6. The closed-subspace and finite-dimensional special cases follow by identifying the topological closure with M; they are not claimed as separate declarations here.

Repository search found no equivalent D5 declaration. Loogle and direct search of the pinned Mathlib source found the exact theorem Submodule.orthogonal_orthogonal_eq_closure, which the Lean module imports and applies directly. The local smart-search name query did not find that declaration.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/DoubleOrthogonalClosure.double_orthogonal_complement_eq_closure`
