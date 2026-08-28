# Update Kernel and Fixed Observables

## Abstract

Zero update difference is exactly invariance, and cyclic-window fixed observables are constants.

**Theorem 1.1 (Update difference kernel and fixed observables).**

$$\begin{gathered}\forall I: \operatorname{Type}, tau: \operatorname{Perm}\left(I\right), f: I \to \mathbb{C},\\L_{tau}(f) = 0 \Leftrightarrow f \circ tau = f; \\\ker L_{tau} = \operatorname {Inv}_{tau}; \\\forall M \in \mathbb{N}_{>0},\ \forall g: \operatorname {ZMod}(M)\to \mathbb{C},\ g \in \ker L_{+1} \iff \exists c\in \mathbb{C},\ g = (i\mapsto c).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WindowAlgebra/UpdateKernelCharacterization.update_difference_kernel_fixed_observables` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an update permutation tau on an observable index type, the update-difference map is constructed pointwise from the existing observer update defect. The fixed-observable submodule is constructed from the pointwise relation f(tau i) = f(i), rather than being defined from the target kernel.

The first clause applies the existing zero-defect/invariance equivalence. Extensionality then identifies the linear kernel with the independently constructed fixed-observable submodule. On a nonempty cyclic window, the existing cyclic invariance theorem identifies every kernel observable with a constant function.

Pinned Mathlib supplied only the generic LinearMap.ker membership rule; repository search found no packaged update-kernel/fixed-submodule theorem. The source clauses are stated together in the public theorem so no clause is hidden in a private helper.

## References

- Truth anchor: `D5/S3/Observer/WindowAlgebra/UpdateKernelCharacterization.update_difference_kernel_fixed_observables`
- Dependency: [D5/S3/Observer/ObserverMetric](../ObserverMetric.md)
