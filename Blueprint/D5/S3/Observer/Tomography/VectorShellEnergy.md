# Vector Shell Energy

## Abstract

A complete orthogonal Hilbert sum decomposes vector energy into initial, countable-shell, and residual weights.

**Theorem 1.1 (Complete orthogonal shells decompose vector energy).**

$$\forall H, G, V, hV, \psi,\ \operatorname{IsHilbertSum}(H, G, V, hV) \Rightarrow\\\Vert \psi \Vert^{2} = \Vert \operatorname{initialComponent}(V, hV, \psi) \Vert^{2} + \sum_{n=0}^{\infty} \Vert \operatorname{extractedComponent}(V, hV, n, \psi) \Vert^{2} + \Vert \operatorname{residualComponent}(V, hV, \psi) \Vert^{2} \land\\(\Vert \psi \Vert = 1 \Rightarrow 0 \leq \Vert \operatorname{initialComponent}(V, hV, \psi) \Vert^{2} \land (\forall n,\ 0 \leq \Vert \operatorname{extractedComponent}(V, hV, n, \psi) \Vert^{2}) \land\\0 \leq \Vert \operatorname{residualComponent}(V, hV, \psi) \Vert^{2} \land \Vert \operatorname{initialComponent}(V, hV, \psi) \Vert^{2} + \sum_{n=0}^{\infty} \Vert \operatorname{extractedComponent}(V, hV, n, \psi) \Vert^{2} + \Vert \operatorname{residualComponent}(V, hV, \psi) \Vert^{2} = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/VectorShellEnergy.vector_shell_energy_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a complete real inner-product space presented as an internal Hilbert sum with two distinguished coordinates and a countable family of extracted-shell coordinates. The distinguished coordinates represent the initial and residual subspaces.

For a vector psi, initialComponent, extractedComponent, and residualComponent embed its Hilbert-sum coordinates back into H. The extracted index n equals zero for the source shell numbered one, so the displayed sum is the exact reindexing of shells n at least one.

The squared norm equals the initial squared norm, the infinite sum of extracted squared norms, and the residual squared norm. The same named theorem retains the unit-vector clause: when the vector norm is one, these nonnegative weights have total mass one.

Pinned Mathlib supplies lp.norm_rpow_eq_tsum and the canonical isometric equivalence associated with IsHilbertSum; the proof applies them directly. Repository search found finite-stage and one-step shell identities, but no equal infinite energy-and-probability theorem.

## References

- Truth anchor: `D5/S3/Observer/Tomography/VectorShellEnergy.vector_shell_energy_decomposition`
