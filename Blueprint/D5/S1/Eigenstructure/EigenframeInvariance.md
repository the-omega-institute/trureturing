# Eigenframe Invariance

## Abstract

A basis of eigenvectors has invariant coordinate lines.

**Theorem 1.1 (Every coordinate line of an eigenframe is invariant).**

$$\forall R, M, I,\ [\operatorname{CommRing}(R)],\ [\operatorname{AddCommGroup}(M)],\ [\operatorname{Module}(R,M)],\ \forall f\in\operatorname{End}_{R}(M),\ \forall b\in\operatorname{Basis}_{I}(R,M),\ \forall \Lambda:I\to R,\ (\forall i,\ \operatorname{HasEigenvector}(f,\Lambda(i),b(i))) \Rightarrow \forall i,\ \operatorname{map}_{f}(\operatorname{span}_{R}\{b(i)\})\subseteq\operatorname{span}_{R}\{b(i)\}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/EigenframeInvariance.eigenframe_coordinate_line_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be a linear endomorphism and b a basis indexed by i. When each b(i) is a nonzero eigenvector of f with eigenvalue lambda(i), the image under f of the scalar span of b(i) is contained in that same span for every index i.

Pinned Mathlib was searched before proving. No exact packaged eigenframe-invariance theorem was found. The proof is a thin wrapper over Module.End.HasEigenvector.apply_eq_smul, Submodule.map_le_iff_le_comap, and Submodule.span_singleton_le_iff_mem.

## References

- Truth anchor: `D5/S1/Eigenstructure/EigenframeInvariance.eigenframe_coordinate_line_invariant`
