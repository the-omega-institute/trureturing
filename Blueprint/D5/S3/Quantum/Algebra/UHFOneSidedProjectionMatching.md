# Intrinsic localization and one-sided projection matching

## Abstract

Actual completed-algebra projections localize in finite matrix stages and admit one-sided matching.

FullMatrixModel C consists of natural stage sizes, injective unital complex star-algebra maps from the corresponding full matrix algebras into C, increasing ranges, and a norm-dense union of those ranges. Matrix norms are the L2 operator norms. Localization and matching are conclusions, not fields of the model.

The shared coordinate-projection lemma proj_single states that the diagonal matrix unit with coefficient one is a self-adjoint projection in every natural dimension. Both the finite-stage matching proof and the projection-span argument for the sequential Born-rule dichotomy use this same lemma. It has no state, channel, or Born-rule premise.

**Theorem 1.1 (Exact finite-stage localization).**

$$\forall C \in \operatorname{Type}\left(\right),\; [\operatorname{CStarAlgebra}\left(C\right)] \forall M \in \operatorname{FullMatrixModel}\left(C\right),\; \forall p \in C,\; (\operatorname{IsStarProjection}\left(p\right)) \Rightarrow (\exists n \in \operatorname{Nat}\left(\right),\; \exists u \in \operatorname{unitary}\left(C\right),\; \exists Q \in \operatorname{Matrix}\left(\operatorname{Fin}\left(\operatorname{size}\left(M, n\right)\right), \operatorname{Fin}\left(\operatorname{size}\left(M, n\right)\right), \operatorname{Complex}\left(\right)\right),\; (\operatorname{IsStarProjection}\left(Q\right)) \land (u \cdot p \cdot \operatorname{star}\left(u\right) = \operatorname{embed}\left(M, n, Q\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/UHFOneSidedProjectionMatching.localize_projection` (`✓ std3`). ∎

*Citation.* Bruce Blackadar (2006). *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*. DOI: [10.1007/3-540-28517-2](https://doi.org/10.1007/3-540-28517-2). URL: <https://bruceblackadar.com/Mathematics/Cycr.pdf>.

*Commentary.*

Symmetrize a dense finite-stage approximant. Its idempotence defect bounds each eigenvalue, so rounding at one half gives a finite-stage projection close in operator norm. The intrinsic polar decomposition of the near-projection intertwiner supplies a unitary in C. Zero projections are included.

**Theorem 1.2 (One-sided complete partition with one common initial projection).**

$$\forall C \in \operatorname{Type}\left(\right),\; [\operatorname{CStarAlgebra}\left(C\right)] \forall M \in \operatorname{FullMatrixModel}\left(C\right),\; \forall r \in C,\; \forall v \in C,\; (\operatorname{IsStarProjection}\left(r\right)) \Rightarrow ((\operatorname{IsStarProjection}\left(v\right)) \Rightarrow ((r \ne 0) \Rightarrow ((v \ne 0) \Rightarrow (\exists N \in \operatorname{Nat}\left(\right),\; \exists s \in \operatorname{Finset}\left(\operatorname{Fin}\left(\operatorname{size}\left(M, N\right)\right)\right),\; \exists l \in (\operatorname{Fin}\left(\operatorname{size}\left(M, N\right)\right))\to(C),\; \exists m \in C,\; \exists w \in (\operatorname{Fin}\left(\operatorname{size}\left(M, N\right)\right))\to(C),\; (\operatorname{Nonempty}\left(s\right)) \land ((\forall i \in \operatorname{Fin}\left(\operatorname{size}\left(M, N\right)\right),\; (i \in s) \Rightarrow ((\operatorname{IsStarProjection}\left(l\left(i\right)\right)) \land (l\left(i\right) \ne 0))) \land ((\forall i \in \operatorname{Fin}\left(\operatorname{size}\left(M, N\right)\right),\; (i \in s) \Rightarrow (\forall j \in \operatorname{Fin}\left(\operatorname{size}\left(M, N\right)\right),\; (j \in s) \Rightarrow ((i \ne j) \Rightarrow (l\left(i\right) \cdot l\left(j\right) = 0)))) \land ((\sum_{i\in s}(l\left(i\right)) = r) \land ((\operatorname{IsStarProjection}\left(m\right)) \land ((m \ne 0) \land ((m \cdot v = m) \land ((v \cdot m = m) \land (\forall i \in \operatorname{Fin}\left(\operatorname{size}\left(M, N\right)\right),\; (i \in s) \Rightarrow ((\operatorname{star}\left(w\left(i\right)\right) \cdot w\left(i\right) = m) \land (w\left(i\right) \cdot \operatorname{star}\left(w\left(i\right)\right) = l\left(i\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/UHFOneSidedProjectionMatching.one_sided_projection_matching` (`✓ std3`). ∎

*Citation.* Bruce Blackadar (2006). *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*. DOI: [10.1007/3-540-28517-2](https://doi.org/10.1007/3-540-28517-2). URL: <https://bruceblackadar.com/Mathematics/Cycr.pdf>.

*Commentary.*

Apply proved localization separately to both arbitrary projections. In a common later actual matrix stage, split the first projection into rank-one pieces and choose one rank-one subprojection of the second. Matrix units give the partial isometries. Transport all pieces and that one common initial projection back into C. The identities mv = vm = m express projection subordination in the intrinsic spectral order.

The finite family is indexed by the nonempty finite set s; values of l and w outside s carry no requirement. No growth, parity, whole-rank equality, whole-trace equality, or finite-stage membership of the original projections is assumed. Constant positive finite-matrix systems are included. An empty matrix stage cannot support the nonzero localized inputs. In a trivial algebra the nonzero-input hypotheses are impossible.

This is the intrinsic unital-algebra supplier used by the existing full-PB source. A Lean realization of the actual ambient corner C = PAP is a separate bridge. The supplier alone does not establish the scalar remainder classification, response equality, or the original full PB endpoints.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/UHFOneSidedProjectionMatching.localize_projection`
- Truth anchor: `D5/S3/Quantum/Algebra/UHFOneSidedProjectionMatching.one_sided_projection_matching`
- Dependency: [D5/S3/Quantum/Analysis/RussoDye](../Analysis/RussoDye.md)
