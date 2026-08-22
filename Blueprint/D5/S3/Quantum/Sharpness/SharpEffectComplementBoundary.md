# Sharp and Effect Complement Fixed Points

## Abstract

Projection complement is fixed-point-free, while effect complement fixes the half-identity.

**Theorem 1.1 (Projection complement is sharp-fixed-point-free but fixes a general effect).**

$$\forall H, 0 < \operatorname{dim}_{\mathbb{C}}(H) < \infty,\\{}(\forall P: \operatorname{End}\left(H\right), \operatorname{Projection}\left(P\right) \Rightarrow [\operatorname{Projection}\left(I - P\right) \land I - P \neq P]) \land\\{}[\operatorname{Pos}\left(\frac{1}{2}I\right) \land \operatorname{Pos}\left(I - \frac{1}{2}I\right) \land I - \frac{1}{2}I = \frac{1}{2}I] \land\\{}(\forall \tau: \operatorname{End}\left(H\right) \to \operatorname{End}\left(H\right), (\forall E, \operatorname{Pos}\left(E\right) \land \operatorname{Pos}\left(I - E\right) \Rightarrow \tau(E) \neq E) \Rightarrow \tau \neq (E \mapsto I - E)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Sharpness/SharpEffectComplementBoundary.sharp_effect_complement_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a nonzero finite-dimensional complex Hilbert space and let its continuous endomorphisms carry the adjoint operation. For every sharp projection P, I-P is again a sharp projection and differs from P.

Positivity is the library predicate requiring a symmetric, equivalently self-adjoint, operator with nonnegative quadratic form. Thus an effect E is stated directly by Pos(E) and Pos(I-E). Both conditions hold for I/2, and complement fixes I/2 exactly.

It follows that any codomain twist declared fixed-point-free on every effect must differ from ordinary complement. The proof uses Mathlib's projection-complement closure theorem directly; projection non-fixedness then follows from idempotence and nontriviality of H.

## References

- Truth anchor: `D5/S3/Quantum/Sharpness/SharpEffectComplementBoundary.sharp_effect_complement_boundary`
