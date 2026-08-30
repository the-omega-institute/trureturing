# Cayley Moment Tridiagonal Flow

## Abstract

Cayley moments satisfy the tridiagonal positive-scale flow and its resolvent-budget specialization.

**Theorem 1.1 (Tridiagonal moment flow).**

$$\begin{gathered}\forall nu: \operatorname{Measure}\left(\mathbb{R}\right),\\{}a: \mathbb{R},\\{}(\operatorname{map}\left(xi: \mathbb{R} \mapsto - xi, nu\right) = nu) \land\\{}(\forall t: \mathbb{R}, 0 < t \Rightarrow \operatorname{Integrable}\left(xi: \mathbb{R} \mapsto \frac{1}{xi^{2} + t^{2}}, nu\right)) \land\\{}0 < a \Rightarrow\\{}\operatorname{let} m: \mathbb{N} \to \mathbb{R} \to \mathbb{R} := (n: \mathbb{N}, t: \mathbb{R}) \mapsto \operatorname{Re}\left(\operatorname{integral}\left(\operatorname{cayleySpectralMeasure}\left(nu, t\right), z: \mathbb{C} \mapsto z^{n}\right)\right),\\{}\operatorname{let} m_{-1}: \mathbb{R} \to \mathbb{R} := t: \mathbb{R} \mapsto \operatorname{Re}\left(\operatorname{integral}\left(\operatorname{cayleySpectralMeasure}\left(nu, t\right), z: \mathbb{C} \mapsto z^{{-1}}\right)\right),\\{}\operatorname{let} R: \mathbb{R} \to \mathbb{R} := t: \mathbb{R} \mapsto \operatorname{integral}\left(nu, xi: \mathbb{R} \mapsto \frac{1}{xi^{2} + t^{2}}\right),\\{}(\forall t: \mathbb{R}, 0 < t \Rightarrow m_{-1}(t) = m(1, t)) \land\\{}(\operatorname{HasDerivAt}\left(m(0), \frac{\frac{m(1, a) + m_{-1}(a)}{2} - m(0, a)}{a}, a\right)) \land\\{}(\forall n: \mathbb{N}, \operatorname{HasDerivAt}\left(m(n + 1), \frac{\frac{n + 2}{2} \cdot m(n + 2, a) + \frac{- n}{2} \cdot m(n, a) - m(n + 1, a)}{a}, a\right)) \land\\{}(\operatorname{HasDerivAt}\left(R, \frac{m(1, a) - R(a)}{a}, a\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/CayleyMomentTridiagonalFlow.tridiagonal_moment_flow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The moments are constructed from the canonical scale-dependent Cayley spectral measure. The inverse first moment is exposed separately so the zero-index convention is public.

Evenness identifies the inverse first moment with the first moment. A half-scale resolvent dominates differentiation under the source integral and yields every recurrence coefficient.

The last conjunct differentiates the resolvent budget itself and identifies its derivative with the first moment minus mass.

## References

- Truth anchor: `D5/S3/Weil/Budget/CayleyMomentTridiagonalFlow.tridiagonal_moment_flow`
- Dependency: [D5/S3/Weil/Budget/LinearCayleyScaleFlow](LinearCayleyScaleFlow.md)
