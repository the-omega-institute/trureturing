# Dimension-Independent Golden Anti-Isometry

## Abstract

The Fibonacci phase update negates the golden quadratic form in every real Hilbert dimension.

**Theorem 1.1 (The Hilbert-space Fibonacci update negates the form).**

$$\forall H: \operatorname{Type}\left(\right), [\operatorname{NormedAddCommGroup}\left(H\right)], [\operatorname{InnerProductSpace}\left(Real, H\right)], [\operatorname{CompleteSpace}\left(H\right)],\\{}let V = \operatorname{Product}\left(H, H\right); let Q(X, Y) = \operatorname{normSq}\left(X\right) - \operatorname{inner}\left(X, Y\right) - \operatorname{normSq}\left(Y\right); let F(X, Y) = \operatorname{pair}\left(X + Y, X\right);\\{}\forall X, Y: H, Q\left(F\left(\operatorname{pair}\left(X, Y\right)\right)\right) = -Q\left(\operatorname{pair}\left(X, Y\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HilbertGeometry/GoldenAntiIsometry.golden_anti_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a real Hilbert space and V=H x H. The quadratic form is Q(X,Y)=norm(X)^2-inner(X,Y)-norm(Y)^2, and the linear update is F(X,Y)=(X+Y,X).

The public conclusion is the single anti-isometry identity Q(F(X,Y))=-Q(X,Y).

## References

- Truth anchor: `D5/S3/Observer/HilbertGeometry/GoldenAntiIsometry.golden_anti_isometry`
