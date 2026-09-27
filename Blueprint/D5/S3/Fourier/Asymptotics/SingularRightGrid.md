# Singular Quadrature for Complex Sobolev Representatives

## Abstract

A singular right-grid sum approximates its integral uniformly with a square-root mesh error.

**Theorem 1.1 (A uniform estimate including both endpoints).**

$$\forall A \in \mathbb{R}, f \in \mathbb{R} \to \mathbb{C}, h \in \mathbb{R}, b \in \mathbb{R},\; \left(0 < A \land \left(\left(\operatorname{AbsolutelyContinuousOnInterval}\left(f, 0, A\right) \land \operatorname{IntervalIntegrable}\left(x \mapsto \left\lVert \operatorname{deriv}\left(f, x\right) \right\rVert^{2}, volume, 0, A\right)\right) \land \left(0 < h \land \left(h \le b \land b \le A\right)\right)\right)\right) \Rightarrow \left|\sum_{k \in \operatorname{range}\left(\left\lfloor\frac{b}{h}\right\rfloor\right)} \frac{\left\lVert f\left(\left((k: \mathbb{R}) + 1\right) \cdot h\right) \right\rVert^{2} - \left\lVert f\left(0\right) \right\rVert^{2}}{(k: \mathbb{R}) + 1} - \lim_{\varepsilon\to0+} \int_{\varepsilon}^{b} \frac{\left\lVert f\left(x\right) \right\rVert^{2} - \left\lVert f\left(0\right) \right\rVert^{2}}{x} dx\right| \le 14 \cdot \left(\frac{1}{\sqrt{A}} + \sqrt{A}\right) \cdot \sqrt{h} \cdot \int_{0}^{A} (\left\lVert f\left(x\right) \right\rVert^{2} + \left\lVert \operatorname{deriv}\left(f, x\right) \right\rVert^{2}) dx.$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/SingularRightGrid.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be positive and let f be a complex-valued absolutely continuous function on the closed interval from zero to A, with square-integrable actual derivative. Set g(v) equal to the squared norm of f(v) minus the squared norm of f(0). For every positive mesh h and endpoint b satisfying h <= b <= A, sum g(((k:ℝ)+1)h)/((k:ℝ)+1) over k in range(Nat.floor(b/h)) and compare it with the improper integral of g(v)/v, interpreted as the limit of the integral from epsilon to b as epsilon decreases to zero. The absolute error is bounded by 14 times (1/sqrt(A) + sqrt(A)), times sqrt(h), times the integral of the squared norm of f plus the squared norm of its derivative.

The constant depends only on A. In particular it works simultaneously for every b in any fixed interval [A0,A] whenever 0 < h <= A0. The proof includes the singular first cell and the final partial cell created by the floor. Absolute continuity, rather than continuous differentiability, is the regularity assumption.

For a real absolutely continuous function vanishing at zero, the proof first obtains the error bound 7 sqrt(h) times the L2 norm of its derivative. The remaining full cells are controlled by the integrable derivative of g(v)/v away from zero. The Sobolev energy controls the derivative of the squared norm. This is a deterministic quadrature estimate; harmonic counterterms and stochastic spectral convergence are separate conclusions.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/SingularRightGrid.result`
- Dependency: [D5/S3/Observer/HilbertGeometry/HilbertPathFundamentalTheorem](../../Observer/HilbertGeometry/HilbertPathFundamentalTheorem.md)
- Dependency: [D5/S3/Observer/HilbertGeometry/VectorPathDerivativeIntegrability](../../Observer/HilbertGeometry/VectorPathDerivativeIntegrability.md)
