# Trace saturation fixes the actual feedback

## Abstract

The finite-dimensional polar-feedback rigidity step in Section 9.

**Theorem 1.1 (A single common phase for every nonzero coordinate).**

$$\forall n \in \mathbb{N},\; \forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \mathbb{C}\right),\; \forall v \in \operatorname{Fin}\left(n + 1\right) \to \mathbb{C},\; \left(U \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(n + 1\right), \mathbb{C}\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(n + 1\right),\; v\left(i\right) \ne 0\right) \land \operatorname{norm}\left(\operatorname{trace}\left(U \cdot \operatorname{diagonal}\left(v\right)\right)\right) = \sum_{i:\operatorname{Fin}\left(n + 1\right)} {\operatorname{norm}\left(v\left(i\right)\right)}\right)\right) \Rightarrow \left(\exists z \in \mathbb{C},\; \operatorname{norm}\left(z\right) = 1 \land \left(\forall i \in \operatorname{Fin}\left(n + 1\right),\; \forall j \in \operatorname{Fin}\left(n + 1\right),\; U\left(i, j\right) = \operatorname{ite}\left(i = j, \frac{z \cdot \operatorname{star}\left(v\left(i\right)\right)}{\operatorname{norm}\left(v\left(i\right)\right)}, 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathFeedbackRigidity.trace_saturation_forces_polar_feedback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite core uses the trace-saturation implication from (9.22) through the first equality of (9.23); the Lean theorem is trace_saturation_forces_polar_feedback.

For each natural n, the system index is Fin(n+1). U is an actual complex unitary matrix and v has no zero coordinate. The trace saturation hypothesis uses the sum of all coordinate moduli. The conclusion gives one complex scalar z of norm one, common to every diagonal coordinate, and sets every off-diagonal coordinate to zero. star is complex conjugation, ite is the indicated conditional, and the real norm in the denominator is cast to the complex numbers.

Put L=sum(norm(v(i))) and S=trace(U diagonal(v)). Reuse Complex.exists_norm_eq_mul_self to choose a unit scalar alpha with norm(S)=alpha*S, and set z=star(alpha). Saturation gives star(z)*S=L. Every real part of star(z) U(i,i) v(i) is at most norm(v(i)), while their sum is L. Equality of these finite sums forces equality at every coordinate. The imaginary parts then vanish, giving star(z) U(i,i) v(i)=norm(v(i)). This both aligns the phases and forces norm(U(i,i))=1. Each unitary column has squared norm one, so all its remaining entries vanish. Multiplication by the conjugate of v(i) yields the stated polar correction.

The four-path specialization is n=3. Coverage is limited to the child atom's finite core from (9.22) through the first equality of (9.23): the feedback rigidity implication for a single vector under the stated full-support and trace-saturation hypotheses. This theorem does not establish the child's full premises or ray/context, derive the saturation premise from a channel optimum, identify either record ray, prove the second equality with the fixed U_sigma in (9.23), or establish the support equivalence, equal sign masses, unique optimizer channel, compactification or stability. Neither the complete child claim nor the complete parent theorem is covered. The existing FourPathQuadraticMajorant proves the analytic majorant and supplies neither these missing bridges nor the equality characterization.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FourPathFeedbackRigidity.trace_saturation_forces_polar_feedback`
