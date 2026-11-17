# No Continuous Global Section of the Circle Double Cover

## Abstract

The squaring double cover of the unit circle has no continuous global section.

**Theorem 1.1 (The circle squaring map has no continuous right inverse).**

$$\neg \exists s: Circle \to Circle, \operatorname{Continuous}(s) \land \forall z: Circle, \operatorname{s}\left(z\right)^{2} = z.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Topology/CircleDoubleCoverNoSection.no_continuous_global_section` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source map is the canonical squaring map on the exact unit-circle carrier: a section s would satisfy s(z)^2 = z at every point.

To rule out such a section, compose it with the angle exponential and divide by the half-angle exponential. The resulting continuous map takes values in the finite set {1,-1}, so connectedness of the real line forces it to be constant.

The values at 0 and 2*pi differ by a sign because Circle.exp(2*pi) = 1 while Circle.exp(pi) = -1. This contradicts the constant-sign conclusion, proving that no continuous global section exists.

Application: a continuous rank-one positive-semidefinite matrix field can fail to have a continuous real Gram factor with one row. Let S = {z : Complex | norm(z) = 1}, with the subspace topology, and write x = Re(z), y = Im(z). Define A(z) = (1/2)[[1+x,y],[y,1-x]], a real 2-by-2 matrix. The conclusion is that A is continuous, every A(z) is positive semidefinite of real rank exactly one, and there are no continuous p0,p1 : S -> Real satisfying all three equations p0(z)^2 = (1+x)/2, p0(z)p1(z) = y/2, and p1(z)^2 = (1-x)/2 at every z. These are precisely the entries of A(z) = [p0(z),p1(z)]^T [p0(z),p1(z)].

The carrier correspondence preserves the underlying complex number. Mathlib's Circle is the metric unit sphere, so its membership predicate is not definitionally the literal norm-one predicate. The map t : Circle -> S is t(c) = (c, Circle.norm_coe c); its inverse sends (z,h) to (z, mem_sphere_zero_iff_norm.mpr h). The composites are identities by subtype extensionality, and both maps are continuous by Continuous.subtype_mk applied to the continuous subtype inclusion. Thus the topology used in this application is explicitly the inherited topology on the literal carrier, transported by identity on complex values.

For the matrix clauses, Complex.continuous_re and Complex.continuous_im give entrywise continuity, and continuous_matrix assembles the matrix map. The norm-one hypothesis gives x^2+y^2 = 1 via Complex.normSq_eq_norm_sq. Finite entry normalization then gives A(z)^T = A(z), A(z)A(z) = A(z), and trace(A(z)) = 1. Over the reals, conjugate transpose equals transpose. Applying Matrix.posSemidef_conjTranspose_mul_self and rewriting by these identities proves positive semidefiniteness.

Exact rank follows from the existing projection-trace theorem, rather than from a rank upper bound. Matrix.toLin'_mul transfers idempotence to the endomorphism f = Matrix.toLin' (A(z)). The application of LinearMap.IsIdempotentElem.isProj_range makes f a projection onto its range. LinearMap.IsProj.trace and Matrix.trace_toLin'_eq identify trace(A(z)) with the real cast of finrank Real (range f). Matrix.rank is that finrank through the definitionally identical mulVecLin map. Since the trace is one and the natural-number cast into Real is injective, the real matrix rank is exactly one.

For the obstruction, assume such continuous p0 and p1 and set w(z) = p0(z) + i*p1(z). The first and third equations give p0(z)^2+p1(z)^2 = 1, hence norm(w(z)) = 1. All three equations give Re(w(z)^2) = p0(z)^2-p1(z)^2 = x and Im(w(z)^2) = 2*p0(z)p1(z) = y, so w(z)^2 = z. The continuous map s(c) = (w(t(c)), norm-one membership converted to sphere membership) therefore maps Circle to Circle. Subtype extensionality gives s(c)^2 = c. This is exactly the forbidden section in no_continuous_global_section; the topological obstruction is reused from that theorem.

The pointwise and continuous quantifiers differ. For each individual z, a square root is obtained from Circle.exp(arg(z)/2), using Circle.exp_arg and Circle.exp_natCast_mul. Its real and imaginary parts satisfy the three factor equations. This selection has no global continuity guarantee. Allowing two real rows also changes the problem: P(z) = A(z) is itself continuous and P(z)^T P(z) = A(z), by symmetry and idempotence. Thus the obstruction concerns a continuous one-row real factor, despite pointwise one-row existence; it does not rule out continuous factors in a larger ambient dimension.

This is a classical application of the circle double cover. Hatcher, Algebraic Topology, Chapter 1, printed p. 56, describes the circle cover z -> z^n; Proposition 1.33 on printed p. 61 gives the lifting criterion for a path-connected, locally path-connected source. Hatcher, Vector Bundles & K-Theory, version 2.2, printed p. 7, identifies the Mobius bundle with the canonical line bundle over RP^1, and printed p. 8 relates triviality to a full set of independent sections. These provide covering-space and bundle context; the matrix derivation above uses the existing Lean no-section theorem and projection-trace APIs. The application asserts no new literature result, physical realization, or dynamics law.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Topology/CircleDoubleCoverNoSection.no_continuous_global_section`
