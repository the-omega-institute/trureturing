# Operator-convex affine rigidity and curvature

## Abstract

Every nonaffine operator-convex real function on the positive ray has full support of its actual right-derivative Stieltjes curvature.

All operator-convex predicates here are the existing domain-aware CFC predicates with domain Ioi 0. Their quantified inputs are actual selfadjoint operators with spectra in the positive ray. The matrix predicate uses complex two by two matrices with the existing Loewner order and actual real continuous functional calculus. OperatorConvexOnAll quantifies over all complex Hilbert spaces in Type 0. No continuous Jensen theorem, integral representation, strict convexity, curvature support, normalization or endpoint assumption is supplied as a premise.

**Theorem 1.1 (affine_of_matrixConvex).**

$$\forall f : \mathbb{R}\to\mathbb{R}, ((\operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right)) \Rightarrow ((\operatorname{OperatorConvexOn}\left(\operatorname{ComplexTwoByTwoMatrices}\left(\right), \operatorname{Ioi}\left(0\right), f\right)) \Rightarrow (\forall a : \mathbb{R}, (\forall b : \mathbb{R}, (\forall alpha : \mathbb{R}, (\forall gamma : \mathbb{R}, ((0 < a) \Rightarrow ((a < b) \Rightarrow ((\forall x : \mathbb{R}, ((\operatorname{mem}\left(x, \operatorname{Ioo}\left(a, b\right)\right)) \Rightarrow (\operatorname{f}\left(x\right) = alpha \cdot x + gamma))) \Rightarrow (\forall x : \mathbb{R}, ((\operatorname{mem}\left(x, \operatorname{Ioi}\left(0\right)\right)) \Rightarrow (\operatorname{f}\left(x\right) = alpha \cdot x + gamma))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/OperatorConvexCurvature.affine_of_matrixConvex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A local affine formula propagates to every positive real. Subtracting that line gives a scalar convex nonnegative function g vanishing on an interval. Choose q and beta>0 with q-beta,q,q+beta in that interval. For A=diag(q,w), B=[[q,beta],[beta,q]], and 0<t<1, the matrices A, B and D=(1-t)A+tB have actual positive spectra. Convexity bounds 0<=g(D)<=(1-t)g(A), whose first diagonal entry is zero. The positive-semidefinite zero-quadratic-form theorem kills the first column of g(D). CFC commutation with D and the nonzero offdiagonal t*beta then kill the second column, so g(D)=0. For a target z!=q, set d=z-(t*beta)^2/(z-q) and w=(d-t*q)/(1-t). Ordinary scalar continuity at t=0 selects 0<t<1 with w>0. The exact two by two determinant proves z is in the real spectrum of D=[[q,t*beta],[t*beta,d]]. Injectivity of actual CFC on that spectrum gives g(z)=0. The case z=q was already zero. Every private matrix helper is consumed by this propagation proof.

**Theorem 1.2 (convexOn_of_operatorConvexOnAll).**

$$\forall f : \mathbb{R}\to\mathbb{R}, ((\operatorname{OperatorConvexOnAll}\left(\operatorname{Ioi}\left(0\right), f\right)) \Rightarrow (\operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/OperatorConvexCurvature.convexOn_of_operatorConvexOnAll` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing all-Hilbert predicate is instantiated on the actual one-dimensional complex Euclidean Hilbert space. The star-algebra equivalence between one by one matrices and its bounded operators transports spectra, CFC and order. Applying the resulting inequality to scalar matrices gives scalar convexity. The same consumed transport is instantiated in dimension two for affine rigidity. This helper organizes existing CFC transport and the actual scalar inequality; it is consumed by the curvature theorem and is not claimed as new independent mathematical content.

**Theorem 1.3 (operatorConvex_curvature_full_support).**

$$\forall f : \mathbb{R}\to\mathbb{R}, (\forall hconv : \operatorname{OperatorConvexOnAll}\left(\operatorname{Ioi}\left(0\right), f\right), ((\neg \exists alpha gamma :\mathbb{R}, \forall x : \mathbb{R}, ((\operatorname{mem}\left(x, \operatorname{Ioi}\left(0\right)\right)) \Rightarrow (\operatorname{f}\left(x\right) = alpha \cdot x + gamma))) \Rightarrow (\operatorname{support}\left(\operatorname{curvature}\left(\operatorname{convexOnOfOperatorConvexOnAll}\left(hconv\right)\right)\right) = \operatorname{univPositive}\left(\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/OperatorConvexCurvature.operatorConvex_curvature_full_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonaffine means there do not exist real alpha and gamma with f(x)=alpha*x+gamma for every x>0. The scalar convexity proof in the curvature construction is derived from hconv, rather than assumed. The two-dimensional affine rigidity theorem supplies the complete premise of CurvatureAffineRigidity.full_support_of_affine_rigidity. A zero derivative increment would squeeze every secant slope on that interval to the same value and force a local affine formula, hence a global one. Nonaffineness therefore makes every right-derivative increment strictly positive. The actual curvature_Ioc identity gives positive mass on every positive half-open interval and hence on every neighborhood in Positive. The equality is support relative to Positive=(0,infinity), with no finiteness condition at zero or infinity.

The finite spectral and convexity ingredients are classical. This is a necessary supplier for the Hiai–Mosonyi–Tomamichel setting, arXiv:2607.08760v1, whose maximal hockey-stick versus maximal f-divergence equality classification is a separate question. No world novelty or solution of that classification is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/OperatorConvexCurvature.affine_of_matrixConvex`
- Truth anchor: `D5/S3/Quantum/Lieb/OperatorConvexCurvature.convexOn_of_operatorConvexOnAll`
- Truth anchor: `D5/S3/Quantum/Lieb/OperatorConvexCurvature.operatorConvex_curvature_full_support`
- Dependency: [D5/S3/Analytic/Convexity/CurvatureAffineRigidity](../../Analytic/Convexity/CurvatureAffineRigidity.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Lieb/LownerHeinzTheorem](LownerHeinzTheorem.md)
