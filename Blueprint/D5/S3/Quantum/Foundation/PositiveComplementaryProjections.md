# Positive complementary projections on the original cone

## Abstract

Original weak geometry yields positive complementary primal and dual projections for every native cone face.

V is the original nonzero finite dimensional real normed space, C the original closed generating pointed cone, and u the original linear unit strictly positive on C away from zero. K=base(C,u) is the entire normalized base and P=pure(C,u) its entire extreme-point set. The hypotheses are all original exclusion balls of positive dimension and weakPair. Proper effects range over every linear functional between zero and u on all C. No finite pure carrier, spectral decomposition, positive projector or positive extension is an additional premise.

**Definition 1.1 (Literal positive image).**

$$\forall E \in Type,\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(\mathbb{R}, E\right)] \forall K \in \operatorname{PointedCone}\left(\mathbb{R}, E\right),\; \forall L \in \operatorname{LinearMap}\left(\mathbb{R}, E, E\right),\; \operatorname{positiveImage}\left(K, L\right) = \operatorname{inter}\left(\operatorname{range}\left(L\right), K\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/PositiveComplementaryProjections.positiveImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive image is the linear range intersected with the actual cone. It is not defined as the image of that cone.

**Definition 1.2 (Literal positive kernel).**

$$\forall E \in Type,\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(\mathbb{R}, E\right)] \forall K \in \operatorname{PointedCone}\left(\mathbb{R}, E\right),\; \forall L \in \operatorname{LinearMap}\left(\mathbb{R}, E, E\right),\; \operatorname{positiveKernel}\left(K, L\right) = \operatorname{inter}\left(\operatorname{ker}\left(L\right), K\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/PositiveComplementaryProjections.positiveKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive kernel is the linear kernel intersected with the actual cone, with the same definition on the original algebraic dual.

**Definition 1.3 (The actual positive dual).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{positiveDual}\left(C\right) = \operatorname{coneDual}\left(\operatorname{dualEval}\left(\mathbb{R}, V\right), C\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/PositiveComplementaryProjections.positiveDual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A member is an original algebraic linear functional nonnegative at every vector of C. The pairing is evaluation; no self-dual inner product identification is made.

**Definition 1.4 (Genuine finite dimensional dual transport).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall Sigma \in \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right), \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right)\right),\; \operatorname{primal}\left(Sigma\right) = \operatorname{comp}\left(\operatorname{inverse}\left(\operatorname{evalEquiv}\left(\mathbb{R}, V\right)\right), \operatorname{comp}\left(\operatorname{dualMap}\left(Sigma\right), \operatorname{evalEquiv}\left(\mathbb{R}, V\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/PositiveComplementaryProjections.primal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite dimensional algebraic biduality defines Pi on the original V. For every original f and v, f(Pi(v))=Sigma(f)(v); consequently Pi.dualMap=Sigma. This uses the evaluation equivalence, with no perfect-pair topology premise on the algebraic dual.

**Definition 1.5 (Positivity and idempotence).**

$$\forall E \in Type,\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(\mathbb{R}, E\right)] \forall K \in \operatorname{PointedCone}\left(\mathbb{R}, E\right),\; \forall L \in \operatorname{LinearMap}\left(\mathbb{R}, E, E\right),\; \operatorname{PositiveProjection}\left(K, L\right) \Leftrightarrow \left(\left(\forall x \in E,\; x\in K \Rightarrow \operatorname{apply}\left(L, x\right)\in K\right) \land \operatorname{comp}\left(L, L\right) = L\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/PositiveComplementaryProjections.PositiveProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positivity is tested on the entire cone. Idempotence is equality of linear maps.

**Definition 1.6 (All original pointwise projection laws).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall p \in \operatorname{pure}\left(C, u\right),\; \forall ap \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall Pi \in \operatorname{LinearMap}\left(\mathbb{R}, V, V\right),\; \forall Sigma \in \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right), \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right)\right),\; \operatorname{PointLaws}\left(C, u, p, ap, Pi, Sigma\right) \Leftrightarrow \left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\operatorname{dualMap}\left(Pi\right) = Sigma \land \operatorname{PositiveProjection}\left(C, Pi\right)\right) \land \operatorname{PositiveProjection}\left(C, \operatorname{smulRight}\left(ap, p\right)\right)\right) \land \operatorname{PositiveProjection}\left(\operatorname{positiveDual}\left(C\right), Sigma\right)\right) \land \operatorname{PositiveProjection}\left(\operatorname{positiveDual}\left(C\right), \operatorname{dualMap}\left(\operatorname{smulRight}\left(ap, p\right)\right)\right)\right) \land \operatorname{apply}\left(Sigma, u\right) = \operatorname{sub}\left(u, ap\right)\right) \land \operatorname{apply}\left(Sigma, ap\right) = 0\right) \land \operatorname{apply}\left(Pi, p\right) = 0\right) \land \left(\forall x \in V,\; x\in \operatorname{exclusion}\left(C, u, p\right) \Rightarrow \operatorname{apply}\left(Pi, x\right) = x\right)\right) \land \operatorname{positiveImage}\left(C, Pi\right) = \operatorname{coneHull}\left(\mathbb{R}, \operatorname{exclusion}\left(C, u, p\right)\right)\right) \land \operatorname{positiveKernel}\left(C, Pi\right) = \operatorname{coneHull}\left(\mathbb{R}, \operatorname{singleton}\left(p\right)\right)\right) \land \operatorname{positiveImage}\left(C, \operatorname{smulRight}\left(ap, p\right)\right) = \operatorname{coneHull}\left(\mathbb{R}, \operatorname{singleton}\left(p\right)\right)\right) \land \operatorname{positiveKernel}\left(C, \operatorname{smulRight}\left(ap, p\right)\right) = \operatorname{coneHull}\left(\mathbb{R}, \operatorname{exclusion}\left(C, u, p\right)\right)\right) \land \operatorname{positiveImage}\left(\operatorname{positiveDual}\left(C\right), Sigma\right) = \operatorname{zeroPositive}\left(C, u, p\right)\right) \land \operatorname{positiveKernel}\left(\operatorname{positiveDual}\left(C\right), \operatorname{dualMap}\left(\operatorname{smulRight}\left(ap, p\right)\right)\right) = \operatorname{zeroPositive}\left(C, u, p\right)\right) \land \operatorname{positiveKernel}\left(\operatorname{positiveDual}\left(C\right), Sigma\right) = \operatorname{coneHull}\left(\mathbb{R}, \operatorname{singleton}\left(ap\right)\right)\right) \land \operatorname{positiveImage}\left(\operatorname{positiveDual}\left(C\right), \operatorname{dualMap}\left(\operatorname{smulRight}\left(ap, p\right)\right)\right) = \operatorname{coneHull}\left(\mathbb{R}, \operatorname{singleton}\left(ap\right)\right)\right) \land \left(\forall f \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{apply}\left(\operatorname{dualMap}\left(\operatorname{smulRight}\left(ap, p\right)\right), f\right) = \operatorname{smul}\left(\operatorname{apply}\left(f, p\right), ap\right)\right)\right) \land \left(\forall x \in V,\; \operatorname{apply}\left(u, \operatorname{apply}\left(Pi, x\right)\right) = \operatorname{apply}\left(\operatorname{sub}\left(u, ap\right), x\right) \land \operatorname{apply}\left(u, \operatorname{apply}\left(\operatorname{smulRight}\left(ap, p\right), x\right)\right) = \operatorname{apply}\left(ap, x\right)\right)\right) \land \left(\forall x \in V,\; x\in C \Rightarrow \left(0 \le \operatorname{apply}\left(u, \operatorname{apply}\left(Pi, x\right)\right) \land \operatorname{apply}\left(u, \operatorname{apply}\left(Pi, x\right)\right) \le \operatorname{apply}\left(u, x\right)\right)\right)\right) \land \left(\forall x \in V,\; x\in C \Rightarrow \left(0 \le \operatorname{apply}\left(u, \operatorname{apply}\left(\operatorname{smulRight}\left(ap, p\right), x\right)\right) \land \operatorname{apply}\left(u, \operatorname{apply}\left(\operatorname{smulRight}\left(ap, p\right), x\right)\right) \le \operatorname{apply}\left(u, x\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/PositiveComplementaryProjections.PointLaws` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here R=ap.smulRight(p), so R(v)=ap(v)p, and Rstar is its genuine algebraic dual. The eight equalities use actual linear range and kernel intersections. Zp consists of all original positive functionals vanishing at p. cone(Dp) and the two nonnegative rays are native PointedCone hulls, denoted coneHull, including zero.

The mass identities quantify over ALL v in V. On C both masses lie in [0,u(v)], giving normalization nonincrease. Pi fixes every mixed state of the entire Dp and kills p; Sigma fixes every positive functional in Zp through the positive restriction inverse.

**Definition 1.7 (Mathematical complementary filters).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall T \in \operatorname{LinearMap}\left(\mathbb{R}, V, V\right),\; \forall R \in \operatorname{LinearMap}\left(\mathbb{R}, V, V\right),\; \operatorname{ComplementaryPair}\left(C, u, T, R\right) \Leftrightarrow \left(\left(\left(\left(\left(\left(\left(\left(\operatorname{PositiveProjection}\left(C, T\right) \land \operatorname{PositiveProjection}\left(C, R\right)\right) \land \operatorname{PositiveProjection}\left(\operatorname{positiveDual}\left(C\right), \operatorname{dualMap}\left(T\right)\right)\right) \land \operatorname{PositiveProjection}\left(\operatorname{positiveDual}\left(C\right), \operatorname{dualMap}\left(R\right)\right)\right) \land \operatorname{positiveImage}\left(C, T\right) = \operatorname{positiveKernel}\left(C, R\right)\right) \land \operatorname{positiveKernel}\left(C, T\right) = \operatorname{positiveImage}\left(C, R\right)\right) \land \operatorname{positiveImage}\left(\operatorname{positiveDual}\left(C\right), \operatorname{dualMap}\left(T\right)\right) = \operatorname{positiveKernel}\left(\operatorname{positiveDual}\left(C\right), \operatorname{dualMap}\left(R\right)\right)\right) \land \operatorname{positiveKernel}\left(\operatorname{positiveDual}\left(C\right), \operatorname{dualMap}\left(T\right)\right) = \operatorname{positiveImage}\left(\operatorname{positiveDual}\left(C\right), \operatorname{dualMap}\left(R\right)\right)\right) \land \left(\forall x \in V,\; x\in C \Rightarrow \left(\operatorname{apply}\left(u, \operatorname{apply}\left(T, x\right)\right) \le \operatorname{apply}\left(u, x\right) \land \operatorname{apply}\left(u, \operatorname{apply}\left(R, x\right)\right) \le \operatorname{apply}\left(u, x\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/PositiveComplementaryProjections.ComplementaryPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both maps and their genuine duals are positive idempotents. Their positive images and kernels agree in both complementary directions, and both original unit masses do not increase on C. Complementarity imposes no sum-to-identity equation.

**Theorem 1.8 (Full original VII105.5).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow \left(x\neq 0 \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{exclusionBalls}\left(C, u\right) \Rightarrow \left(\operatorname{weakPair}\left(C, u\right) \Rightarrow \left(\exists a \in \operatorname{Function}\left(\operatorname{pure}\left(C, u\right), \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right)\right),\; \left(\left(\left(\forall p \in \operatorname{pure}\left(C, u\right),\; \operatorname{common}\left(C, u, p, \operatorname{apply}\left(a, p\right)\right)\right) \land \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall f \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{common}\left(C, u, p, f\right) \Rightarrow f = \operatorname{apply}\left(a, p\right)\right)\right) \land \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall b \in \operatorname{ExclusionChart}\left(C, u, p\right),\; \exists Lambda \in \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{AffineMap}\left(\mathbb{R}, \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(\operatorname{dim}\left(b\right)\right)\right), \mathbb{R}\right), \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right)\right),\; \left(\left(\operatorname{ExtensionLaws}\left(b, \operatorname{apply}\left(a, p\right), Lambda\right) \land \operatorname{comp}\left(\operatorname{restriction}\left(b\right), Lambda\right) = \operatorname{id}\left(\right)\right) \land \operatorname{PointLaws}\left(C, u, p, \operatorname{apply}\left(a, p\right), \operatorname{primal}\left(\operatorname{comp}\left(Lambda, \operatorname{restriction}\left(b\right)\right)\right), \operatorname{comp}\left(Lambda, \operatorname{restriction}\left(b\right)\right)\right)\right) \land \left(\forall c \in \operatorname{ExclusionChart}\left(C, u, p\right),\; \forall Gamma \in \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{AffineMap}\left(\mathbb{R}, \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(\operatorname{dim}\left(c\right)\right)\right), \mathbb{R}\right), \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right)\right),\; \operatorname{PositiveLift}\left(c, Gamma\right) \Rightarrow \operatorname{comp}\left(Lambda, \operatorname{restriction}\left(b\right)\right) = \operatorname{comp}\left(Gamma, \operatorname{restriction}\left(c\right)\right)\right)\right)\right) \land \left(\forall F \in \operatorname{Face}\left(C\right),\; \exists T \in \operatorname{LinearMap}\left(\mathbb{R}, V, V\right),\; \exists R \in \operatorname{LinearMap}\left(\mathbb{R}, V, V\right),\; \operatorname{ComplementaryPair}\left(C, u, T, R\right) \land \operatorname{positiveImage}\left(C, T\right) = F\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveComplementaryProjections.whole_positive_projections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common family a and each signed linear extension Lambda are obtained from whole_positive_extension on the original W hypotheses. Restriction followed by Lambda gives Sigma; finite dimensional dual transport gives Pi. res composed with Lambda is the identity on the whole affine coordinate space. The extension laws give Sigma(u)=u-a_p and Sigma(a_p)=0. Every other positive lift in every other chart gives the same Sigma, hence the same genuine Pi.

Sigma is positive by restriction and positive extension. If Pi(v) were outside the original closed cone for positive v, separation would supply an original continuous linear functional nonnegative on C but negative at Pi(v). Its value equals Sigma(f)(v), a contradiction. This proves positivity on the original V rather than on a chosen coordinate model.

The zero cone of a_p is exactly cone(Dp), by normalizing every nonzero positive vector using the strictly positive original unit. The maximum face a_p=1 contains p. The complete original proper-face classification makes it a singleton or Dq. In the latter case, original zero symmetry and joint completion produce a point in Dp intersect Dq, where a_p would equal both zero and one. Thus p is its unique normalized maximum. These two exact faces give the four primal range and kernel equalities.

For the remaining dual kernel, a positive f annihilating the entire Dp must equal f(p)a_p on ALL V. An original joint triple p,q,r identifies the whole pair face of r,p with Dq. Restrict f and a_p to an actual whole Dq ball. Both are nonnegative and vanish at r; affine_zero_antipode gives the same diameter factor. Evaluation at the actual p fixes their coefficient ratio, so the two restrictions agree after multiplication by f(p). Both original functionals vanish at q and are positive. The actual Lambda_q.inverse_positive reconstructs both from those restrictions, proving the equality globally. This reconstruction also fixes every member of Zp and yields both dual positive range and kernel pairs.

Every F is a native PointedCone.Face C, not merely a selected or exposed face. A nonzero proper face is recovered from its entire unit slice by normalization and conical hull. The complete original proper-face classification makes that slice a pure singleton or an entire Dp, so the appropriate rank-one or Pi pair represents F. Zero and C use zero and identity in the two orders. All native faces are therefore positive images of mathematical complementary filter pairs.

This concludes mathematical projectivity on the original domain. It asserts no Pi+R=id, no unconditional preservation of pure rays, no physical event or instrument, no applicability of BMU Theorem 16, and no full static completion of later reconstruction results. The two-map and dual conditions are mathematical linear and cone statements.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/PositiveComplementaryProjections.ComplementaryPair`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveComplementaryProjections.PointLaws`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveComplementaryProjections.PositiveProjection`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveComplementaryProjections.positiveDual`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveComplementaryProjections.positiveImage`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveComplementaryProjections.positiveKernel`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveComplementaryProjections.primal`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveComplementaryProjections.whole_positive_projections`
- Dependency: [D5/S3/Quantum/Foundation/CommonPositiveExtension](CommonPositiveExtension.md)
