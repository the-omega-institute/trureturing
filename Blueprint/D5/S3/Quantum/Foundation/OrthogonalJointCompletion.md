# Original orthogonal joint completion

## Abstract

Original weak orthogonal-pair properness supplies unique whole joint triples and mathematical capacity three.

V is the original nonzero finite dimensional real normed vector space. C is the original closed generating pointed cone; u is the original real linear unit strictly positive on C away from zero. K=base(C,u) is the entire normalized base and P=pure(C,u) is its entire extreme-point set. Proper effects are ALL linear maps with 0<=f<=u on ALL C. No finiteness or closedness of P, global pairProper, dimension-two condition, joint frame, reciprocal comparison, spectrality, Jordan representation or PSD cone is assumed.

**Definition 1.1 (The original restricted pair entrance).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{weakPair}\left(C, u\right) \Leftrightarrow \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall q \in \operatorname{pure}\left(C, u\right),\; \operatorname{excludes}\left(C, u, p, q\right) \Rightarrow \operatorname{pairBase}\left(C, u, p, q\right)\neq \operatorname{base}\left(C, u\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/OrthogonalJointCompletion.weakPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

weakPair requires pairBase(C,u,p,q) different from K only when excludes(C,u,p,q) holds. excludes means one original proper effect confirms p and reads zero at q. Complementation gives the opposite orientation. pairBase remains the whole smallest native cone-face slice, rather than the segment or a chosen chart.

**Definition 1.2 (The entire common confirmation family).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall p \in \operatorname{pure}\left(C, u\right),\; \forall a \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{common}\left(C, u, p, a\right) \Leftrightarrow \left(\operatorname{confirms}\left(C, u, p, a\right) \land \left(\forall x \in V,\; x\in \operatorname{exclusion}\left(C, u, p\right) \Rightarrow \operatorname{apply}\left(a, x\right) = 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/OrthogonalJointCompletion.common` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

common(C,u,p,a) means exactly a belongs to the original A_p: a is proper on the entire cone, a(p)=1 and a vanishes at every mixed state of the entire original D_p. No leastness or uniqueness is included.

**Definition 1.3 (All clauses of a joint third point).**

Lean statement: `D5/S3/Quantum/Foundation/OrthogonalJointCompletion.jointThird`

*Formalization.* `D5/S3/Quantum/Foundation/OrthogonalJointCompletion.jointThird` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

jointThird(C,u,p,q,r) asserts D_p intersect D_q={r}, H(p,q)=D_r, and the three original zero relations p perpendicular q, p perpendicular r and q perpendicular r. For EVERY specified a in A_p and b in A_q, it asserts c=u-a-b belongs to A_r, all nine delta readings a(p)=b(q)=c(r)=1 with the other six zero, and the identity a+b+c=u as linear maps on the whole original vector space. This is a conclusion predicate, never an entrance assumption.

**Definition 1.4 (Finite mathematical distinguishing measurements).**

Lean statement: `D5/S3/Quantum/Foundation/OrthogonalJointCompletion.measurement`

*Formalization.* `D5/S3/Quantum/Foundation/OrthogonalJointCompletion.measurement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

measurement(C,u,n) means there are p:Fin n to ALL P and f:Fin n to the original dual, with every f_i proper on ALL C, f_i(p_j)=if i=j then 1 else 0, and sum_i f_i=u. The delta equations force distinct pure points. It asserts a mathematical effect family and supplies no actual menu, device, wiring or physical implementation.

**Theorem 1.5 (Unique joint completion on the entire original domain).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow \left(x\neq 0 \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{exclusionBalls}\left(C, u\right) \Rightarrow \left(\operatorname{weakPair}\left(C, u\right) \Rightarrow \left(\left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall q \in \operatorname{pure}\left(C, u\right),\; \operatorname{excludes}\left(C, u, p, q\right) \Rightarrow \left(\exists r \in \operatorname{pure}\left(C, u\right),\; \operatorname{jointThird}\left(C, u, p, q, r\right) \land \left(\forall s \in \operatorname{pure}\left(C, u\right),\; \operatorname{jointThird}\left(C, u, p, q, s\right) \Rightarrow s = r\right)\right)\right) \land \left(\left(\forall p \in \operatorname{pure}\left(C, u\right),\; \exists q \in \operatorname{pure}\left(C, u\right),\; \exists r \in \operatorname{pure}\left(C, u\right),\; \operatorname{jointThird}\left(C, u, p, q, r\right)\right) \land \left(\left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall q \in \operatorname{pure}\left(C, u\right),\; \forall r \in \operatorname{pure}\left(C, u\right),\; \forall s \in \operatorname{pure}\left(C, u\right),\; \operatorname{excludes}\left(C, u, p, q\right) \Rightarrow \left(\operatorname{excludes}\left(C, u, p, r\right) \Rightarrow \left(\operatorname{excludes}\left(C, u, p, s\right) \Rightarrow \left(\operatorname{excludes}\left(C, u, q, r\right) \Rightarrow \left(\operatorname{excludes}\left(C, u, q, s\right) \Rightarrow \left(\neg \operatorname{excludes}\left(C, u, r, s\right)\right)\right)\right)\right)\right)\right) \land \left(\operatorname{measurement}\left(C, u, 3\right) \land \left(\forall n \in Nat,\; \operatorname{measurement}\left(C, u, n\right) \Rightarrow n \le 3\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OrthogonalJointCompletion.whole_joint_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under original EB_ge1 and weakPair, every original orthogonal p,q has exactly one r satisfying jointThird. Every original pure p belongs to such a triple. Six original pairwise zero relations among four points are impossible. A three-effect mathematical measurement exists, and every finite original mathematical distinguishing measurement has at most three outcomes. Thus the maximum jointly distinguishable original pure capacity is exactly three, without presupposing a finite set of ALL pure points.

Use ONLY the first two conjuncts of ExclusionBallFaces.exclusion_ball_faces: the common exposure and complete proper convex face classification already follow from EB alone. The whole minimal face of an original orthogonal pair is convex and extreme; weakPair makes that particular face proper. Its two different pure points exclude the singleton classification, so H(p,q)=D_r. Original zero symmetry puts r in both D_p and D_q. If their intersection contained two points, chart_face_eq would make that face the entire ball D_p. But q belongs to D_p and cannot belong to D_q, a contradiction. Therefore the whole intersection is exactly {r}. This is the new weak-entrance geometric bridge.

For arbitrary specified a in A_p and b in A_q, pull u-a back to the derived whole pair ball D_r. Reuse the original affine_zero_antipode equality theorem. Its endpoint value at q and original proper upper bound force its coefficient to be one; the original pure endpoint coordinates and the inner-product equality criterion identify q with the antipode of p. The same existing equality theorem fixes b's whole restriction, hence a+b=u on every mixed state of D_r. This ball calculation uses the actual whole pair derived above, never a global pair-ball assumption.

Set c=u-a-b. Original nonnegativity of a,b gives c<=u on ALL C; common zero readings give c(r)=1. The just-proved whole-ball equality gives c=0 on ALL D_r. Directly apply WholeExclusionSupport.whole_exclusion_support to obtain properness of c on the entire original cone, including positivity. Its normalization proof is neither copied nor re-counted. The nine readings and the linear-map unit sum follow. Compact nonpoint D_p has an extreme point of its own, which is original pure by faciality, giving every-pure completion. A fourth original orthogonal point lies in the same singleton intersection. For capacity attainment use pure_span, nontriviality and the common effects supplied by the paid classifier; for the upper bound a delta measurement with more than three outcomes supplies four forbidden original pairwise zero points.

This implements the complete original VII104.3 all-P target, distinct from the finite-ALL-P classical-triangle target VII104.9. No spectral decomposition of mixed states, global least effect, general nonzero reciprocal values, physical common menu or newer spectral framework is concluded. The mirrored Reg attempt reconstructs the original telescope and records an actual-positive law and conditional erased-relation failure; full four-slot registration is not asserted. Mathematical source and compiled evidence determine the theorem; no literature priority is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OrthogonalJointCompletion.common`
- Truth anchor: `D5/S3/Quantum/Foundation/OrthogonalJointCompletion.jointThird`
- Truth anchor: `D5/S3/Quantum/Foundation/OrthogonalJointCompletion.measurement`
- Truth anchor: `D5/S3/Quantum/Foundation/OrthogonalJointCompletion.weakPair`
- Truth anchor: `D5/S3/Quantum/Foundation/OrthogonalJointCompletion.whole_joint_completion`
- Dependency: [D5/S3/Quantum/Foundation/ExclusionBallFaces](ExclusionBallFaces.md)
- Dependency: [D5/S3/Quantum/Foundation/WholeExclusionSupport](WholeExclusionSupport.md)
