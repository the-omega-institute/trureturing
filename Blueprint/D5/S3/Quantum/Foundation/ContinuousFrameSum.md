# Original common centers and continuous frame sums

## Abstract

Original EB and common centers force weakPair and interior; original W supplies compact pure points and continuous frame sums.

**Theorem 1.1 (Compactness of the full original effect interval).**

Lean statement: `D5/S3/Quantum/Foundation/ContinuousFrameSum.effects_compact`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ContinuousFrameSum.effects_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite dimensional real normed V, original pointed cone C and linear unit u, strict positivity of u on nonzero cone vectors and span(C)=top imply compactness of the entire original interval effects(C,u)={f : V toL R : proper(C,u,f)}. The original proof and telescope are unchanged. ExclusionIncidence.exclusion_upper_limit directly consumes this fact to obtain a subsequential limit of actual full-interval confirming effects. Neither Pair nor closedness of the pure carrier is needed.

The original carrier is any nonzero finite-dimensional real V, with closed generating cone C and the same strictly positive unit u. K is the whole normalized base, P is ALL its extreme points and [0,u] is the entire original proper-effect interval. No finite carrier, selected menu, assumed compact P, closed orthogonality, common intersection or positive-extension premise is used.

**Definition 1.2 (Original centers and frame carrier).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow \left(x \ne 0 \Rightarrow 0 < \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\forall hB \in \operatorname{exclusionBalls}\left(C, u\right),\; \forall p \in \operatorname{pure}\left(C, u\right),\; \operatorname{base}\left(C, u\right) = \operatorname{normalizedConeBase}\left(C, u\right) \land \left(\operatorname{pure}\left(C, u\right) = \operatorname{extremePoints}\left(\mathbb{R}, \operatorname{base}\left(C, u\right)\right) \land \left(\operatorname{center}\left(hB, p\right) = \operatorname{apply}\left(\operatorname{chosenExclusionChart}\left(hB, p\right), 0\right) \land \operatorname{sumVector}\left(hB, p\right) = \operatorname{add}\left(p, \operatorname{smul}\left(2, \operatorname{center}\left(hB, p\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/ContinuousFrameSum.sumVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

exclusionBalls supplies, at every original pure p, an injective affine parametrization of ALL D_p by a finite Euclidean closed unit ball of positive dimension. center is the image of zero in a chosen such chart. sumVector(p)=p+2 center(p) is the original U(p). commonCenter quantifies equality of these vectors over ALL original pure p,q. The frame-sum argument identifies this chart center with the midpoint of every original orthogonal diameter; no frame-fiber sum is assumed.

effects uses continuous linear maps to represent the original full proper interval. Every real linear map on finite-dimensional V has its native continuous-linear representation, so this does not restrict the original effects. frames initially permits three arbitrary original states with three full proper effects, delta readings, and their linear-map sum exactly u. Purity of the three states is derived where needed; it is not built into that raw compact frame carrier.

**Theorem 1.3 (Original W forces compactness of all pure points).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow \left(x \ne 0 \Rightarrow 0 < \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\forall hB \in \operatorname{exclusionBalls}\left(C, u\right),\; \operatorname{weakPair}\left(C, u\right) \Rightarrow \operatorname{IsCompact}\left(\operatorname{pure}\left(C, u\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ContinuousFrameSum.original_pure_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypotheses are original closedness, strict positivity, generation, EB_ge1 and weakPair. Pure-point compactness is a conclusion. A generating cone has nonempty interior by the existing affine-span criterion. Choose an interior point v and a ball radius, and evaluate any proper effect at v plus and minus a small unit vector. Nonnegativity at both points bounds its operator norm uniformly by u(v) divided by that small radius. The original proper-effect interval is closed, hence compact by the existing finite-dimensional closed-bounded criterion.

The full raw-frame constraints are closed in the compact product of three original bases and three entire effect intervals. Joint completion is supplied by OrthogonalJointCompletion.whole_joint_completion on the original all-P domain. It also gives injectivity of p to D_p: after completing p to p,r,s, equal exclusions put both owners into the singleton intersection D_r intersect D_s.

For a raw frame, consider the exposed one-value face of its first effect. Its other two states are different because another effect distinguishes them. For any two pure points in that one-value face, both other states lie in both exclusions. chart_face_eq makes those exclusions equal, and injectivity makes the two pure points equal. The existing compact-face Krein-Milman result then makes the entire one-value face a singleton, proving the first raw vertex pure. Conversely every original pure point is the first vertex of a raw frame by the original joint theorem. Thus P is precisely a continuous projection of the compact raw-frame set. The conclusion uses the derived purity of raw-frame vertices; compact projection and Krein-Milman are existing library results.

**Theorem 1.4 (Continuity, all original orthogonal edges, and full Pair).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow \left(x \ne 0 \Rightarrow 0 < \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\forall hB \in \operatorname{exclusionBalls}\left(C, u\right),\; \left(\operatorname{weakPair}\left(C, u\right) \Rightarrow \left(\operatorname{IsClosed}\left(\{s:\operatorname{pure}\left(C, u\right)\times\operatorname{pure}\left(C, u\right)\mid\operatorname{excludes}\left(C, u, \operatorname{fst}\left(s\right), \operatorname{snd}\left(s\right)\right)\}\right) \land \left(\operatorname{Continuous}\left(\operatorname{sumVector}\left(hB\right)\right) \land \left(\left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall q \in \operatorname{pure}\left(C, u\right),\; \operatorname{excludes}\left(C, u, p, q\right) \Rightarrow \operatorname{sumVector}\left(hB, p\right) = \operatorname{sumVector}\left(hB, q\right)\right) \land \left(\operatorname{commonCenter}\left(hB\right) \Leftrightarrow \left(\exists U \in V,\; \forall p \in \operatorname{pure}\left(C, u\right),\; \operatorname{sumVector}\left(hB, p\right) = U\right)\right)\right)\right)\right)\right) \land \left(\operatorname{pairProper}\left(C, u\right) \Rightarrow \operatorname{commonCenter}\left(hB\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ContinuousFrameSum.original_continuous_frame_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the original P squared the existential proper-effect witness relation is closed. This follows by projecting the closed one-zero evaluation constraints through the compact ENTIRE effect interval, using the existing closed-projection theorem. For two original orthogonal pure points q,r in an entire D_p, native sphere coordinates and the public affine_zero_antipode theorem force their coordinates to be antipodal. Affine midpoint preservation then gives q+r=2 center(p). Applied to an original joint triple, this proves p+q+r=U(p)=U(q), hence constancy on EVERY original orthogonal edge.

Restrict raw frames to those whose three vertices are original pure points. The derived compactness of P makes this restriction compact. Its first-vertex projection is continuous and surjective onto ALL P. Joint completion and its singleton intersection identify any frame's third point with the original joint third point, so U composed with this projection is exactly the continuous sum of the three vertices. Continuity descends through the existing compact closed-map quotient criterion and quotient continuity theorem. No generic continuity lemma is re-proved or counted as new mathematics, and neither carrier compactness nor fiber sums are additional hypotheses.

commonCenter is equivalent to a single vector value on ALL P; nonemptiness follows from pure_span and nontriviality. Full Pair gives weakPair because an original orthogonal pair is distinct. Under full Pair, the existing complete proper-face classifier gives H(p,q)=D_s for every distinct original pair. Original zero symmetry places s in both original exclusions, yielding two original orthogonal edges through s. Their equalities give U(p)=U(q). Thus the full-Pair implication uses an actually derived common pure point, rather than assuming a common intersection or a covering law.

**Theorem 1.5 (EB plus G suffices on the original domain).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow \left(x \ne 0 \Rightarrow 0 < \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\forall hB \in \operatorname{exclusionBalls}\left(C, u\right),\; \operatorname{commonCenter}\left(hB\right) \Rightarrow \left(\operatorname{weakPair}\left(C, u\right) \land \left(\exists U \in V,\; \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \operatorname{sumVector}\left(hB, p\right) = U\right) \land \left(\operatorname{smul}\left(\operatorname{div}\left(1, 3\right), U\right)\in \operatorname{intrinsicInterior}\left(\mathbb{R}, \operatorname{base}\left(C, u\right)\right) \land U\in \operatorname{interior}\left(C\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ContinuousFrameSum.common_center_interior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem assumes only the original cone data, EB_ge1 and commonCenter. weakPair is a CONCLUSION. Every U(p) equals one U, and w=U/3 is an original state because w=(p+2 center(p))/3. If w were outside the cone interior, the existing Hahn-Banach support theorem would supply a nonzero linear functional maximizing there. Cone scaling forces its maximum to be zero. Every original p and center(p) then has nonpositive value; the common-center equation forces the value of every p to be zero. Since ALL original pure points span V, the functional is zero, a contradiction. Hence w is in the cone interior; positive scaling gives U in the cone interior. Restricting an open cone neighborhood to the affine span of the normalized base gives w in its intrinsic, or relative, interior.

For an original p orthogonal to q, take q's antipode r in ALL D_p. Its purity follows from the original exclusion faciality and the sphere extreme-point image theorem. Choose an original common zero confirmer a_q from the EB face theorem. G gives a_q(U)=1, original zero symmetry gives a_q(p)=0, and the antipodal affine identity U=p+q+r gives a_q(r)=0. Thus r belongs to BOTH D_p and D_q. Zero symmetry puts p,q in D_r. The native cone-face lift of D_r now contains their whole original minimal face, which is therefore proper. This proves weakPair directly, without first invoking W.

Together these declarations cover the full original VII105.9 statement and its explicit U-interior conclusion. They do not assume pure compactness, original orthogonality closedness, frame completion, global common intersections or the separate positive-extension theorem VII105.4. No assertion of physical realization or reconstruction is made.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/ContinuousFrameSum.common_center_interior`
- Truth anchor: `D5/S3/Quantum/Foundation/ContinuousFrameSum.effects_compact`
- Truth anchor: `D5/S3/Quantum/Foundation/ContinuousFrameSum.original_continuous_frame_sum`
- Truth anchor: `D5/S3/Quantum/Foundation/ContinuousFrameSum.original_pure_compact`
- Truth anchor: `D5/S3/Quantum/Foundation/ContinuousFrameSum.sumVector`
- Dependency: [D5/S3/Quantum/Foundation/OrthogonalJointCompletion](OrthogonalJointCompletion.md)
