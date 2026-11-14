# Original binary-center geometry

## Abstract

Reciprocal repeated fibers, one original separating effect and repeated-block compatibility.

V is the same finite dimensional real normed carrier, C the closed pointed generating cone, and u the strictly positive original unit. K=base(C,u) is the entire normalized base, P=pure(C,u) all its extreme points. D(p)=exclusion(C,u,p) uses every original proper effect; no restricted effects or alternative state carrier is introduced. The full confirmer minimum corresponds to this exclusion through ExclusionWidthCompactness.comparison_attained and comparison_zero_iff. B is a proof of exclusionBalls on this same original domain. center(B,p) is ContinuousFrameSum.center, and equality of whole balls identifies these existing centers by AffineBallRigidity.center_eq_of_ball_eq. The results below permit all positive chart dimensions and hence apply to EB3.

binaryMixture(t,x,y) denotes t times x plus (1-t) times y. union is set union. sum(w) and weightedSum(w,a) are the sums over every index of the displayed Fin type; weightedCenterSum(B,w,a) replaces each a(i) by center(B,a(i)). Functions denotes the full function type. All endpoint functions take values in the original P. The finite compatibility result holds for arbitrary real normalized weights, in particular all nonnegative pure mixtures, repeated endpoints and zero coefficients. Empty index types are included; their normalization premise is false.

**Definition 1.1 (The entire original binary law).**

$$\forall V \in Types,\; [NormedAddCommGroup\left(V\right)] [NormedSpace\left(Real, V\right)] [FiniteDimensional\left(Real, V\right)] \forall C \in PointedCone\left(Real, V\right),\; \forall u \in LinearMaps\left(Real, V, Real\right),\; \forall B \in exclusionBalls\left(C, u\right),\; binaryCompatible\left(B\right) \Leftrightarrow \left(\forall p \in pure\left(C, u\right),\; \forall q \in pure\left(C, u\right),\; \forall r \in pure\left(C, u\right),\; \forall s \in pure\left(C, u\right),\; \forall t \in Real,\; \forall v \in Real,\; \left(\left(0 \le t \land t \le 1\right) \land \left(\left(0 \le v \land v \le 1\right) \land binaryMixture\left(t, p, q\right) = binaryMixture\left(v, r, s\right)\right)\right) \Rightarrow binaryMixture\left(t, center\left(B, p\right), center\left(B, q\right)\right) = binaryMixture\left(v, center\left(B, r\right), center\left(B, s\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/BinaryCenterGeometry.binaryCompatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two weights are independently quantified in the closed unit interval. The law compares two decompositions of the same actual original vector. No MC, global injectivity, pure closedness or common-center premise is included.

**Theorem 1.2 (Centers of equal whole original balls).**

Lean statement: `D5/S3/Quantum/Foundation/BinaryCenterGeometry.center_eq_of_exclusion_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterGeometry.center_eq_of_exclusion_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite dimensional real normed carrier V, original pointed cone C and linear unit u, a proof B of exclusionBalls, and any two original pure labels p and q, equality of their entire exclusions implies center(B,p)=center(B,q). No closedness, strict positivity, generating-span, BC or injectivity premise is required. The existing affine-ball center uniqueness theorem applies to the two complete chosen chart images, allowing different chart dimensions. This implication does not identify arbitrary balls from equality of their centers.

**Theorem 1.3 (Both original fibers and disjointness).**

$$\forall V \in Types,\; [NormedAddCommGroup\left(V\right)] [NormedSpace\left(Real, V\right)] [FiniteDimensional\left(Real, V\right)] \forall C \in PointedCone\left(Real, V\right),\; \forall u \in LinearMaps\left(Real, V, Real\right),\; \left(IsClosed\left(C\right) \land \left(\left(\forall x \in V,\; \left(x \in C \land x \ne 0\right) \Rightarrow 0 < u\left(x\right)\right) \land span\left(Real, C\right) = top\right)\right) \Rightarrow \left(exclusionBalls\left(C, u\right) \Rightarrow \left(\forall p \in pure\left(C, u\right),\; \forall s \in pure\left(C, u\right),\; \forall q \in pure\left(C, u\right),\; \left(p \ne s \land \left(exclusion\left(C, u, s\right) = exclusion\left(C, u, p\right) \land q \in exclusion\left(C, u, p\right)\right)\right) \Rightarrow \left(\left(\forall r \in pure\left(C, u\right),\; exclusion\left(C, u, r\right) = exclusion\left(C, u, q\right) \Leftrightarrow r \in exclusion\left(C, u, p\right)\right) \land \left(\left(\forall r \in pure\left(C, u\right),\; exclusion\left(C, u, r\right) = exclusion\left(C, u, p\right) \Leftrightarrow r \in exclusion\left(C, u, q\right)\right) \land Disjoint\left(exclusion\left(C, u, p\right), exclusion\left(C, u, q\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterGeometry.repeated_partner_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume p and s are distinct original pure labels with the same whole exclusion F, and q is any original pure point of F. For every original r in F, zero symmetry places p and s in D(r), so the two-point whole-ball rigidity gives D(r)=D(q). Conversely equality with D(q) and zero symmetry give r in F. Two distinct original pure points of F give the reciprocal identity I(F)=P intersect D(q). The original repeated_ball_isolated theorem gives disjointness; the equality alternative would put p in its own exclusion. These identities identify the two whole faces used by the common separating effect and the repeated-block relations.

**Theorem 1.4 (One original effect on the entire paired balls).**

$$\forall V \in Types,\; [NormedAddCommGroup\left(V\right)] [NormedSpace\left(Real, V\right)] [FiniteDimensional\left(Real, V\right)] \forall C \in PointedCone\left(Real, V\right),\; \forall u \in LinearMaps\left(Real, V, Real\right),\; \left(IsClosed\left(C\right) \land \left(\left(\forall x \in V,\; \left(x \in C \land x \ne 0\right) \Rightarrow 0 < u\left(x\right)\right) \land span\left(Real, C\right) = top\right)\right) \Rightarrow \left(exclusionBalls\left(C, u\right) \Rightarrow \left(\forall p \in pure\left(C, u\right),\; \forall s \in pure\left(C, u\right),\; \forall q \in pure\left(C, u\right),\; \left(p \ne s \land \left(exclusion\left(C, u, s\right) = exclusion\left(C, u, p\right) \land q \in exclusion\left(C, u, p\right)\right)\right) \Rightarrow \left(\exists e \in LinearMaps\left(Real, V, Real\right),\; proper\left(C, u, e\right) \land \left(\left\{x \mid x \in base\left(C, u\right) \land e\left(x\right) = 0\right\} = exclusion\left(C, u, p\right) \land \left\{x \mid x \in base\left(C, u\right) \land e\left(x\right) = 1\right\} = exclusion\left(C, u, q\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterGeometry.repeated_pair_separating_effect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose antipodal original pure points on the partner ball. Their original whole-face exposing confirmers vanish on F. On the partner ball the two restrictions are 1-alpha+alpha inner(n,z) and 1-beta-beta inner(n,z), with alpha and beta between zero and one half. If either coefficient is zero, that confirmer is already constant one on the partner. Otherwise beta times the first effect plus alpha times the second is constant k=alpha+beta-2 alpha beta>0 there and zero on F. positive_annihilator_maximum puts an actual global maximizer on the partner, so division by k yields a proper effect on the entire original cone. A fixed original pure point of each ball and the same effect or its complement prove both full face equalities. No full-Inj contact theorem is used.

**Theorem 1.5 (Every finite relation within the repeated block).**

$$\forall V \in Types,\; [NormedAddCommGroup\left(V\right)] [NormedSpace\left(Real, V\right)] [FiniteDimensional\left(Real, V\right)] \forall C \in PointedCone\left(Real, V\right),\; \forall u \in LinearMaps\left(Real, V, Real\right),\; \left(IsClosed\left(C\right) \land \left(\left(\forall x \in V,\; \left(x \in C \land x \ne 0\right) \Rightarrow 0 < u\left(x\right)\right) \land span\left(Real, C\right) = top\right)\right) \Rightarrow \left(\forall B \in exclusionBalls\left(C, u\right),\; \forall p \in pure\left(C, u\right),\; \forall s \in pure\left(C, u\right),\; \forall q \in pure\left(C, u\right),\; \left(p \ne s \land \left(exclusion\left(C, u, s\right) = exclusion\left(C, u, p\right) \land q \in exclusion\left(C, u, p\right)\right)\right) \Rightarrow \left(\forall n \in Nat,\; \forall m \in Nat,\; \forall a \in Functions\left(Fin\left(n\right), pure\left(C, u\right)\right),\; \forall b \in Functions\left(Fin\left(m\right), pure\left(C, u\right)\right),\; \forall w \in Functions\left(Fin\left(n\right), Real\right),\; \forall v \in Functions\left(Fin\left(m\right), Real\right),\; \left(\left(\forall i \in Fin\left(n\right),\; a\left(i\right) \in union\left(exclusion\left(C, u, p\right), exclusion\left(C, u, q\right)\right)\right) \land \left(\left(\forall j \in Fin\left(m\right),\; b\left(j\right) \in union\left(exclusion\left(C, u, p\right), exclusion\left(C, u, q\right)\right)\right) \land \left(sum\left(w\right) = 1 \land \left(sum\left(v\right) = 1 \land weightedSum\left(w, a\right) = weightedSum\left(v, b\right)\right)\right)\right)\right) \Rightarrow weightedCenterSum\left(B, w, a\right) = weightedCenterSum\left(B, v, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterGeometry.repeated_block_finite_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same original separating effect e defines J(x)=c(q)+e(x)(c(p)-c(q)). Both reciprocal fiber identities and whole-ball center uniqueness prove that J equals the original center replacement at every pure point of F union H. Linearity of e and the normalization of the finite sums show that each replaced sum equals J of the original sum. The identity uses the entire paired zero and one faces of the constructed original effect.

**Theorem 1.6 (One outside and three inside endpoints cannot cross).**

$$\forall V \in Types,\; [NormedAddCommGroup\left(V\right)] [NormedSpace\left(Real, V\right)] [FiniteDimensional\left(Real, V\right)] \forall C \in PointedCone\left(Real, V\right),\; \forall u \in LinearMaps\left(Real, V, Real\right),\; \left(IsClosed\left(C\right) \land \left(\left(\forall x \in V,\; \left(x \in C \land x \ne 0\right) \Rightarrow 0 < u\left(x\right)\right) \land span\left(Real, C\right) = top\right)\right) \Rightarrow \left(\forall B \in exclusionBalls\left(C, u\right),\; \forall p \in pure\left(C, u\right),\; \forall s \in pure\left(C, u\right),\; \forall q \in pure\left(C, u\right),\; \left(p \ne s \land \left(exclusion\left(C, u, s\right) = exclusion\left(C, u, p\right) \land q \in exclusion\left(C, u, p\right)\right)\right) \Rightarrow \left(\forall r \in pure\left(C, u\right),\; \forall a \in pure\left(C, u\right),\; \forall b \in pure\left(C, u\right),\; \forall d \in pure\left(C, u\right),\; \forall t \in Real,\; \forall v \in Real,\; \left(binaryCompatible\left(B\right) \land \left(Not\left(r \in union\left(exclusion\left(C, u, p\right), exclusion\left(C, u, q\right)\right)\right) \land \left(a \in union\left(exclusion\left(C, u, p\right), exclusion\left(C, u, q\right)\right) \land \left(b \in union\left(exclusion\left(C, u, p\right), exclusion\left(C, u, q\right)\right) \land \left(d \in union\left(exclusion\left(C, u, p\right), exclusion\left(C, u, q\right)\right) \land \left(\left(0 < t \land t < 1\right) \land \left(0 < v \land v < 1\right)\right)\right)\right)\right)\right)\right) \Rightarrow binaryMixture\left(t, r, a\right) \ne binaryMixture\left(v, b, d\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterGeometry.repeated_block_one_outside` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply BC and the same affine J to a proposed active crossing. Agreement on all three block endpoints and cancellation of the positive outside weight imply c(r)=J(r). The full zero and one faces of e give 0<e(r)<1 for an original pure r outside the block. Any strict mixture of the two ball centers belongs to no original exclusion: otherwise the facial property puts both centers in that exclusion, and the original interior-vanishing theorem puts both whole balls there. Whole-ball maximality identifies both balls, contradicting their disjointness. The actual center c(r) lies in its own exclusion, which gives the contradiction.

These are original repeated-block results and prerequisites for the XI138 local geometry. They do not construct the BC boundary-center affine graph on each whole ball or prove its rank dichotomy, exact interior section, reflected sphere dichotomy or fixed-sphere quantitative minimum. BC to MC, global injectivity, global noncollapse, equality of a reflected ball with its source, cross-ball vector gluing and two-outside crossings remain outside these conclusions. No quantum classification, literature priority or physical realization is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterGeometry.binaryCompatible`
- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterGeometry.center_eq_of_exclusion_eq`
- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterGeometry.repeated_block_finite_compatibility`
- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterGeometry.repeated_block_one_outside`
- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterGeometry.repeated_pair_separating_effect`
- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterGeometry.repeated_partner_fibers`
- Dependency: [D5/S3/Geometry/AffineBallRigidity](../../Geometry/AffineBallRigidity.md)
- Dependency: [D5/S3/Quantum/Foundation/ActualExclusionBoundary](ActualExclusionBoundary.md)
- Dependency: [D5/S3/Quantum/Foundation/UniqueConfirmationDensity](UniqueConfirmationDensity.md)
