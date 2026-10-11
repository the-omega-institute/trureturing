# Native laws and endpoint flows

## Abstract

Actual native endpoints on full legal carriers

native(s,r) is the comap of the actual explicitStoppedWordLaw(s,r) along legal subtype inclusion. The actual stopped-word map always lands in the legal range; that range has mass one. Thus native is a probability law, rather than an unnormalized comap. endpoint(false)=1/3 and endpoint(true)=2/5. nativeEndpoint(s,b) bundles this actual law with the exact Regular predicate.

**Theorem 1.1 (native coordinate).**

$$\forall s: ActivePhase, \forall r: UnitInterval, \forall t: ValidTail, \operatorname{mass}\left(\operatorname{native}\left(s, r\right), t\right)=\operatorname{mass}\left(\operatorname{explicitStoppedWordLaw}\left(s, r\right), \operatorname{val}\left(t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws.native_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The atom t ranges over ValidTail(s), including infinity. Measurable subtype inclusion is injective and comap evaluates its singleton image exactly.

**Theorem 1.2 (native map).**

$$\forall s: ActivePhase, \forall r: UnitInterval, \operatorname{map}\left(\operatorname{native}\left(s, r\right), \operatorname{SubtypeVal}\left(\right)\right)=\operatorname{explicitStoppedWordLaw}\left(s, r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws.native_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transported law maps back to the actual stopped-word law. Invalid finite words have zero explicit mass, and legal words are reconstructed by the inclusion. This is an equality of complete measures.

**Theorem 1.3 (native atoms).**

$$\forall r: UnitInterval, (\forall n: Nat, \forall i: Letter, \operatorname{mass}\left(\operatorname{native}\left(\operatorname{p}\left(\right), r\right), \operatorname{pAtom}\left(n, i\right)\right)=\operatorname{markerCoefficient}\left(r, i\right) \cdot {\operatorname{alphaMass}\left(r\right) \cdot \operatorname{betaMass}\left(r\right)}^{n})\land((\operatorname{mass}\left(\operatorname{native}\left(\operatorname{beta}\left(\right), r\right), \operatorname{betaStop}\left(\right)\right)=\operatorname{betaMass}\left(r\right))\land((\forall n: Nat, \forall i: Letter, \operatorname{mass}\left(\operatorname{native}\left(\operatorname{beta}\left(\right), r\right), \operatorname{betaAtom}\left(n, i\right)\right)=\operatorname{alphaMass}\left(r\right) \cdot \operatorname{markerCoefficient}\left(r, i\right) \cdot {\operatorname{alphaMass}\left(r\right) \cdot \operatorname{betaMass}\left(r\right)}^{n})\land(\forall s: ActivePhase, \operatorname{mass}\left(\operatorname{native}\left(s, r\right), \operatorname{infinity}\left(s\right)\right)=0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws.native_atoms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

markerCoefficient(r,i) means alphaMass(r) when i=0 and betaMass(r)^2 otherwise. alphaMass(r)=r and betaMass(r)=1-r as ENNReal masses. The complete list is pAtom(n,0): r z^n; pAtom(n,1): (1-r)^2 z^n; betaStop: 1-r; betaAtom(n,0): r^2 z^n; betaAtom(n,1): r(1-r)^2 z^n; infinity in either phase: zero.

**Theorem 1.4 (native tails).**

$$\forall r: UnitInterval, \forall j: Nat, (\operatorname{mass}\left(\operatorname{native}\left(\operatorname{p}\left(\right), r\right), \operatorname{tailSet}\left(\operatorname{p}\left(\right), j\right)\right)={\operatorname{alphaMass}\left(r\right) \cdot \operatorname{betaMass}\left(r\right)}^{j})\land(\operatorname{mass}\left(\operatorname{native}\left(\operatorname{beta}\left(\right), r\right), \operatorname{tailSet}\left(\operatorname{beta}\left(\right), j\right)\right)=\operatorname{alphaMass}\left(r\right) \cdot {\operatorname{alphaMass}\left(r\right) \cdot \operatorname{betaMass}\left(r\right)}^{j})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws.native_tails` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Countable legal atom reconstruction, word injectivity and shifted geometric sums give every exact tail. The p normalization fixes the full series sum. At j=0 the suspended tail is r, not one.

**Theorem 1.5 (native endpoint boxes).**

$$\forall s: ActivePhase, \forall b: Bool, \operatorname{EndpointBox}\left(\operatorname{nativeEndpoint}\left(s, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws.native_endpoint_boxes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both native endpoints satisfy every exact regular tail bound and the complete atom boxes. At each atom the law is literally one comparison endpoint, so the proof uses min and max and imposes no global ordering of endpoint probabilities.

**Theorem 1.6 (native endpoint residuals).**

$$\forall b: Bool, (\operatorname{residualB}\left(\operatorname{nativeEndpoint}\left(\operatorname{p}\left(\right), b\right)\right)=\operatorname{law}\left(\operatorname{nativeEndpoint}\left(\operatorname{beta}\left(\right), b\right)\right))\land(\operatorname{residualA}\left(\operatorname{nativeEndpoint}\left(\operatorname{beta}\left(\right), b\right)\right)=\operatorname{law}\left(\operatorname{nativeEndpoint}\left(\operatorname{p}\left(\right), b\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws.native_endpoint_residuals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both identities are equalities of the full opposite probability measures. prependB takes betaStop to pAtom(0,1), betaAtom(n,i) to pAtom(n+1,i), and infinity to infinity. prependA takes pAtom(n,i) to betaAtom(n,i) and retains infinity. The complete native atom formulas prove both comap identities; the original nonzero denominators normalize them.

**Theorem 1.7 (endpoint flow inhabited).**

$$\forall theta: UnitInterval, \exists F: CommonFlow, \operatorname{mass}\left(\operatorname{nuP}\left(F\right), \operatorname{nativeEndpoint}\left(\operatorname{p}\left(\right), \operatorname{true}\left(\right)\right)\right)=\operatorname{alphaMass}\left(theta\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws.endpoint_flow_inhabited` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness endpointCommonFlow(theta) has marginals (1-theta) Dirac(native_a)+theta Dirac(native_b) and edge measures with the corresponding endpoint pairs in each orientation. Globally Borel deterministic kernels distinguish the upper native descriptor and choose the matching opposite endpoint. Both disintegrations, all four unweighted margins, both full normalized residuals and both complete boxes are proved. Neither mixture weight is divided out. This proves boundary inhabitance for every weight, including zero and one; it restricts none of the arbitrary Borel flows of the original theorem. A Dirac at a mixed descriptor is a different construction and is not used.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws.endpoint_flow_inhabited`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws.native_atoms`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws.native_coordinate`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws.native_endpoint_boxes`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws.native_endpoint_residuals`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws.native_map`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws.native_tails`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelRepresentation](NativeBorelRepresentation.md)
