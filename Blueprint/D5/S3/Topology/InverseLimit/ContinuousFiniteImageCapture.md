# Intrinsic continuous-map Dirac capture

## Abstract

Original exhaustive birth tables and actual ordinary launch readback capture both whole Dirac sequences under continuity alone.

**Theorem 1.1 (One original launch and two whole-sequence labels).**

$$\forall inputs \in OriginalLaunchInputs,\; \operatorname{OntoTablesAndLiteralLaunchReadback}\left(inputs\right) \Rightarrow \left(\forall f \in \operatorname{ClosedDomainContinuousMap}\left(\operatorname{LiteralLimit}\left(inputs\right)\right),\; \left(\operatorname{InfiniteRange}\left(f\right) \land \operatorname{DisjointDomainRange}\left(f\right)\right) \Rightarrow \left(\exists capture \in OriginalWholeDiracCapture,\; \operatorname{OriginalLaunchAndIntrinsicDelayedPredicate}\left(inputs, f, capture\right) \land \operatorname{EveryTargetDiracWitnessIsProjectedImage}\left(inputs, f, capture\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/ContinuousFiniteImageCapture.exists_original_dirac_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tomasz Kania and Jerzy Kakol (2026). *Talagrand compacta, 2DCP, and pointwise quotients*. URL: <https://arxiv.org/abs/2607.06808v2>.

*Commentary.*

OriginalLaunchInputs means exactly H : SignedProperLimit.Prefix(omega-one); original onto tables U for support families, nu for BornData on V, and P for clopens on every stage at or above omega; the fixed Nat pair decoder; the prescribed lower bound; and literal original ordinary launch readback. That readback says that when the fixed CofinalTaskSchedule reservation at theta is (b,i), with b,i < theta and omega <= b, V(theta) is the pullback of U(b,i) along the actual restriction. No capture, delayed event or final conclusion is assumed. The limit is H.LimitSpace, the literal subspace of the original Boolean coordinate cube.

For any closed domain A, continuous f : A -> H.LimitSpace, infinite range and disjoint domain and range, the theorem produces b above the requested base, an ordinary reservation theta > b,i, a single source point list x, original labels s and t for the two entire Dirac sequences, and one code k in the original P enumeration. The coded clopens are disjoint. Every target projection belongs to both V(theta,n) and the second clopen, the original source measures vanish in variation outside the first clopen, and both nu equalities hold for every n. Any alternative target point list whose signed Diracs equal nu(theta,t,n) is exactly the projected f-image list.

SynchronizedClopenSupports supplies disjoint ambient clopens containing both markers under continuity alone. CountableClopenReflection reflects that whole family and the separator with its complement at one proper b. CofinalTaskSchedule supplies a later actual ordinary reservation; literal launch readback retains the same supports. SignedBirthEnumeration.pointBornData reuses the original regular Dirac construction for the supplied whole point lists; surjectivity chooses one label for each whole sequence. Original clopen surjectivity and the fixed decoder supply k. Mathlib's signed-measure conversion equality and Dirac injectivity force equality of every target witness. There is no termwise relabelling and no metric on the final uncountable cube.

Application: these are precisely the intrinsic original-birth data needed by the signed delayed branch. Once the actual raw history and its birth/arrival readback are supplied, the same executed event must supply its clopen and replacement J. The proper-stage continuous-preimage obstruction then excludes the event for a continuous infinite-image map to a disjoint complement. This theorem alone does not construct that history or establish the final finite-image, anti-homeomorphism or CH Talagrand endpoint.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/ContinuousFiniteImageCapture.exists_original_dirac_capture`
- Dependency: [D5/S3/Topology/InverseLimit/CofinalTaskSchedule](CofinalTaskSchedule.md)
- Dependency: [D5/S3/Topology/InverseLimit/CountableClopenReflection](CountableClopenReflection.md)
- Dependency: [D5/S3/Topology/InverseLimit/SignedBirthEnumeration](SignedBirthEnumeration.md)
- Dependency: [D5/S3/Topology/Separation/SynchronizedClopenSupports](../Separation/SynchronizedClopenSupports.md)
