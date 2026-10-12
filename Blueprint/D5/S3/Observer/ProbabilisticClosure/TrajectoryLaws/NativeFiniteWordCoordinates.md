# Periodic and installed coordinate suppliers

## Abstract

Finite stopped-word coordinates

The original declaration namespace remains NativeBorelFiniteCompleteObstruction. This module owns the finite word-coordinate suppliers; the continuous descriptor and moment construction imports them. No observer register or acquired operation is added.

CurveParameter is the closed interval [239/1000,6/25]. The same x sets q=1944/390625, g(x)=q/x^3, u(x)=1-g(x)-x and v(x)=x/(g(x)+x). curveParameters has w=1/4 and uses these same u and v for all three native control labels. scalar_boxes proves the original u,v control boxes and g bounds; curve_algebra identifies the fixed rate with x. These consumed helpers are parameter adaptations of the existing periodic supplier.

**Theorem 1.1 (The periodic coordinate at the same parameter).**

$$\forall t: CurveParameter, \forall n: Nat, \forall b: Letter, \operatorname{periodicCoord}\left(\operatorname{curveParameters}\left(t\right), n, b, 2\right)=\operatorname{if}\left(b=0, \operatorname{curveU}\left(t\right), \operatorname{curveG}\left(t\right)\right) \cdot \operatorname{pow}\left(t, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFiniteWordCoordinates.curve_coord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

periodicCoord(T,n,b,2) denotes NativePeriodicWordLaw.coord(T,n,b,2). The real coercion of t is used in its power. NativePeriodicWordLaw.fixed_coord is applied directly, with curve_algebra identifying its rate. This supplied helper is consumed by curve_atoms in the continuous descriptor construction; it is not new mathematical content.

FiniteMeasurableCarrier means any Z with Fintype, MeasurableSpace and MeasurableSingletonClass. M and e retain the full original Observer and lawful InstalledEmitter hypotheses. Marked(Z) is Z times Option(Operation). cylinderVector(M,e,a)(w) is the real marked-law mass of the rawFrom prefix cylinder a, started at w. letterStep(M,e,b) sums the actual markedRow(M,e,w,v).toReal times f(v), retaining only incoming marks whose readSymbol is b.

**Theorem 1.2 (The exact finite stopped-word transfer).**

$$\forall Z: FiniteMeasurableCarrier, \forall M: ObserverZ, \forall e: InstalledEmitterM, \forall n: Nat, \operatorname{cylinderVector}\left(M, e, \operatorname{pWord}\left(n, 1\right)\right)=\operatorname{apply}\left(\operatorname{pow}\left(\operatorname{letterStep}\left(M, e, 1\right) \cdot \operatorname{letterStep}\left(M, e, 0\right), n\right), \operatorname{cylinderVector}\left(M, e, \operatorname{word}\left(1, 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFiniteWordCoordinates.cylinderVector_pWord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The marked regeneration law gives cylinder_cons. Taking real masses gives cylinderVector_cons. Induction on n, using the original p_word_succ identity, yields the displayed power of the two masked linear maps. This existing content proof is consumed by continuous_no_finite_complete in NativeBorelFiniteCompleteObstruction.

tail_coordinate identifies the actual pAtom(n,1) stopped-law singleton with this prefix cylinder at (z,none), using the exact stopped_word_fiber. initialReadout(rho) is the linear functional summing rho(z).toReal times f(z,none). The original finite COMPLETE exclusion consumes these suppliers with the same M, e and rho. Every starting PMF and every natural n remain quantified; no exponential rate or unrestricted positive-jc assertion is introduced.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFiniteWordCoordinates.curve_coord`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFiniteWordCoordinates.cylinderVector_pWord`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow](NativeBorelCommonFlow.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw](NativeInstalledFullLaw.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePeriodicWordLaw](NativePeriodicWordLaw.md)
