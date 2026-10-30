# Generic historical collisions and signed capture

## Abstract

Fixed free historical ultrafilters, observable collisions and original whole signed-sequence capture.

## Generic historical filters and observables

The Historical namespace gives a reusable result for arbitrary histories J:I -> Set Nat, independent of the ordinal diagram and signed measures below. The pair constructor uses any nonempty I and pairwise downward directedness modulo finite differences, with two fixed disjoint reservoirs meeting every historical set infinitely. It fixes the free pair using the entire history before any continuous map or observable is selected. No CH, countability of I, last historical set or common infinite pseudointersection is required. The equality theorem applies to any topological X and actual continuous V:Ultrafilter Nat -> X, with a point-separating family of continuous observables into possibly different Hausdorff spaces. Only the observable targets are required to be Hausdorff; compactness or Hausdorffness of X is not an added premise. Each observable supplies its own historical convergence stage.

**Theorem 1.1 (Two free extensions of the entire history).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.exists_distinct_free_ultrafilters`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.exists_distinct_free_ultrafilters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tomasz Kania and Jerzy Kakol (2026). *Talagrand compacta, 2DCP, and pointwise quotients*. URL: <https://arxiv.org/abs/2607.06808v2>.

*Commentary.*

Let I be any nonempty type, J:I -> Set Nat, and suppose that for every i,j there is k for which J(k) minus J(i) and J(k) minus J(j) are finite. Let N0,N1 be disjoint, with J(i) intersect N0 and J(i) intersect N1 infinite for every i. Then there exist u0,u1:Ultrafilter Nat with both underlying filters below cofinite, N0 in u0, N1 in u1, every J(i) in both ultrafilters, and u0 distinct from u1. The filter order reverses inclusion of collections of sets; below cofinite therefore means free, or nonprincipal, on Nat.

For each reservoir N use F(i)=cofinite inf principal(J(i) intersect N). Removing a finite difference leaves this filter unchanged, so a common refinement modulo finite exceptions refines both filters. Infinitude makes each F(i) nonbottom, and directedness makes their infimum nonbottom. Ultrafilter.of extends this actual infimum. Nonemptiness of I recovers cofinite and N membership, while each index separately gives J(i) membership. Two extensions cannot agree because a proper filter cannot contain both disjoint reservoirs.

This is a repository composition of classical filter facts. The precise upstream sources are Mathlib.Order.Filter.Cofinite, especially Set.Finite.cofinite_inf_principal_sdiff and cofinite_inf_principal_neBot_iff, Filter.iInf_neBot_of_directed', and Mathlib.Order.Filter.Ultrafilter.Basic with Ultrafilter.of and Ultrafilter.of_le. The ultrafilter lemma is classical and choice is used; no effective enumeration of the pair is claimed. FreeUltrafilterCardinality supplies the nearby project example of the directed-filter extension method, but no cardinal-supply theorem is needed as a mathematical dependency.

**Theorem 1.2 (Observable-specific stages force equality of fixed images).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.eq_of_historical_observables`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.eq_of_historical_observables` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tomasz Kania and Jerzy Kakol (2026). *Talagrand compacta, 2DCP, and pointwise quotients*. URL: <https://arxiv.org/abs/2607.06808v2>.

*Commentary.*

Fix any u0,u1 below cofinite and containing every J(i). Let V:Ultrafilter Nat -> X be continuous. Let phi(a):X -> Y(a) be continuous, with every Y(a) Hausdorff, and let the whole family separate points of X. For every a assume there are i and L such that n |-> phi(a)(V(pure n)) tends to L along cofinite inf principal(J(i)). Then V(u0)=V(u1). The spaces Y(a) may depend on a; neither a common historical index nor Hausdorffness of X is an extra assumption.

Membership in J(i) and freeness put each chosen ultrafilter below the filter on which this one observable converges. Hence the same sequence converges to L along each ultrafilter. In the actual compact Hausdorff topology on Ultrafilter Nat, Mathlib's Ultrafilter.tendsto_pure_self says pure tends along u to u. Continuity of phi(a) composed with V therefore gives the second limit phi(a)(V(u)). Hausdorff uniqueness identifies these two limits. Equality for every a and point separation give equality in X. This uses actual continuous V, without any supplied ultrafilter-extension evaluation identity.

Choose the pair from the first theorem once, before choosing any observable. In the signed-ball application, X is the final weak-star target and phi(g) is evaluation at a continuous test function g. Each test may reflect to its own proper ordinal stage and converge on its own J(i). The same fixed distinct free pair then has equal V images. These free points are precisely the type required by a later signed-ball perturbation argument; a collision involving a principal point is not substituted.

The exact statements are repository-derived compositions of the classical ultrafilter lemma, continuity and uniqueness of Hausdorff limits. The Kania-Kakol Library reference records the original Talagrand question and is contextual attribution, not attribution of these exact generic statements. No mathematical novelty, completed CH recursion, final signed-ball contradiction, full solution or official acceptance is claimed. The actual history, its infinite reservoir intersections, continuity and separating tests must be supplied by their own constructions. All declarations are general structural mathematics, so utility is none: there is no bounded enumeration, numerical certificate or certified finite instance.

## Signed history application

In collision_of_original_birth, the generic index type I is Eligible(theta,d), J(c) is H.J(theta,d,c), and the reservoirs are H.N0(theta,d) and H.N1(theta,d). A proper successor of max(theta,d) supplies an eligible stage, and the maximum of two eligible stages supplies a common refinement using H.directed. The generic X is WeakDual R C(C.pt,R), its continuous map V is the extension f, and A is C(C.pt,R). This V is distinct from the support-family field H.V. For each test g, Y(g) is R and phi(g)(x)=x(g). WeakDual.eval_continuous supplies continuity; extensionality of the underlying continuous linear maps supplies point separation.

CountableContinuousReflection chooses an eligible stage c separately for each final test g, factoring it through a stage test a. The projected_lift theorem puts the actual projected sequence into H.properF, whose convergence for a has scalar limit signedFunctional(mu)(a). The signed pushforward integration identity and the application's premise f(pure n)=StrongDual.toWeakDual(signedFunctional(s(n))) identify this scalar sequence with phi(g)(f(pure n)). The generic theorem then obtains the values at the free ultrafilters from continuity and Ultrafilter.tendsto_pure_self. It assumes no evaluation identity at those free points.

The diagram has all proper ordinals below omega-one as indices, with arrows reversed. Its objects and the point of its actual limit cone are profinite spaces. BirthStage contains only the stages at or above omega. RawHistory stores the original onto support enumerations U, support families V and onto whole-sequence signed enumerations nu on those stages. No support enumeration is required at an earlier finite stage. The launch law identifies an original V(theta) with the literal pullback of an enumerated U(b,i) at a later proper theta.

Fix a regular signed sequence of variation mass one with disjoint nonempty clopen supports and positive Jordan mass at least one half. CountableSignedMeasureReflection.exists_common_stage supplies one proper b at or above omega that reflects those same supports and preserves the variation and Jordan whole masses. Surjectivity of U(b) selects one support-family index i. The launch law supplies theta greater than b. Cone naturality identifies the final b projection with the composite through theta. Two variation contractions force every theta pushforward to have mass exactly one. Preservation of signed whole mass and the sum and difference identities for the Jordan masses preserve the positive-half bound. Continuous pushforward of regular variation, together with exact mass preservation, gives regular variation downstairs. Variation contraction proves complement nullity on the actual launched supports.

The entire theta pushforward sequence is therefore one BornData value. The original total onto nu(theta) chooses a single d whose equality holds for every natural index. The label d may exceed theta. Eligible(theta,d) consists exactly of the proper c greater than max(theta,d). At every such c, literal projection composition and the same two-contraction argument prove a regular norm-one lift of that original birth, with the required inverse-image carrying. The proper-stage F law applies to these actual projected sequences.

The original disjoint reservoirs and the historical J sets determine two distinct free ultrafilters before any continuous test is selected. Finite directedness modulo finite sets suffices; no common infinite J or pseudointersection is used. Each final continuous real test factors exactly through its own eligible proper stage by CountableContinuousReflection.exists_stage. Pushforward integration transfers proper-stage convergence to that final test. The fixed ultrafilters then agree under every weak-dual evaluation of every continuous extension of the signed sequence.

The resulting implication is exactly SignedBallReduction.SignedClopenCollision for the actual cone point. Simultaneous signed-measure reflection is a proved supplier, with the same reflected supports. An arbitrary signed pushforward need not preserve its variation mass. RawHistory does not assume such an isometry or final-test convergence. The historical calculation is an application of the cited suppliers. It does not construct a CH history, establish AH, or settle Problem 8.2.

**Theorem 1.3 (Capture the entire original signed birth).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.exists_original_birth`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.exists_original_birth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every proper-stage profinite diagram F, cone C, and RawHistory H, take a regular signed sequence s on C.pt of variation mass one and positive Jordan mass at least one half. Fix a birth b and support family W at b, whose final pullbacks carry s, and assume the b pushforwards still have mass one. There are one original birth theta greater than b and one whole label d such that for every natural n the original H.nu(theta,d,n) is exactly s(n) pushed to theta, and the original H.V(theta,n) pullback carries s(n). The proof body is unchanged; the helper is public for the actual endpoint consumer.

**Theorem 1.4 (Every eligible projection is the original norm-one lift).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.projected_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.projected_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any such F, C and H, regular norm-one signed sequence s, original birth theta and label d, suppose every theta pushforward is H.nu(theta,d,n), with variation carried by the original theta support pullbacks. At every eligible proper c greater than max(theta,d), the c pushforwards have regular variation and mass exactly one, push along the literal bond back to those original birth measures at every n, and are variation-null off the pulled-back original theta supports. The proof body is unchanged.

**Theorem 1.5 (Historical F gives the signed collision criterion).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.signed_clopen_collision`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.signed_clopen_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every F with nonempty profinite objects, actual limit cone C, all diagram maps surjective, and RawHistory H, SignedClopenCollision holds on C.pt. Thus every admissible normalized regular signed sequence on disjoint nonempty clopen supports and every continuous ultrafilter extension of its signed functionals admit two distinct free ultrafilters with the same extension value. The ultrafilters are chosen before the final continuous scalar test, and each test factors through its own eligible proper stage. The publicization retains the unchanged proof and permits the actual CH endpoint theorem to consume it.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.eq_of_historical_observables`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.exists_distinct_free_ultrafilters`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.exists_original_birth`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.projected_lift`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.signed_clopen_collision`
- Dependency: [D5/S3/Topology/InverseLimit/CountableContinuousReflection](CountableContinuousReflection.md)
- Dependency: [D5/S3/Topology/InverseLimit/CountableSignedMeasureReflection](CountableSignedMeasureReflection.md)
- Dependency: [D5/S3/Topology/InverseLimit/SignedBirthEnumeration](SignedBirthEnumeration.md)
- Dependency: [D5/S3/Topology/Measures/SignedBallReduction](../Measures/SignedBallReduction.md)
- Dependency: [D5/S3/Topology/Measures/SignedSplitSuccessorOrdered](../Measures/SignedSplitSuccessorOrdered.md)
