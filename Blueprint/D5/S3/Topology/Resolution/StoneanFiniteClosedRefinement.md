# Stonean finite closed refinements

## Abstract

Regular local shrinking and extremal disconnectedness make closed restrictions open and yield finite closed subordinate refinements.

The universes u and v are independent. T and B carry arbitrary topologies. Regularity is required on T and extremal disconnectedness on B. The map p is continuous, open and closed. All openness conclusions take values in the entire B. Compactness, Hausdorffness, surjectivity and nonemptiness are absent from the general suppliers.

**Theorem 1.1 (Openness on the closure of an open set).**

$$\begin{aligned}\forall u: UniverseLevel, \forall v: UniverseLevel, \forall T: Type_{u}, \forall B: Type_{v}, {}[\operatorname{TopologicalSpace}\left(T\right)] {}[\operatorname{TopologicalSpace}\left(B\right)] {}[\operatorname{RegularSpace}\left(T\right)] {}[\operatorname{ExtremallyDisconnected}\left(B\right)] \\\forall p: T \to B, \operatorname{Continuous}\left(p\right) \land \operatorname{IsOpenMap}\left(p\right) \land \operatorname{IsClosedMap}\left(p\right) \Rightarrow \\\forall W: \operatorname{Set}\left(T\right), \operatorname{IsOpen}\left(W\right) \Rightarrow \operatorname{IsOpenMap}\left(\operatorname{compose}\left(p, \operatorname{subtypeVal}\left(\operatorname{closure}\left(W\right)\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/StoneanFiniteClosedRefinement.isOpenMap_closure_domRestrict_of_regular_extremallyDisconnected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

subtypeVal(closure(W)) is the inclusion from the subtype closure W into T, with its induced topology, and compose(p,r) means p after r. For a relatively open V in closure W, IsInducing.subtypeVal.isOpen_iff gives an ambient open O with V equal to the inverse image of O. Its image is p(O intersect closure W). At any point t of this intersection, hasBasis_opens_closure supplies an open N containing t with closure N contained in O. Every open neighborhood R of t meets N intersect W, because R intersect N meets W. Thus t belongs to closure(N intersect W).

Continuity places p(t) in H = closure(p(N intersect W)). Openness of p and ExtremallyDisconnected.open_closure make H an open neighborhood in B. IsClosedMap.closure_image_eq_of_continuous identifies H with p(closure(N intersect W)), which is contained in p(O intersect closure W). These neighborhoods prove openness of every relatively open image. This local composition is repository-derived from the pinned Mathlib suppliers; it does not require a section or projectivity argument.

**Theorem 1.2 (Finite closed subordinate refinement).**

$$\begin{aligned}\forall u: UniverseLevel, \forall v: UniverseLevel, \forall T: Type_{u}, \forall B: Type_{v}, {}[\operatorname{TopologicalSpace}\left(T\right)] {}[\operatorname{TopologicalSpace}\left(B\right)] {}[\operatorname{RegularSpace}\left(T\right)] {}[\operatorname{ExtremallyDisconnected}\left(B\right)] {}[\operatorname{NormalSpace}\left(T\right)] \\\forall p: T \to B, \operatorname{Continuous}\left(p\right) \land \operatorname{IsOpenMap}\left(p\right) \land \operatorname{IsClosedMap}\left(p\right) \Rightarrow \\\forall n: Nat, \forall U: \operatorname{Fin}\left(n\right) \to \operatorname{Set}\left(T\right), \\{\forall i: \operatorname{Fin}\left(n\right), \operatorname{IsOpen}\left(\operatorname{U}\left(i\right)\right)} \land \operatorname{iUnion}\left(U\right) = univ \Rightarrow \operatorname{HasFiniteClosedRefinement}\left(p, U\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/StoneanFiniteClosedRefinement.hasFiniteClosedRefinement_of_regular_normal_extremallyDisconnected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normality is additionally required on T. The finite open cover is U : Fin n to Set T, with union all T; n may be zero. HasFiniteClosedRefinement is exactly the predicate in D5.S3.Topology.AlmostDisjoint.AdaptiveRefinementCounterexample. It asks for m : Nat, closed K : Fin m to Set T covering T and side : Fin m to Fin n, with K(j) contained in U(side(j)) and IsOpenMap for x in K(j) mapped to p(x.val). Empty pieces, repeated labels and restrictions that are not onto are permitted.

Every Fin n cover is point-finite. Mathlib's exists_iUnion_eq_closure_subset supplies open W(i) covering T and closure W(i) contained in U(i). Take m = n, K(i) = closure W(i), and side = id. Closedness and coverage follow from closure and the open shrinking cover. Each restriction is open by the preceding closure-domain theorem, used on the live proof path for every piece. For n = 0 the premise forces T empty and the same construction uses an empty index type; no point or nonempty piece is chosen.

For the compact Hausdorff Stonean application, B is compact Hausdorff and extremally disconnected, and T is compact Hausdorff in the same universe as B. Ref(B) means that every compact Hausdorff T in the same universe, every continuous open onto p : T to B, and every n and U : Fin n to Set T admit HasFiniteClosedRefinement p U whenever each U(j) is open and the pointwise cover condition holds: for every t there is j with t in U(j). This condition gives iUnion U = univ. Existing instances provide RegularSpace T and NormalSpace T; Continuous.isClosedMap supplies closedness from compact T and Hausdorff B. Apply the general finite-refinement theorem to p and U to obtain Ref(B). Onto and compactness of B belong to this application telescope but are unused by the stronger supplier.

The source-owned Local.familyRegistration and Finite.familyRegistration compile with complete topology/map telescopes, kernel-checked equivalence bridges, actual positive laws, complete-family variation, sensitivity and actual observational dependence. Their Contract registrations remain incomplete: the scoped report records declared_unresolved for both, with IE-C050 ClosedTruthReadout, reason=unclassified_form, rule=source.selection_missing, and no binding certificate. The packed Inputs/State families do not yet supply a legal raw sourceSelection or exact structural reconstruction of the original Pi telescope. Topology dictionaries and proof hypotheses cannot simply become independently variable source coordinates, and the V or refinement-witness scopes are inside the applied IsOpenMap and HasFiniteClosedRefinement predicates. The missing evidence is a lawful parameter/state/readout correspondence and complete raw Law reconstruction with rigid universes and binder modes. This gap is disclosed under https://github.com/the-omega-institute/trureturing/issues/16293; neither registration is declared_validated.

The pinned Mathlib shrinking and separation theorems are suppliers, and the local assembly is repository-derived. Library/Dynamics/gleason1958projective.md provides separate classical Stonean projectivity context; this composition is not attributed to Gleason. No worldwide novelty is claimed. Necessity of extremal disconnectedness, a classification of all nonmetrizable bases, and Peng's original dynamical question remain outside this result.

## References

- Truth anchor: `D5/S3/Topology/Resolution/StoneanFiniteClosedRefinement.hasFiniteClosedRefinement_of_regular_normal_extremallyDisconnected`
- Truth anchor: `D5/S3/Topology/Resolution/StoneanFiniteClosedRefinement.isOpenMap_closure_domRestrict_of_regular_extremallyDisconnected`
- Dependency: [D5/S3/Topology/AlmostDisjoint/AdaptiveRefinementCounterexample](../AlmostDisjoint/AdaptiveRefinementCounterexample.md)
