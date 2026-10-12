# Actual square lifts and arbitrary futures at the same integer cut

## Abstract

Actual square lifts and arbitrary futures at the same integer cut.

Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in the corresponding definitions; proof arguments are determined by the displayed telescope, not new hypotheses.

**Definition 1.1 (Local squares keep their actual boundary edges).**

$$\forall V \in Type, E \in Type, D \in Type, R \in Type, A \in \operatorname{DirectedMultigraph}\left(V, E\right), Bgraph \in \operatorname{DirectedMultigraph}\left(V, D\right),\; \operatorname{recordType}\left(\operatorname{Squares}\left(A, Bgraph, R\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge.Squares` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A : DirectedMultigraph V E and B : DirectedMultigraph V D share their vertex type; R is an arbitrary actual boundary-edge type. recordType displays the Lean structure. Squares stores source, target, sq, endpoint equations, totalized back and forth operations with composable-input specifications and the two local uniqueness laws, plus actual incoming and outgoing R choices at every vertex. It supplies no global lift or whole-ray claim.

FiniteForgetting S q is a Prop with positive : 0<q. Its left field quantifies ALL natural-indexed x:E, y,y':D and r,r':R square strips of length q with identical left inputs and concludes r 0=r' 0. Its right field quantifies all x,x':E, y:D and r,r':R strips with identical right inputs and concludes r q=r' q. Opposite rows and other boundaries are unrestricted. No extra endpoint equality is assumed. q-run overlap constructs compatible leftBoundary and rightBoundary at EVERY integer time. FullSquare.boundary k is immediately after edge k, so square k relates boundary(k-1), left k, right k and boundary k.

**Theorem 1.2 (Every full legal right future has the prescribed left-past preimage).**

$$\forall V \in Type, E \in Type, D \in Type, R \in Type, A \in \operatorname{DirectedMultigraph}\left(V, E\right), Bgraph \in \operatorname{DirectedMultigraph}\left(V, D\right), S \in \operatorname{Squares}\left(A, Bgraph, R\right), q \in Nat, K \in \operatorname{FiniteForgetting}\left(S, q\right),\; \forall x \in \operatorname{History}\left(A\right), n \in Int, r \in \operatorname{Out}\left(S, x, n\right), y \in \operatorname{History}\left(Bgraph\right), hy \in y \in \operatorname{betaRay}\left(S, x, n, r\right),\; \exists z \in \operatorname{History}\left(A\right),\; z \in \operatorname{leftRay}\left(S, x, n\right) \land \left(\operatorname{H}\left(S, K\right)\left(z\right) = y \land \operatorname{liftBoundary}\left(S, K, z, n\right) = \operatorname{value}\left(r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge.whole_ray_preimage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

leftRay(S,x,n) is S.ray x n={z | forall k:Int, k<=n implies z k=x k}. Out(S,x,n) is {r:R // S.source r=A.target(x n)}; value(r)=r.val. betaRay(S,x,n,r) fixes the right past produced by S.backEdge x n r.val (n-k).toNat for EVERY k<=n. liftBoundary(S,K,z,n) is (S.leftLift K z).boundary n. H(S,K) is (S.leftLift K x).right, constructed rather than postulated.

The splice uses the prescribed alpha past backward from the exact boundary r at n, then forthRun consumes the supplied y edge at every time strictly after n. Local square seam laws make both histories legal. Derived full-left uniqueness identifies this full lift with leftLift, proving H z=y AND the exact original boundary r at n. The y binder ranges over all full legal histories in the right ray, not selected representative futures.

**Theorem 1.3 (The entire image is a union of full represented rays at the same cut).**

$$\forall V \in Type, E \in Type, D \in Type, R \in Type, A \in \operatorname{DirectedMultigraph}\left(V, E\right), Bgraph \in \operatorname{DirectedMultigraph}\left(V, D\right), S \in \operatorname{Squares}\left(A, Bgraph, R\right), q \in Nat, K \in \operatorname{FiniteForgetting}\left(S, q\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteD \in \operatorname{Fintype}\left(D\right), decV \in \operatorname{DecidableEq}\left(V\right), hB \in \operatorname{Essential}\left(Bgraph\right),\; \forall x \in \operatorname{History}\left(A\right), n \in Int,\; \operatorname{image}\left(\operatorname{H}\left(S, K\right), \operatorname{leftRay}\left(S, x, n\right)\right) = \operatorname{betaFullRayUnion}\left(S, hB, x, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge.same_cut_full_rays` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

betaFullRayUnion is the union over r:Out S x n of {y:History B | forall k:Int, k<=n implies y k=(S.betaFull hB x n r) k}. The finite V,D and DecidableEq V instances together with Essential B are precisely the represented-ray hypotheses. betaFull extends the prescribed right past by an actual legal outgoing tail to give one full representative. betaRay_is_whole_ray shows its choice of tail restricts NO future member.

same_cut_whole_ray_image uses the arbitrary-future reverse inclusion. component_disjoint uses right q-step forgetting on the COMMON LAST q right edges to show distinct R indices give disjoint sets; this is not an appeal to global lift uniqueness. betaFull_endpoint is S.target r.val. Thus negative cuts, every original boundary index, and endpoint multiplicity remain in scope. There is no finiteness assumption on R here; a later finite numbered specialization provides it.

**Definition 1.4 (Finite forgetting constructs both inverse continuous maps).**

$$\forall V \in Type, E \in Type, D \in Type, R \in Type, A \in \operatorname{DirectedMultigraph}\left(V, E\right), Bgraph \in \operatorname{DirectedMultigraph}\left(V, D\right), S \in \operatorname{Squares}\left(A, Bgraph, R\right), q \in Nat, K \in \operatorname{FiniteForgetting}\left(S, q\right), topE \in \operatorname{TopologicalSpace}\left(E\right), discreteE \in \operatorname{DiscreteTopology}\left(E\right), topD \in \operatorname{TopologicalSpace}\left(D\right), discreteD \in \operatorname{DiscreteTopology}\left(D\right), topR \in \operatorname{TopologicalSpace}\left(R\right), discreteR \in \operatorname{DiscreteTopology}\left(R\right),\; \operatorname{Homeomorph}\left(\operatorname{History}\left(A\right), \operatorname{History}\left(Bgraph\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge.historyHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula displays the definition's result type with its complete local-square/FiniteForgetting telescope and TopologicalSpace plus DiscreteTopology instances on E,D,R. No finiteness or Essential graph assumption is needed for this construction. leftLift and rightLift are built by q-step recursion and overlap. full_left_unique and full_right_unique derive uniqueness from the two forgetting fields and prove the two inverse identities of historyEquiv.

The discrete finite-run functions are continuous; coordinatewise continuity in the native product/subtype topology proves H_continuous and Hinv_continuous. FullSquare.shift and lift uniqueness give H_shift for the original unit shifts. These facts concern the constructed H, not an assumed map with prescribed action support.

**Definition 1.5 (Bind the local squares to the literal numbered boundary graph).**

$$\forall Hgroup \in Type, groupH \in \operatorname{Group}\left(Hgroup\right), finiteH \in \operatorname{Fintype}\left(Hgroup\right), decH \in \operatorname{DecidableEq}\left(Hgroup\right), a \in Nat, M \in \operatorname{GroupMat}\left(Hgroup, a, a\right), N \in \operatorname{GroupMat}\left(Hgroup, a, a\right), C \in \operatorname{GroupMat}\left(Hgroup, a, a\right),\; \operatorname{recordType}\left(\operatorname{NumberedData}\left(M, N, C\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge.NumberedData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Hgroup is any Group with Fintype and DecidableEq instances; a:Nat is arbitrary, and M,N,C : GroupMat Hgroup a a. recordType displays NumberedData's structure type. NumberedData contains squares : Squares (expandedGraph M) (expandedGraph N) with R=Edge C times Hgroup, and source_exact and target_exact equal its boundary endpoints to the original expandedGraph C endpoints.

ActualOut T alpha n is {r:Edge C times Hgroup // expandedGraph C.source r=expandedGraph M.target(alpha n)}. It retains the full numbered C edge and its absolute group anchor. outEquiv converts only this endpoint proof to squares.Out, without forgetting labels, numbers or group coordinates.

**Theorem 1.6 (The actual constructed H preserves the original cut and numbered indices).**

$$\forall Hgroup \in Type, groupH \in \operatorname{Group}\left(Hgroup\right), finiteH \in \operatorname{Fintype}\left(Hgroup\right), decH \in \operatorname{DecidableEq}\left(Hgroup\right), a \in Nat, M \in \operatorname{GroupMat}\left(Hgroup, a, a\right), N \in \operatorname{GroupMat}\left(Hgroup, a, a\right), C \in \operatorname{GroupMat}\left(Hgroup, a, a\right), T \in \operatorname{NumberedData}\left(M, N, C\right), q \in Nat, K \in \operatorname{FiniteForgetting}\left(\operatorname{squares}\left(T\right), q\right), hN \in \operatorname{Essential}\left(\operatorname{expandedGraph}\left(N\right)\right),\; \forall alpha \in \operatorname{History}\left(\operatorname{expandedGraph}\left(M\right)\right), n \in Int,\; \operatorname{image}\left(\operatorname{H}\left(\operatorname{squares}\left(T\right), K\right), \operatorname{Cleft}\left(T, alpha, n\right)\right) = \operatorname{numberedRightRayUnion}\left(T, hN, alpha, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge.numbered_same_cut_whole_ray_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cleft T alpha n and Cright T beta n fix all integer coordinates k<=n of their full legal histories. numberedBeta(T,hN,alpha,n,r) is T.beta hN alpha n r, the generic betaFull representative after outEquiv. numberedRightRayUnion is the indexed union over r:ActualOut T alpha n of Cright T (numberedBeta r) n. The square map is T.squares.H K, with K : FiniteForgetting T.squares q and its positive q field; Essential(expandedGraph N) supplies represented full rays.

numbered_beta_endpoint identifies the component endpoint with expandedGraph C.target r.val. numbered_components_disjoint uses the right forgetting field to distinguish EVERY unequal full numbered edge index, even if its endpoint is repeated. This is a genuine same-integer-cut image of entire ray sets.

**Theorem 1.7 (Every component member lifts with its exact numbered boundary).**

$$\forall Hgroup \in Type, groupH \in \operatorname{Group}\left(Hgroup\right), finiteH \in \operatorname{Fintype}\left(Hgroup\right), decH \in \operatorname{DecidableEq}\left(Hgroup\right), a \in Nat, M \in \operatorname{GroupMat}\left(Hgroup, a, a\right), N \in \operatorname{GroupMat}\left(Hgroup, a, a\right), C \in \operatorname{GroupMat}\left(Hgroup, a, a\right), T \in \operatorname{NumberedData}\left(M, N, C\right), q \in Nat, K \in \operatorname{FiniteForgetting}\left(\operatorname{squares}\left(T\right), q\right), hN \in \operatorname{Essential}\left(\operatorname{expandedGraph}\left(N\right)\right),\; \forall alpha \in \operatorname{History}\left(\operatorname{expandedGraph}\left(M\right)\right), n \in Int, r \in \operatorname{ActualOut}\left(T, alpha, n\right), y \in \operatorname{History}\left(\operatorname{expandedGraph}\left(N\right)\right), hy \in y \in \operatorname{Cright}\left(T, \operatorname{numberedBeta}\left(T, hN, alpha, n, r\right), n\right),\; \exists x \in \operatorname{History}\left(\operatorname{expandedGraph}\left(M\right)\right),\; x \in \operatorname{Cleft}\left(T, alpha, n\right) \land \left(\operatorname{H}\left(\operatorname{squares}\left(T\right), K\right)\left(x\right) = y \land \operatorname{liftBoundary}\left(\operatorname{squares}\left(T\right), K, x, n\right) = \operatorname{value}\left(r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge.numbered_arbitrary_future_preimage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

liftBoundary(S,K,x,n) is (S.leftLift K x).boundary n and value(r)=r.val. The binder y is an arbitrary full legal history in Cright of the represented component. Forward phi-inverse recursion consumes its entire right future and yields x with the whole original alpha past through n, H x=y, and EXACTLY r.val as boundary at n. This is stronger than containment in a selected finite collection of representatives and is the reverse inclusion consumed by the concrete reset family.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge.NumberedData`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge.Squares`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge.historyHomeomorph`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge.numbered_arbitrary_future_preimage`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge.numbered_same_cut_whole_ray_image`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge.same_cut_full_rays`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge.whole_ray_preimage`
- Dependency: [D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion](FiniteWindowTableCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FixedBlockRigidity](FixedBlockRigidity.md)
