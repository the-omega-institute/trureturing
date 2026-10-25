# Original pure endpoints and actual return classes

## Abstract

The classes of literal pure endpoints in the original point quotient correspond to the four actual fiber return-cycle quotients.

**Definition 1.1 (The original label fiber).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Flag`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Flag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A flag is an original ordered dart (omega,j,k) with j different from k and with the original corner label equal to nu. No endpoint sorting, different quotient or orbit enlargement is performed.

**Definition 1.2 (Pure barycentric coordinates).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.delta`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate at the selected tip is exactly one; all other coordinates are zero.

**Definition 1.3 (The endpoint in the original carrier).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpoint`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original corner and its delta coordinates satisfy the unchanged Carrier: the omitted coordinate is zero, coordinates are nonnegative, their sum is one and their corner label is nu.

**Definition 1.4 (The pure endpoint locus).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Endpoints`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Endpoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the range of the literal endpoint map inside the full original carrier, before any quotient is taken.

**Definition 1.5 (The original point quotient).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.PointQuotient`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.PointQuotient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quotient uses exactly EqvGen of the original guarded Step. It includes every original intermediate in a chain.

**Definition 1.6 (The restricted original dart relation).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.flagSetoid`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.flagSetoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the pullback of the original DartRelated setoid to Flag. The theorem proves flag and label saturation before identifying it with the generated restricted relation.

**Definition 1.7 (Original endpoint flag classes).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.FlagQuotient`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.FlagQuotient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the quotient of the nu-restricted flags by the full original dart relation.

**Definition 1.8 (The actual map to point classes).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpointClassMap`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpointClassMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Send each flag class to its literal endpoint class in the unchanged point quotient. Full bidirectional relation correspondence makes this map injective.

**Definition 1.9 (Four distinct root fibers).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Root`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In row order L0,L1,H2,H0, a root sheet has original corner number 0,1,2,0 respectively, and that corner has label nu. These fibers remain distinct until an explicit equivalence transports them.

**Definition 1.10 (Actual return permutations).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnPerm`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnPerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two low rows act by ell = v inverse times u squared; the two high rows by h = v squared times u. These are permutations of the original arbitrary right action.

**Definition 1.11 (Returns in the selected root fibers).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootReturn`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootReturn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Prove preservation of the original nu label, then restrict the actual return permutation to its Root. The construction allows nonfaithful, nonfree and nontransitive finite actions.

**Definition 1.12 (Actual root-return cycle classes).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.RootCycles`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.RootCycles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cycle quotient is SameCycle of the actual restricted permutation. Every fixed point is a cycle; period one is included.

**Definition 1.13 (The four row quotients).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.ReturnClasses`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.ReturnClasses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dependent sum over four rows contains their actual root-return cycle quotients. It counts no other nu component and uses no order of an acting group element.

**Definition 1.14 (Actual phase-zero flags).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootFlag`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootFlag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Encode a sheet in its original row at phase zero, preserving the original ordered endpoint pair and label.

**Definition 1.15 (The component enumeration consumer).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnClassMap`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnClassMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map each actual root-return class through its phase-zero flag to the original flag quotient. Injectivity follows from the full component enumeration and unique row/phase classification. Surjectivity pulls an arbitrary valid dart back by its actual phase offset and uses an occurrence of the same enumeration to reach it from phase zero.

**Definition 1.16 (Faithful return-class correspondence).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnClassesEquiv`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnClassesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence uses that actual map and its proved bijectivity. The proof reduces natural returns modulo the least positive pointPeriod supplied by actual_component_enumeration; it does not substitute the order of the return word.

**Definition 1.17 (Marked classes in the original quotient).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.EndpointClasses`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.EndpointClasses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These are the range of the injective endpointClassMap, an actual subset of the original point quotient.

**Definition 1.18 (Return classes as actual point classes).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpointClassesEquiv`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpointClassesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose the return-class equivalence with the injective original endpoint map onto its range. Its representative formula commutes with the original point quotient map.

**Definition 1.19 (The slot-zero fiber).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.ZeroFiber`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.ZeroFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

O_nu contains exactly those original sheets whose corner (omega,0) has label nu.

**Definition 1.20 (Preserving labels under corner normalization).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootToZero`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootToZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For row c, act by u to the power of its original root corner number. The public actual_corner_orbit_iff proves this is an equivalence to O_nu with inverse action by the inverse power. The proof keeps arbitrary groups and the same original corner quotient.

**Definition 1.21 (Conjugated actual returns).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.zeroReturn`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.zeroReturn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugate rootReturn by rootToZero. The same-cycle relation is transported in both directions by this equivalence.

**Definition 1.22 (The four words in row order).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.normalizedWord`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.normalizedWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The words are inverse s, inverse t, s times k, and k times t, using the original sWord,tWord,kWord. Thus they are c1, inverse c3, c2, inverse c4. Inverting a permutation preserves SameCycle; the conventional final c1,c2,c3,c4 order is the row order 0,2,1,3.

**Definition 1.23 (The conventional boundary order).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rowOrder`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rowOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The involutive row permutation (0,2,1,3) transports the original L0,L1,H2,H0 order into c1,c2,c3,c4 order.

**Definition 1.24 (Original boundary words).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryWord`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In conventional order the words are inverse s, s times k, t, inverse of k times t. They act on the same slot-zero fiber O_nu.

**Definition 1.25 (Actual oriented boundary returns).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryReturn`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryReturn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reorder the proved zeroReturn permutations and invert the last two. The theorem proves that these permutations act by the corresponding original boundaryWord.

**Definition 1.26 (Cycles of the actual boundary returns).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.BoundaryCycles`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.BoundaryCycles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use SameCycle of boundaryReturn on O_nu, retaining fixed points and repeated point classes.

**Definition 1.27 (Four boundary cycle quotients).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.BoundaryClasses`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.BoundaryClasses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This dependent sum uses the actual returns c1,c2,c3,c4 on the selected original slot-zero fiber.

**Definition 1.28 (Fiber, conjugacy and inverse correspondence).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryClassesEquiv`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryClassesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Quotient.congr transports the proved rootToZero equivalences; Mathlib's sameCycle_inv justifies the inverse directions; sigma congruence applies the row permutation. These are actual class equivalences, not count substitutions.

**Definition 1.29 (Boundary cycles as original endpoint classes).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryEndpointEquiv`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryEndpointEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose the actual boundary-class equivalence with the original endpoint-class equivalence. The theorem includes the commuting equality with the unchanged point quotient.

**Theorem 1.30 (Full endpoint restriction and actual return classes).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.actual_endpoint_return_classes`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.actual_endpoint_return_classes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every group G, arbitrary right action on a finite Omega, u,v in G and original corner class nu, two literal pure endpoints are Related if and only if their flags are DartRelated. The full original dart chain is equivalent to its nu-restricted flag chain, and the endpoint locus is saturated under every full original point chain. For any two points of the pure endpoint locus, the full original Related relation holds exactly when those points are connected by EqvGen of the original Step restricted to that locus.

The return-class equivalences above identify the actual endpoint classes with the four actual root-fiber cycle quotients and commute with the original point quotient. The theorem retains the existing positive point period and exact tour period three times that period, and proves the slot-zero conjugacy and both directions of same-cycle transport.

Point-relation reflection consumes actual_guarded_point_analysis through the strict neighborhood of the source endpoint. Restriction and saturation keep all transitive intermediates. The cycle correspondence consumes the exhaustion, unique ordered-pair classification and indexed occurrence formula of actual_component_enumeration. No component enumeration or minimal-period theorem is reproved.

Repeated quotient classes, period one, nonregular and nonfaithful actions are allowed. If Omega is empty, the statement quantified over its original nu is vacuous. The two low rows share a return word but have different root fibers; they are identified with slot zero only by the proved corner normalization equivalences.

This source-specific inference is derived from the original corner-pairing suppliers and pinned Mathlib relation and permutation APIs. It makes no literature-priority claim. It is an endpoint and cycle-class correspondence: a faithful polygon adapter, invariance under complete polygon normalization, manifold structure, orientation, Euler characteristic and genus require separate constructions and proofs.

Application: pure endpoints for an arbitrary raw face pairing. Let T be any type and P:RawFacePairing(T), retaining its fixed-point-free involutive facePair on T times Fin(4), its original three-slot faceMap and the paired inverse-slot law. Use the same P throughout. For x=(t,f) paired to (t′,g), the whole-vertex permutation is the derived sigma_x=frame_g^(-1) composed with Option(faceMap_x) composed with frame_f; Option(faceMap_x) fixes the omitted-face marker. These are the actual face-slot frames, not additional transport data. The compatible corner pairing is obtained by the same fixed frame changes, and label(t,j) is its corner quotient label. Fix any such label nu. No finiteness, topology, coloring or group action is required for this application.

The full corner carrier consists of x=((t,j),b) with b_j=0, all b_i>=0, sum_i b_i=1 and label(t,j)=nu. Its Point type retains the entire closed triangle. A raw Dart is the ordered triple d=((t,j),k), including raw triples with j=k; Flag(P,nu) restricts it to j!=k and label(t,j)=nu. Reuse the literal delta_k(i), equal to 1 at k and 0 elsewhere, and send a flag to endpoint(d)=((t,j),delta_k). This satisfies the full carrier conditions. The endpoint map is injective before any quotient: equality preserves the original corner, and evaluating the equal delta functions at k forces the tips to agree.

For every raw Dart d=((t,j),k), crossing face f sends it to dartMove_f(d)=((t′,sigma_(t,f)(j)),sigma_(t,f)(k)), where t′ is the tetrahedron of facePair(t,f). DartStep(d,e) requires f!=j, f!=k and e=dartMove_f(d). Define DartRelated as EqvGen of this relation on the full raw Dart type. Permutation injectivity preserves j!=k. On unequal darts, the actual carrier transport also preserves the corner label. Consequently, for every full raw DartRelated chain and every nu, membership in Flag(P,nu) is equivalent at its two ends. This invariant is proved before restricting the chain to the flag subtype.

Use the same full Point generator Step(x,y): there is f different from the omitted corner j, b_f=0, and y=move_f(x), with the barycentric vector transported by precomposition with sigma_(t,f)^(-1). At a literal endpoint b=delta_k, the zero-face condition b_f=0 is exactly f!=k. The permutation identity delta_k composed with sigma^(-1)=delta_(sigma(k)) then gives Step(endpoint(d),endpoint(e)) if and only if DartStep(d,e). The forward implication recovers the new tip by evaluating the target delta at sigma(k); it keeps the original face guard as well as the original corner.

Let Endpoints(P,nu) be the range of the literal endpoint map inside the full Point carrier, and Related=EqvGen(Step) on that full carrier. Endpoint membership is preserved in both directions by each Step. Forward transport sends delta_k to delta_(sigma(k)); backward transport recovers the source delta with sigma^(-1), using the target carrier to retain the unequal-corner guard and label. Induction through the complete EqvGen proves that Related(x,y) implies x is an endpoint if and only if y is an endpoint. In particular every intermediate connected to a source endpoint in a full Point chain is itself a literal endpoint.

For any flags d,e, the resulting full relation correspondence is Related(endpoint(d),endpoint(e)) if and only if DartRelated(d,e). To reflect a Point chain, lift its generator steps by the guarded equivalence, its reflexive case by endpoint injectivity, and its transitive case by the endpoint representative of the intermediate supplied by saturation. In the other direction, flag invariance keeps the full raw Dart chain inside Flag, and the same generator equivalence maps the resulting flag chain into the full Point relation. Both directions retain all original intermediates.

The two restriction statements are precise consequences of saturation. For flags d,e, their underlying raw darts are DartRelated exactly when d and e are in EqvGen of DartStep restricted to Flag(P,nu). For x,y in the subtype Endpoints(P,nu), Related(x,y) holds exactly when x and y are in EqvGen of Step restricted to that endpoint subtype. In each lifting induction, membership of a transitive intermediate follows from the corresponding full-chain invariant; projecting a restricted chain back gives the converse. Thus the full raw closure and the generated subtype closure agree on their stated saturated carriers.

For one fixed ordered flag d, its endpoint component is fully saturated in the entire Point carrier: Related(endpoint(d),y) if and only if there is a flag e with DartRelated(d,e) and endpoint(e)=y. Indeed full-chain saturation first supplies an endpoint representative e for y, and full relation reflection supplies its raw Dart relation to d; the converse is the same reflection followed by the representative equality. This describes the whole Point equivalence class of the selected endpoint, rather than only its intersection with a chosen list of endpoints.

Finally use the already established cap bridge for this same arbitrary P. Its affine map toTruncation sends ((t,j),b) to (t,a), with a_i=(3/4 if i=j, else 0)+b_i/4, in the unchanged truncated carrier 0<=a_i<=3/4 and sum_i a_i=1. TruncatedStep crosses an original face with a_f=0 using the same sigma. The cap bridge proves Related(x,y) if and only if EqvGen(TruncatedStep)(toTruncation(x),toTruncation(y)), where that closure is taken on the full truncated carrier. Composing with endpoint reflection gives DartRelated(d,e) if and only if the two truncated literal endpoints are related by that full ambient closure. The cap bridge retains every ambient intermediate through saturation of the same nu cap; no finite-T or topological part of that supplier is needed.

The endpoint conclusions above retain the endpoint order without a hypothesis forbidding a chain from exchanging endpoints. To compare with an original global edge, now forget that order explicitly. For an unequal raw dart d=((t,j),k), set occ(d)=(t,edgeIndex(j,k)) in the original Occurrence(T)=T times Fin(6), and set swap(d)=((t,k),j). The existing six-edge table identifies edgeIndex(j,k) with an unordered pair of distinct vertices. Every actual DartStep projects to the original P.edgeStep: choose the slot n in the crossed face f containing that same local edge, and use the derived sigma endpoint law to identify its image with the original faceMap(f,n). Full raw DartRelated chains therefore project to full EqvGen(P.edgeStep), with unequal endpoints preserved along every intermediate.

Conversely fix the actual source face x=(t,f) and edge slot n witnessing an original edgeStep, and any ordered endpoint dart d with occ(d)=(t,faceEdge(f,n)). The same six-edge table proves f differs from both endpoints of d. The lifted dart is exactly dartMove_f(d); it uses this same face and slot and has occurrence ((P.facePair(x)).tetrahedron,faceEdge((P.facePair(x)).face,P.faceMap(x,n))). Thus the lift retains the supplied port, rather than choosing an unrelated adjacency witness. The inverse move crosses the paired face and returns the same dart, by the paired inverse-slot law and sigma_(P.facePair(x))=sigma_x^(-1). The original edgeStep is symmetric by those same paired laws.

Fix any unequal dart d0 and let Component(P,d0) consist of all unequal darts d with DartRelated(d0,d). Let OccurrenceFiber(P,occ(d0)) consist of every original occurrence o with P.edgeLabel(o)=P.edgeLabel(occ(d0)). Projection by occ gives a map from this ordered component into that whole original fibre, because the edge label is the quotient by the original full EqvGen(P.edgeStep). No finite list or selected subfibre replaces that quotient fibre.

This projection is surjective without a no-reversal hypothesis. Define Reach(o) to mean some dart in Component(P,d0) has occurrence o. The exact port lift proves Reach is preserved by an original edgeStep; symmetry gives preservation in the reverse direction. Reach is therefore invariant along the full EqvGen(P.edgeStep). Quotient exactness lifts the defining equality of any occurrence-fibre member to such a full chain from occ(d0). Since d0 witnesses Reach(occ(d0)), that chain supplies an ordered dart above the arbitrary member. Repeated local edge labels and arbitrary intermediate occurrences are retained.

For two unequal darts with the same occurrence, the original six-edge table gives precisely two possibilities: the darts agree, or one is swap of the other. Raw DartStep commutes with swap because the same sigma transports both endpoints, and hence so does its full EqvGen. Impose only the local no-edge-reversal condition at the chosen root d0: there is no full DartRelated chain from d0 to swap(d0). If two members of Component(P,d0) project to the same occurrence, the swap alternative would combine their component chains and swap-equivariance to give that forbidden root reversal. Thus this local condition makes the projection injective; no global no-reversal condition on all edges is assumed.

Under this local condition, the actual projection therefore induces Component(P,d0) equivalent to OccurrenceFiber(P,occ(d0)), and its forward representative is exactly the original occurrence occ(d), unchanged. Take nu to be the corner label at the omitted endpoint of d0. The full-chain flag invariant makes every dart in this component a Flag(P,nu), so the endpoint saturation and reflection above identify the same component with the entire Point equivalence class of the literal endpoint of d0. Its occurrence comparison is thus a statement about that original full class, with the local no-reversal hypothesis needed for bijectivity. Without that hypothesis, the whole-fibre surjection remains the conclusion.

The endpoint restriction and the conditional ordered-component/occurrence-fibre equivalence just established require neither finite T nor topology, coloring, a group action or fixture data. Those two comparisons alone provide no cyclic order or topological chart. The finite occurrence-cycle construction below is a separate application with its own finiteness hypothesis; no disk, fan, atlas or manifold neighborhood follows from these endpoint comparisons.

Application: the actual uncolored occurrence cycle for the same raw face pairing. Now additionally assume Fintype(T), retaining exactly the arbitrary original P and its fixed-point-free involutive facePair, faceMap and paired inverse-slot law. The carrier remains the original Occurrence(T)=T times Fin(6), and P.GlobalEdge remains the quotient by the full original EqvGen(P.edgeStep). For an occurrence i=(t,e), its two incident faces are the original edgeFaces(e), with their actual slots given by edgeFaceSlots(e). No replacement edge quotient, selected orbit or preexisting coloring is introduced.

Choose a function r:Occurrence(T)->Bool using the existing private flag-orientation existence theorem for the pairing whose five fields are exactly those of P. Fintype(T) is used for this existence argument and the finite permutation construction. The chosen data comprise only r and the entersFace law stated below. If r(i) is false, incomingFace(i) is the first original incident face and outgoingFace(i) the second; if r(i) is true, their roles are exchanged. The incoming and outgoing slots are the corresponding entries of edgeFaceSlots(e). This chooses which face port is incoming at each occurrence; it does not choose an ordering of the two edge endpoints or assert local no-edge-reversal. It requires no color function or valid-coloring hypothesis.

Define N(i) directly from the original outgoing port. Put x=(t,outgoingFace(i)); if P.facePair(x)=(t′,g), then N(i)=(t′,faceEdge(g,P.faceMap(x,outgoingSlot(i)))). The supplied entersFace law is incomingFace(N(i))=g. These equations define the actual rawNext of P, rather than an arbitrary permutation of a set of equal labels. To prove injectivity, equal successors have equal tetrahedra and equal incoming faces, so their paired source faces agree. Injectivity of facePair recovers the source face; injectivity of faceEdge within that target face and of the original faceMap recovers the source slot, hence the original local edge and tetrahedron. Since Occurrence(T) is finite, injectivity gives surjectivity, making N a permutation.

The generator comparison retains the actual witness, not merely adjacency. Fix any original face x=(t,f) and slot n, and set i=(t,faceEdge(f,n)) and q=((P.facePair(x)).tetrahedron,faceEdge((P.facePair(x)).face,P.faceMap(x,n))). If f=outgoingFace(i), the local face-slot table gives n=outgoingSlot(i), and the defining formula gives q=N(i). The target face is exactly P.facePair(x)=(q.tetrahedron,incomingFace(q)), and the transported original slot satisfies P.faceMap(x,n)=incomingSlot(q). Thus both source and target ports are retained.

The only other case in that same table is f=incomingFace(i) and n=incomingSlot(i). Set k=N^(-1)(i) and source=(k.tetrahedron,outgoingFace(k)). From N(k)=i and entersFace(k), recover P.facePair(source)=(i.tetrahedron,incomingFace(i)), hence x=P.facePair(source). Involutivity gives P.facePair(x)=source. Comparing the edge of N(k) with the edge of i and using faceEdge injectivity identifies P.faceMap(source,outgoingSlot(k)) with n; the paired inverse-slot law then gives P.faceMap(x,n)=outgoingSlot(k). Consequently q=k=N^(-1)(i), with its actual paired target face and outgoing slot retained. This proves the full outgoing-or-incoming port dichotomy for every original (x,n), including repeated or parallel occurrences of a face-edge adjacency.

Every successor step i->N(i) is an original P.edgeStep, witnessed by its own outgoing face and slot, and therefore preserves the original quotient edge label. Conversely the port dichotomy sends every original P.edgeStep to a successor or predecessor step, hence to N.SameCycle. Induction through all constructors of the original EqvGen, including symmetry and every transitive intermediate, gives EqvGen(P.edgeStep)(i,q) implies N.SameCycle(i,q). For the reverse implication, finiteness expresses SameCycle by an actual nonnegative power N^a(i)=q. Iterating successor label preservation gives P.edgeLabel(i)=P.edgeLabel(q); exactness of the original quotient recovers EqvGen(P.edgeStep)(i,q). Thus the full original generated relation, successor SameCycle and equality of the original global-edge labels agree in both directions.

For any original global-edge class E, let F_E contain every original occurrence i with P.edgeLabel(i)=E. Successor label preservation and its inverse make N a bijection of this whole fibre. For any i,q in F_E, their original labels agree, so the preceding equivalence puts them in N.SameCycle. Therefore N.IsCycleOn(F_E): the entire original label fibre is one successor cycle. This conclusion includes all original occurrences in that quotient class, rather than only the orbit generated from a chosen list, and does not confuse a permutation preserving the fibre with a permutation transitive on it. IsCycleOn allows the identity on a singleton.

Choose an actual occurrence i0, take E=P.edgeLabel(i0), and let m be the cardinality of the original fibre F_E. The chosen root gives m>0. Enumerate it by A:Fin(m)->F_E, A(a)=N^a(i0), retaining the displayed original occurrence as the representative. The IsCycleOn power-injectivity theorem makes this map injective for 0<=a<m. Its bounded-power existence theorem reaches every member of the whole original fibre with such an exponent, so A is an equivalence. This enumeration is by actual successive face crossings, not an arbitrary finite-type equivalence followed by a declared cyclic order.

The same finite-cycle theorems give N^m(i0)=i0 and, for every natural a including zero, N^a(i0)=i0 if and only if m divides a. In particular m is the least positive return exponent. Equality of two powers is congruence of their exponents modulo m, so N(A(a))=A((a+1) mod m), including the wrap from the last enumerated occurrence to the root. When m=1, the successor fixes i0. When m=2, N(N(i0))=i0 and N(i0) differs from i0. No assumption m>=3, Nontrivial fibre or NeZero index type is imposed. Self-returning transitions and repeated or parallel ports remain covered by the same original witness law.

This m-cycle has occurrence carrier T times Fin(6). Each occurrence has two incident face-edge ports, so its fibre has 2m such ports before choosing an incoming direction. The product permutation used internally on those flags need not itself be a single cycle on all 2m ports. The orientation choice and entersFace law construct N on the m occurrences, and transitivity of that N is proved by the full original relation comparison. They do not identify the two ports as the same flag or replace an ordered endpoint dart by an unoriented occurrence.

No local no-edge-reversal hypothesis is used for this occurrence-cycle construction. To use its m-cycle to enumerate the selected ordered endpoint component at d0, separately impose the local condition already stated: d0 is not DartRelated to swap(d0). Then the proved occurrence projection from that component to F_(P.edgeLabel(occ(d0))) is an equivalence, with representative exactly occ(d). Composing its inverse with A enumerates the same original ordered component, and the endpoint reflection identifies that component with the full Point equivalence class of the literal endpoint. Without the local condition, the proved comparison supplies only the whole-fibre surjection; an ordered cyclic model would require its own verified construction retaining the endpoint choices, for example an appropriate double cover. The m-cycle on occurrences must not automatically be identified with an ordered endpoint cycle.

These occurrence-cycle and finite-power deductions reuse the original private flag-orientation supplier, the color-independent successor construction, the original paired-port argument and pinned Mathlib relation and permutation APIs. They introduce no canonical mathematical declaration or theorem Describe and make no code-retention or literature-priority claim. The endpoint results without finite T retain their earlier scope; the successor construction here has the stated Fintype(T) premise. Neither the occurrence cycle nor the conditional ordered-component comparison constructs a fan, disk, polygon adapter, atlas or manifold neighborhood, and neither identifies a fibre with a separate eighteen- or six-element fixture. Those geometric and fixture bridges remain separate obligations.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.BoundaryClasses`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.BoundaryCycles`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.EndpointClasses`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Endpoints`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Flag`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.FlagQuotient`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.PointQuotient`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.ReturnClasses`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Root`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.RootCycles`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.ZeroFiber`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.actual_endpoint_return_classes`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryClassesEquiv`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryEndpointEquiv`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryReturn`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryWord`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.delta`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpoint`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpointClassMap`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpointClassesEquiv`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.flagSetoid`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.normalizedWord`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnClassMap`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnClassesEquiv`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnPerm`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootFlag`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootReturn`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootToZero`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rowOrder`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.zeroReturn`
- Dependency: [D5/S3/Geometry/Gluing/ActualCornerPointPeriods](ActualCornerPointPeriods.md)
