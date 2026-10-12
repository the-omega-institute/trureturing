# Alternating reset square algebra

## Abstract

Typed original reset edges, endpoint square bijections and uniform strip forgetting.

In all displays q:Nat is unbounded, NatPositive(q) means 0 < q, and Sign is the fixed Multiplicative Bool with native XOR addition. Group, Fintype and DecidableEq instances are those of this concrete Sign; there are no additional varying carriers or class hypotheses. Matrix is resetMatrix q and Vertex is Fin q times Sign. product, sum, Equiv, fst, snd and length display the corresponding Lean types, equivalence, projections and List.length. The Lean q binders are implicit in these six declarations; hq is explicit in the first four and implicit in the two strip theorems. Prime display names spell Lean prime suffixes. Every other parameter and hypothesis is displayed below.

B q has reset constructors f(i,h) and advance constructors a(i,h,hi), with i:Fin q, h:Sign and hi:i.val+1<q. R q additionally has the distinct identity constructor d(i,h). sourceB and sourceR are (i,h). targetB and targetR send f to (zero hq, flipSign h), a to (next i hi,h), and targetR sends d to (i,h). Each legal original reset coefficient is exactly one: reset has label ofAdd true, advance has label 1, and both have the unique number zero. No adjacency quotient or edge multiplicity is discarded; the absolute source sign is retained. The additive identity-plus-reset number intervals are refined in the upper ResetAlternatingHistories owner.

**Definition 1.1 (Every original numbered reset edge and absolute sign).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{actualEdgeEquiv}\left(hq\right):\operatorname{Equiv}\left(\operatorname{B}\left(q\right), \operatorname{product}\left(\operatorname{Edge}\left(\operatorname{resetMatrix}\left(q\right)\right), Sign\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetAlternatingSquares.actualEdgeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

originalEdge and typedEdge are the two inverse functions, with actual_source and actual_target preserving the expanded graph endpoints. The inverse proofs use the actual matrix support and numbered-edge extensionality, including the coefficient-one number constraint. This equivalence works for every positive q, including q=1.

**Definition 1.2 (Identity vertices and original numbered reset edges remain distinct).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{actualBoundaryEquiv}\left(hq\right):\operatorname{Equiv}\left(\operatorname{R}\left(q\right), \operatorname{sum}\left(\operatorname{product}\left(\operatorname{Fin}\left(q\right), Sign\right), \operatorname{product}\left(\operatorname{Edge}\left(\operatorname{resetMatrix}\left(q\right)\right), Sign\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetAlternatingSquares.actualBoundaryEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward decoder is originalBoundary and the inverse is typedBoundary. The d constructor enters the identity-vertex summand; f and legal a enter the original numbered B-edge summand via actualEdgeEquiv. This typed sum equivalence composes with the numbered-edge equivalence for the literal matrix identity plus resetMatrix.

**Theorem 1.3 (A compatible left input and terminal boundary determine their square).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \forall x \in \operatorname{B}\left(q\right), s \in \operatorname{R}\left(q\right), hc \in \operatorname{targetB}\left(hq, x\right) = \operatorname{sourceR}\left(s\right),\; \operatorname{Square}\left(hq, \operatorname{fst}\left(\operatorname{leftSquare}\left(hq, x, s\right)\right), x, \operatorname{snd}\left(\operatorname{leftSquare}\left(hq, x, s\right)\right), s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetAlternatingSquares.leftSquare_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Square hq r x y s has eight guarded constructors fdSwap, fdFix, afSwap, afFix, ff, fa, ad and aa. The FD/AF swap requires both an available advance i.val+1<q and even i.val; fdFix retains the terminal exception. square_endpoints gives sourceR r=sourceB x, targetR r=sourceB y, targetB x=sourceR s and targetR s=targetB y. The endpointSquare is the constructed equivalence BRFiber hq v z to RBFiber hq v z for every v,z:Vertex: the left fiber retains (x,s), sourceB x=v, targetB x=sourceR s and targetR s=z; the right fiber retains (r,y), sourceR r=v, targetR r=sourceB y and targetB y=z. leftSquare uses its forward map; rightSquare uses its inverse. Existence and both uniqueness proofs construct this equivalence. On incompatible inputs the total operations use their specified identity fallback, so the displayed hc hypothesis is essential. The finite tables and numbered square interface use these operations.

**Theorem 1.4 (A compatible initial boundary and right input determine their square).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \forall r \in \operatorname{R}\left(q\right), y \in \operatorname{B}\left(q\right), hc \in \operatorname{targetR}\left(hq, r\right) = \operatorname{sourceB}\left(y\right),\; \operatorname{Square}\left(hq, r, \operatorname{fst}\left(\operatorname{rightSquare}\left(hq, r, y\right)\right), y, \operatorname{snd}\left(\operatorname{rightSquare}\left(hq, r, y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetAlternatingSquares.rightSquare_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the inverse endpointSquare operation on the exact same guarded relation. square_right_unique recovers both the input B edge and terminal R boundary from the initial R boundary and right B edge; square_left_unique recovers both the initial boundary and output edge from the left edge and terminal boundary. The operations are used by sweepLeft and sweepRight and their soundness proofs.

**Theorem 1.5 (A common q-edge left strip forces the initial full boundary).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), he \in \operatorname{Even}\left(q\right),\; \forall xs \in \operatorname{List}\left(\operatorname{B}\left(q\right)\right), ys \in \operatorname{List}\left(\operatorname{B}\left(q\right)\right), ysPrime \in \operatorname{List}\left(\operatorname{B}\left(q\right)\right), r \in \operatorname{R}\left(q\right), rPrime \in \operatorname{R}\left(q\right), s \in \operatorname{R}\left(q\right), sPrime \in \operatorname{R}\left(q\right), hs \in \operatorname{Strip}\left(hq, xs, r, s, ys\right), hsPrime \in \operatorname{Strip}\left(hq, xs, rPrime, sPrime, ysPrime\right), hlen \in \operatorname{length}\left(xs\right) = q, hc \in \operatorname{sourceR}\left(s\right) = \operatorname{sourceR}\left(sPrime\right),\; \operatorname{originalBoundary}\left(hq, r\right) = \operatorname{originalBoundary}\left(hq, rPrime\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetAlternatingSquares.strip_left_forgets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strip is the nil/cons inductive relation retaining all left and right B edges and both R boundaries, with existential internal boundaries in Prop. The lists and boundaries are otherwise unrestricted; the Lean xs,ys,ysPrime,r,rPrime,s,sPrime binders are implicit. leftRank is positive on unequal boundaries with a common source, at most q for even q, and strictly increases from initial to terminal along a common left edge. strip_left_rank sums this increase over the strip. The displayed common terminal source is the only endpoint comparison hypothesis; terminal targets are independent. first_output_independent uses this result on the q-edge tail of a q+1 strip; resetFiniteForgetting later obtains hc from the last common left edge.

**Theorem 1.6 (A common q-edge right strip forces the terminal full boundary).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), he \in \operatorname{Even}\left(q\right),\; \forall xs \in \operatorname{List}\left(\operatorname{B}\left(q\right)\right), xsPrime \in \operatorname{List}\left(\operatorname{B}\left(q\right)\right), ys \in \operatorname{List}\left(\operatorname{B}\left(q\right)\right), r \in \operatorname{R}\left(q\right), rPrime \in \operatorname{R}\left(q\right), s \in \operatorname{R}\left(q\right), sPrime \in \operatorname{R}\left(q\right), hs \in \operatorname{Strip}\left(hq, xs, r, s, ys\right), hsPrime \in \operatorname{Strip}\left(hq, xsPrime, rPrime, sPrime, ys\right), hlen \in \operatorname{length}\left(ys\right) = q,\; \operatorname{originalBoundary}\left(hq, s\right) = \operatorname{originalBoundary}\left(hq, sPrime\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetAlternatingSquares.strip_right_forgets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Lean xs,xsPrime,ys,r,rPrime,s,sPrime binders are implicit; there is no common-initial-source hypothesis. rightRank is positive on unequal boundaries, bounded by q and strictly decreases from initial to terminal along a common right edge. strip_right_rank sums this decrease and forces the terminal boundaries to agree after q edges. Distinct reset origins are included in the comparison. last_input_independent consumes the q-edge prefix and resetFiniteForgetting consumes arbitrary natural-indexed square strips. Both forgetting statements preserve the full originalBoundary values, hence their typed boundaries by actualBoundaryEquiv.injective. No bounded enumeration of q or words supplies either proof.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetAlternatingSquares.actualBoundaryEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetAlternatingSquares.actualEdgeEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetAlternatingSquares.leftSquare_spec`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetAlternatingSquares.rightSquare_spec`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetAlternatingSquares.strip_left_forgets`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetAlternatingSquares.strip_right_forgets`
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetNumberedHistories](ResetNumberedHistories.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge](SameCutWholeRayBridge.md)
