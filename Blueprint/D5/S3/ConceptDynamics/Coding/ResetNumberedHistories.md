# Reset paths as numbered expanded histories

## Abstract

The actual positive-kernel reset space retains its absolute sign and suffix in a numbered, equivariant topological coding.

**Definition 1.1 (The Boolean group matrix).**

$$\forall q \in Nat, i \in \operatorname{Fin}\left(q\right), j \in \operatorname{Fin}\left(q\right),\; \operatorname{entry}\left(\operatorname{resetMatrix}\left(q\right), i, j\right) = \operatorname{sum}\left(\operatorname{indicatorSingle}\left(\operatorname{isZero}\left(j\right), \operatorname{ofAdd}\left(true\right), one\right), \operatorname{indicatorSingle}\left(\operatorname{isSuccessor}\left(i, j\right), groupIdentity, one\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNumberedHistories.resetMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sign is Multiplicative Bool with the native BooleanRing Bool addition, namely XOR; its identity is ofAdd false and tau is ofAdd true. The natural group matrix C(i,j) is single(tau,1) when j.val=0, plus single(1,1) when j.val=i.val+1. The two target conditions are disjoint. Thus each allowed labelled edge has coefficient one and number in Fin 1. No adjacency with forgotten labels or forgotten parallel-edge numbers replaces this matrix.

**Definition 1.2 (Local encoding and source decoding).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{Homeomorph}\left(\operatorname{ResetPath}\left(q\right), \operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNumberedHistories.resetHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NatPositive(q) means 0<q, with no additional assumption q>=2. ResetPath q is precisely ParryBilateralLaw.ResetPath: an Int-indexed sequence x_t=(b_t,i_t) for which TwistedResetPaths.kernel q (ParryResetLaw.parryParameter q) x_t x_(t+1)>0 at every integer origin. History is the existing subtype of Int-indexed expanded edges whose targets equal the next sources. Both spaces use their native product and subtype topologies, with the native discrete Bool, Fin and Multiplicative coordinate instances.

For q>=2, parry_stationary_law gives p>1/2 and p<=suffixWeight(q,p,i). Hence reset mass p/h_i and increment mass p*h_j/h_i are strictly positive. For q=1, the defined fallback parameter is 1/2 and the only suffix weight is 1/2, so reset mass is one. Increment is impossible. In either case the actual positive support consists exactly of a sign flip to suffix zero or a sign-preserving suffix increment. The one-suffix calculation is a deterministic flip and makes no claim that the fallback inverse parameter is the spectral radius of the unweighted transition.

numberedStep maps a positive adjacent pair ((b,i),(d,j)) to the edge with source i, target j, label ofAdd(xor b d), and number zero, together with absolute group coordinate ofAdd b. The support calculation proves that this precise label has coefficient one in C(i,j). The expanded target is (j,ofAdd b * ofAdd(xor b d))=(j,ofAdd d); it equals the next expanded source. The order is the existing right multiplication of the current group coordinate by the edge label.

The inverse reads (toAdd groupCoordinate,edge.source) at each time. An arbitrary numbered edge supplies a positive coefficient through its Fin number. The coefficient formula forces exactly one of the reset and increment alternatives; the actual history seam then supplies the next suffix and sign. This proves positive kernel support of the decoded path. Decoding an encoded path recovers every original coordinate. Encoding a decoded history recovers the same source, target and label; coefficient one forces its original number to be zero. Thus both inverse identities hold for the actual histories, rather than only for label projections.

Continuity of encoding is coordinatewise: the output at t is a discrete local function of input coordinates t and t+1. Decoding is a discrete local function of one expanded-edge coordinate t. Evaluation in the product topology and the subtype continuity rules give the homeomorphism. This construction does not use or repeat the private suffix or sign reconstruction in bilateral_reset_coding.

**Theorem 1.3 (One construction preserves time and complement).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \exists e \in \operatorname{Homeomorph}\left(\operatorname{ResetPath}\left(q\right), \operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right)\right),\; \left(\forall x \in \operatorname{ResetPath}\left(q\right), t \in Int,\; \operatorname{coordinate}\left(\operatorname{apply}\left(e, x\right), t\right) = \operatorname{numberedStep}\left(q, hq, \operatorname{positiveAdjacentPair}\left(x, t\right)\right)\right) \land \left(\left(\forall y \in \operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right), t \in Int,\; \operatorname{coordinate}\left(\operatorname{apply}\left(\operatorname{symm}\left(e\right), y\right), t\right) = \operatorname{pair}\left(\operatorname{toAdd}\left(\operatorname{groupCoordinate}\left(\operatorname{coordinate}\left(y, t\right)\right)\right), \operatorname{sourceSuffix}\left(\operatorname{coordinate}\left(y, t\right)\right)\right)\right) \land \left(\left(\forall x \in \operatorname{ResetPath}\left(q\right),\; \operatorname{apply}\left(e, \operatorname{resetShift}\left(q, x\right)\right) = \operatorname{shift}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{apply}\left(e, x\right)\right)\right) \land \left(\forall x \in \operatorname{ResetPath}\left(q\right),\; \operatorname{apply}\left(e, \operatorname{resetComplement}\left(q, x\right)\right) = \operatorname{groupHistory}\left(\operatorname{resetMatrix}\left(q\right), \operatorname{ofAdd}\left(true\right), \operatorname{apply}\left(e, x\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNumberedHistories.reset_numbered_coding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

coordinate means the underlying subtype function evaluated at the given integer. positiveAdjacentPair(x,t) contains (x_t,x_(t+1)) and its actual positive-kernel proof. sourceSuffix and groupCoordinate project the source suffix and absolute group coordinate of that expanded edge. The existential homeomorphism is resetHomeomorph itself, with the forward and inverse coordinates specified above.

resetShift sends x_t to x_(t+1); on histories shift is FiniteWindowTableCriterion.shift. Both adjacent input coordinates translate by one, so the numbered coding commutes with unit time. resetComplement applies TwistedResetPaths.flip to every source state. Complementing both adjacent signs leaves their XOR label fixed, while the absolute group coordinate changes by left multiplication by tau. Consequently the same coding intertwines complement with FixedBlockRigidity.groupHistory C tau, preserving the suffix, label and edge number.

The native topological and equivariant identification attaches the positive reset dynamics to the counted group graph. Existing TwistedPeriodicHistories.twistedPeriodEquiv and twistedPeriod_card concern this exact history type, with finite numbered word fibers and ordered signed seams for every positive period. Their generic extension and enumeration need no replacement. This statement does not identify a separate original marked-word language, prove the marked count Fix_K(k,n)+1=Fix_Y(k,n)+k*[k divides n], settle n<q multiple wraparounds, or claim novelty for a published scalar formula. Surviving integral dimension-group classes and an ordered positive cone require their own proofs; no integral splitting of the plus/minus lattices or order-infinitesimal conclusion follows here.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNumberedHistories.resetHomeomorph`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNumberedHistories.resetMatrix`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNumberedHistories.reset_numbered_coding`
- Dependency: [D5/S3/ConceptDynamics/Coding/FixedBlockRigidity](FixedBlockRigidity.md)
- Dependency: [D5/S3/TotalVariation/ParryBilateralLaw](../../TotalVariation/ParryBilateralLaw.md)
