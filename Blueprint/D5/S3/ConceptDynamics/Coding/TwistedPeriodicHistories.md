# Twisted periods from finite seamed words

## Abstract

Every positive twisted period is an actual legal bilateral history reconstructed from one finite numbered word and its ordered group seam.

**Definition 1.1 (Restriction and signed extension are inverse).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finiteH \in \operatorname{Fintype}\left(H\right), n \in Nat, C \in \operatorname{GroupMat}\left(H, n, n\right), h \in H, j \in Nat, hj \in \operatorname{NatPositive}\left(j\right),\; \operatorname{Equiv}\left(\operatorname{TwistedPeriod}\left(C, h, j\right), \operatorname{SeamWords}\left(C, h, hj\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/TwistedPeriodicHistories.twistedPeriodEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NatPositive(j) means 0<j. TwistedPeriod(C,h,j) is the subtype of actual History(expandedGraph C) satisfying shift iterated j times of x equals groupHistory(C,h,x). SeamWords(C,h,hj) is Sigma i:Fin n, Sigma z:H, WordFiber C hj i i (z inverse times h times z). WordFiber retains every original edge and parallel-edge number, both endpoints and the ordered total label. The bridge requires no essentiality, inertness, assumed history equivalence or assumed finiteness of histories. The zero-vertex case is included naturally as an empty sigma; no period-zero assertion is made.

Restriction reads the actual length-j window at zero and its initial coordinate z. The original expandedWordCoordinates inverse recovers this window as liftWord(w,z). Last-edge legality and the twist at zero give equal base endpoints and z*totalLabel(w)=h*z, hence totalLabel(w)=z inverse*h*z in this order.

For every integer address t=assemble j(q,r), extension uses the exact numbered edge (w.edge r, h^q*(z*prefixLabel w r)). Internal legality is supplied by liftWord. At each seam, the original lift_source and lift_target endpoint equations and z*totalLabel(w)=h*z join adjacent blocks. Euclidean blockAddress and both assemble inverse identities cover all negative as well as positive positions. The twist is proved on every integer coordinate. Signed recovery of an arbitrary twisted history uses the commuting translation and left-group permutations, Function.IsFixedPt.perm_zpow and Commute.mul_zpow. Thus restriction followed by extension recovers every coordinate, and extension followed by restriction recovers the same dependent finite word data. No generic signed-action induction or duplicated finite-word coordinate proof is added.

**Definition 1.2 (Actual finite enumeration).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finiteH \in \operatorname{Fintype}\left(H\right), n \in Nat, C \in \operatorname{GroupMat}\left(H, n, n\right), h \in H, j \in Nat, hj \in \operatorname{NatPositive}\left(j\right),\; \operatorname{Fintype}\left(\operatorname{TwistedPeriod}\left(C, h, j\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/TwistedPeriodicHistories.twistedPeriodFintype` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive-length argument is supplied explicitly. Fintype.ofEquiv transports the finite dependent sigma enumeration through twistedPeriodEquiv inverse. Consequently the actual twisted-history subtype is Finite. No global finiteness instance for unrestricted History is assumed.

**Theorem 1.3 (Exact diagonal conjugacy sum).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finiteH \in \operatorname{Fintype}\left(H\right), n \in Nat, C \in \operatorname{GroupMat}\left(H, n, n\right), h \in H, j \in Nat, hj \in \operatorname{NatPositive}\left(j\right),\; \operatorname{FintypeCard}\left(\operatorname{TwistedPeriod}\left(C, h, j\right)\right) = \operatorname{sumFin}\left(n, i, \operatorname{sumGroup}\left(H, z, \operatorname{coeff}\left(\operatorname{entry}\left(\operatorname{matrixPower}\left(C, j\right), i, i\right), \operatorname{product}\left(\operatorname{product}\left(\operatorname{inverse}\left(z\right), h\right), z\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/TwistedPeriodicHistories.twistedPeriod_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

FintypeCard uses the constructed twistedPeriodFintype. sumFin and sumGroup sum over every i:Fin n and z:H. MatrixPower is the same natural group-ring matrix power C^j. The proof uses the actual reconstruction equivalence on its live path, expands the two sigma cardinalities and directly applies FixedBlockRigidity.wordFiber_card to each loop fiber. It counts actual bilateral histories, including parallel edges, rather than substituting a coefficient-only proxy. This supplies the bridge for the original18.4 example; the literal D8 coefficients, period-one cancellation, all positive counts16^j and arbitrary original coprime block-map iterate laws remain separate obligations.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/TwistedPeriodicHistories.twistedPeriodEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/TwistedPeriodicHistories.twistedPeriodFintype`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/TwistedPeriodicHistories.twistedPeriod_card`
- Dependency: [D5/S3/ConceptDynamics/Coding/FixedBlockRigidity](FixedBlockRigidity.md)
