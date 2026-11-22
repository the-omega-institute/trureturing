# Dependent-Pair Projections of Finite Traces

## Abstract

Ordered dependent-pair projections characterize finite words modulo partial commutation.

Fix an arbitrary universe level u. In both displayed statements, u is a universe metaparameter. Let alpha be any type in Type(u), and let I be a symmetric irreflexive relation on alpha. Words are native finite lists over alpha. A legal step exchanges p ++ a :: b :: q with p ++ b :: a :: q when I(a,b), leaving both contexts unchanged. Connected(I,s,t) is the reflexive transitive closure of these steps. The independently defined readout pairProjection(a,b,s) deletes every letter other than a or b and keeps the original order. E(I,s,t), also called SameProjections, means equality of these lists for every a,b with not I(a,b), including a=b. EveryIndependent(I,a,p) means that I(a,b) holds for every letter b of p.

**Theorem 1.1 (Recovering a head and its residual word).**

$$\forall alpha \in \operatorname {Type}\left(u\right),\; \forall I \in alpha \to \left(alpha \to Prop\right),\; (\forall x \in alpha,\; \forall y \in alpha,\; (\operatorname {I}\left(x, y\right)) \Rightarrow (\operatorname {I}\left(y, x\right))) \Rightarrow ((\forall x \in alpha,\; \neg \operatorname {I}\left(x, x\right)) \Rightarrow (\forall a \in alpha,\; \forall r \in \operatorname {List}\left(alpha\right),\; \forall t \in \operatorname {List}\left(alpha\right),\; (\operatorname {E}\left(I, \operatorname {cons}\left(a, r\right), t\right)) \Rightarrow (\exists p \in \operatorname {List}\left(alpha\right),\; \exists q \in \operatorname {List}\left(alpha\right),\; t = \operatorname {append}\left(p, \operatorname {cons}\left(a, q\right)\right) \land \operatorname {EveryIndependent}\left(I, a, p\right) \land \operatorname {E}\left(I, r, \operatorname {append}\left(p, q\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TraceProjection.head_exposure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robert Cori, Dominique Perrin (1985). *Automates et commutations partielles*. DOI: [10.1051/ita/1985190100211](https://doi.org/10.1051/ita/1985190100211).

*Commentary.*

For every head a and words r,t, equality E(I,a::r,t) forces a factorization t=p++a::q in which each letter b of p satisfies I(a,b), and E(I,r,p++q) still holds. The diagonal readout first guarantees that a occurs in t. Choose its first occurrence, so p contains no a. If b in p were dependent on a, the (a,b) readout of the source would start with a, while the nonempty readout of p would force a different first letter. This contradiction proves the prefix commutation condition. Actual legal adjacent exchanges move a past p. Their readout invariance and cancellation of the common head give the residual equality.

**Theorem 1.2 (Exact classification by dependent pairs).**

$$\forall alpha \in \operatorname {Type}\left(u\right),\; \forall I \in alpha \to \left(alpha \to Prop\right),\; (\forall x \in alpha,\; \forall y \in alpha,\; (\operatorname {I}\left(x, y\right)) \Rightarrow (\operatorname {I}\left(y, x\right))) \Rightarrow ((\forall x \in alpha,\; \neg \operatorname {I}\left(x, x\right)) \Rightarrow (\forall s \in \operatorname {List}\left(alpha\right),\; \forall t \in \operatorname {List}\left(alpha\right),\; \operatorname {Connected}\left(I, s, t\right) \iff \operatorname {E}\left(I, s, t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TraceProjection.connected_iff_same_projections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robert Cori, Dominique Perrin (1985). *Automates et commutations partielles*. DOI: [10.1051/ita/1985190100211](https://doi.org/10.1051/ita/1985190100211).

*Commentary.*

For all words s,t, Connected(I,s,t) holds exactly when E(I,s,t) holds. A legal swap cannot retain both exchanged letters in a dependent-pair readout: retaining both would contradict symmetry or irreflexivity. Thus each step, and every finite sequence of steps, preserves the readouts. Conversely, induction on the source word uses head exposure to recover a commuting prefix and an equal residual observation. Induction connects the residual words, and moving the exposed head back through the prefix reaches the target.

Empty alphabets and words, infinite alphabets, and repeated letters are included. There is no finiteness, decidable equality, occurrence matching, partial order, or supplied path premise. Classical equality is used internally to define deletion as a native list filter. Cori and Perrin's Proposition 1.1, page 23 with proof on page 24, gives the established finite-alphabet characterization under a reflexive symmetric convention. Here that relation is a=b or I(a,b). The proof itself handles arbitrary alphabets directly. The result asserts existence of a finite legal connection and gives no complexity bound or claim of originality.

## References

- Truth anchor: `D5/S1/Words/TraceProjection.connected_iff_same_projections`
- Truth anchor: `D5/S1/Words/TraceProjection.head_exposure`
