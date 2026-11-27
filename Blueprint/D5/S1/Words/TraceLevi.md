# Generalized Levi Factorization of Finite Traces

## Abstract

A common four-factor arrangement characterizes equality of two concatenated traces.

Fix an arbitrary universe level u, used below as a universe metaparameter. Let alpha be any type in Type(u), and let I be a symmetric irreflexive relation on alpha. A word is a native finite list over alpha; append denotes list concatenation and Mem(a,w) denotes native List.Mem and means that a occurs in w. Connected denotes D5.S1.Words.TraceProjection.Connected: the reflexive transitive closure of the contextual step exchanging l ++ a :: b :: k with l ++ b :: a :: k when I(a,b), with the same left and right contexts. It is not an additional supplied path or a separately chosen quotient relation.

**Theorem 1.1 (A simultaneous two-by-two factorization).**

$$\forall alpha \in \operatorname {Type}\left(u\right),\; \forall I \in alpha \to \left(alpha \to Prop\right),\; (\forall a \in alpha,\; \forall b \in alpha,\; (\operatorname {I}\left(a, b\right)) \Rightarrow (\operatorname {I}\left(b, a\right))) \Rightarrow ((\forall a \in alpha,\; \neg \operatorname {I}\left(a, a\right)) \Rightarrow (\forall x \in \operatorname {List}\left(alpha\right),\; \forall y \in \operatorname {List}\left(alpha\right),\; \forall z \in \operatorname {List}\left(alpha\right),\; \forall t \in \operatorname {List}\left(alpha\right),\; \operatorname {Connected}\left(I, \operatorname {append}\left(x, y\right), \operatorname {append}\left(z, t\right)\right) \iff (\exists p \in \operatorname {List}\left(alpha\right),\; \exists q \in \operatorname {List}\left(alpha\right),\; \exists r \in \operatorname {List}\left(alpha\right),\; \exists s \in \operatorname {List}\left(alpha\right),\; \operatorname {Connected}\left(I, x, \operatorname {append}\left(p, q\right)\right) \land \operatorname {Connected}\left(I, y, \operatorname {append}\left(r, s\right)\right) \land \operatorname {Connected}\left(I, z, \operatorname {append}\left(p, r\right)\right) \land \operatorname {Connected}\left(I, t, \operatorname {append}\left(q, s\right)\right) \land (\forall a \in alpha,\; (\operatorname {Mem}\left(a, q\right)) \Rightarrow (\forall b \in alpha,\; (\operatorname {Mem}\left(b, r\right)) \Rightarrow (\operatorname {I}\left(a, b\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TraceLevi.connected_append_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robert Cori, Dominique Perrin (1985). *Automates et commutations partielles*. DOI: [10.1051/ita/1985190100211](https://doi.org/10.1051/ita/1985190100211).

*Commentary.*

For every four words x,y,z,t, a connection from x ++ y to z ++ t is equivalent to the existence of four common words p,q,r,s. The row factors are x connected to p ++ q and y connected to r ++ s; the column factors are z connected to p ++ r and t connected to q ++ s. The same four words satisfy all four connections simultaneously. Every letter a of q and every letter b of r must satisfy I(a,b). This is a condition on each crossing pair of letters, and is stronger than asking only for a connection between q ++ r and r ++ q. Irreflexivity excludes a common letter from these two crossing factors.

The statement includes empty alphabets, empty words and factors, infinite alphabets, and repeated letters. It assumes no finite alphabet, nonempty alphabet, decidable equality, occurrence matching, heap, partial order, schedule, or cut refinement. The four factors are existential conclusions, not input data.

Cori and Perrin's Proposition 1.3 and its full proof on printed page 25 give the established four-factor arrangement for a finite alphabet A and a reflexive symmetric commutation relation theta. Their factors u,v,r,s correspond here to p,q,r,s. Their absolute commutation condition on v and r requires theta(a,b) for all crossing letters. Two obligations distinguish the present formulation from that source. First, the finite-alphabet congruence formulation must be related to the native contextual closure for arbitrary alpha. Second, the factors must satisfy the strict condition I(a,b) even though the reflexive source convention, theta(a,b) defined as a=b or I(a,b), also permits equality. The source telescope therefore does not directly supply the displayed native statement. No originality, effectiveness, complexity bound, or physical-history interpretation is asserted.

## References

- Truth anchor: `D5/S1/Words/TraceLevi.connected_append_iff`
- Dependency: [D5/S1/Words/TraceProjection](TraceProjection.md)
