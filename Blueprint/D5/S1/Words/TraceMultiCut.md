# Simultaneous Two-Row Refinement of Finite Trace Products

## Abstract

One common pair of rows refines any finite ordered product of native traces.

Fix any universe level u as a universe metaparameter, any alphabet alpha in Type(u), and a symmetric irreflexive relation I on alpha. A word is a native finite List(alpha). Connected means exactly D5.S1.Words.TraceProjection.Connected, the reflexive transitive closure of the original contextual adjacent swap: l ++ a :: b :: t may be exchanged with l ++ b :: a :: t when I(a,b). The contexts remain unchanged. Mem is native list membership; append is concatenation; flatten concatenates a list of words in order; ofFn lists a Fin-indexed family in increasing order. The expression column(zs,j) is the native list entry zs[j], and Fin(length(zs)) consists of all column indices.

**Theorem 1.1 (A common refinement across every cut).**

$$\forall alpha \in \operatorname {Type}\left(u\right),\; \forall I \in alpha \to \left(alpha \to Prop\right),\; (\forall a \in alpha,\; \forall b \in alpha,\; (\operatorname {I}\left(a, b\right)) \implies (\operatorname {I}\left(b, a\right))) \implies ((\forall a \in alpha,\; \neg \operatorname {I}\left(a, a\right)) \implies (\forall x \in \operatorname {List}\left(alpha\right),\; \forall y \in \operatorname {List}\left(alpha\right),\; \forall zs \in \operatorname {List}\left(\operatorname {List}\left(alpha\right)\right),\; \operatorname {Connected}\left(I, \operatorname {append}\left(x, y\right), \operatorname {flatten}\left(zs\right)\right) \iff (\exists p \in \operatorname {Fin}\left(\operatorname {length}\left(zs\right)\right) \to \operatorname {List}\left(alpha\right),\; \exists r \in \operatorname {Fin}\left(\operatorname {length}\left(zs\right)\right) \to \operatorname {List}\left(alpha\right),\; \operatorname {Connected}\left(I, x, \operatorname {flatten}\left(\operatorname {ofFn}\left(p\right)\right)\right) \land \operatorname {Connected}\left(I, y, \operatorname {flatten}\left(\operatorname {ofFn}\left(r\right)\right)\right) \land (\forall j \in \operatorname {Fin}\left(\operatorname {length}\left(zs\right)\right),\; \operatorname {Connected}\left(I, \operatorname {column}\left(zs, j\right), \operatorname {append}\left(\operatorname {p}\left(j\right), \operatorname {r}\left(j\right)\right)\right)) \land (\forall j \in \operatorname {Fin}\left(\operatorname {length}\left(zs\right)\right),\; \forall k \in \operatorname {Fin}\left(\operatorname {length}\left(zs\right)\right),\; (\operatorname {lt}\left(j, k\right)) \implies (\forall a \in alpha,\; (\operatorname {Mem}\left(a, \operatorname {p}\left(k\right)\right)) \implies (\forall b \in alpha,\; (\operatorname {Mem}\left(b, \operatorname {r}\left(j\right)\right)) \implies (\operatorname {I}\left(a, b\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TraceMultiCut.connected_append_flatten_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robert Cori, Dominique Perrin (1985). *Automates et commutations partielles*. DOI: [10.1051/ita/1985190100211](https://doi.org/10.1051/ita/1985190100211).

*Commentary.*

For every pair of words x,y and every finite list of words zs, connection of x ++ y with flatten(zs) is equivalent to the existence of two families p,r on Fin(length(zs)). The same families satisfy every condition: x is connected to the concatenation of all p(j), y to that of all r(j), and each column zs[j] is connected to p(j) ++ r(j). Whenever j < k, every letter a in the later upper factor p(k) and every letter b in the earlier lower factor r(j) satisfy the strict relation I(a,b). Separate choices for the different cuts would not satisfy this simultaneous conclusion.

Induct on the list of columns. The binary native Levi factorization splits the first column into p0,r0 and the remaining product into q,s. Apply the induction hypothesis once to q,s and the tail columns, then prepend p0,r0 to the resulting families. A letter in any later upper factor occurs in their concatenation and therefore in q, since native connection preserves letter membership. Binary Levi's strict independence of q and r0 then gives every crossing from the first lower factor to a later upper factor. The other crossings come from induction. Conversely, reconstruct the tail connection by induction and apply binary Levi to the first column and that tail, using the union of the prescribed crossing conditions.

If zs is empty, membership preservation forces x and y to be empty, and both families have empty index type. Empty columns and row factors, empty or infinite alphabets, and repeated letters are included. Irreflexivity forbids a letter from occurring in an earlier lower and a later upper factor simultaneously. No decidable equality, finite or nonempty alphabet, occurrence matching, partial order, swap schedule, or refinement is an input.

Cori and Perrin's Corollary 1.4 on printed pages 25–26 gives the classical finite-product refinement under their standing assumptions of a finite alphabet A and reflexive symmetric commutation theta. Their u,v,x_i,p_i,q_i correspond to x,y,zs[i],p(i),r(i). Their literal column factorizations imply column congruences, and symmetry aligns their earlier-bottom/later-top direction with the displayed I(a,b). The convention theta(a,b) := a=b or I(a,b) alone does not give strict independence. The native result uses the strict binary Levi theorem for arbitrary alpha. The citation supplies the classical analogue; no novelty, effective reconstruction, or complexity bound is asserted.

## References

- Truth anchor: `D5/S1/Words/TraceMultiCut.connected_append_flatten_iff`
- Dependency: [D5/S1/Words/TraceLevi](TraceLevi.md)
