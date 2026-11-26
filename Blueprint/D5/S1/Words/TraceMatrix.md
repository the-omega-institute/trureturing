# Common Refinement Matrices for Native Traces

## Abstract

A single matrix simultaneously refines every row and column of two finite trace products.

Fix a universe level u as a universe metaparameter, an alphabet alpha in Type(u), and a symmetric irreflexive relation I. Words are native finite List(alpha) values. Connected denotes precisely D5.S1.Words.TraceProjection.Connected: the reflexive transitive closure of exchanging adjacent letters a,b satisfying I(a,b), inside arbitrary unchanged left and right contexts. The operations length, entry, Mem, ofFn and flatten are native list length, list indexing, membership, increasing Fin-indexed enumeration and ordered concatenation. Thus entry(xs,i) means xs[i], and Fin(length(xs)) includes exactly the row indices. The two arguments of w are respectively a row and a column.

**Theorem 1.1 (One simultaneous matrix with strict crossings).**

$$\forall alpha \in \operatorname {Type}\left(u\right),\; \forall I \in alpha \to \left(alpha \to Prop\right),\; (\forall a \in alpha,\; \forall b \in alpha,\; (\operatorname {I}\left(a, b\right)) \implies (\operatorname {I}\left(b, a\right))) \implies ((\forall a \in alpha,\; \neg \operatorname {I}\left(a, a\right)) \implies (\forall xs \in \operatorname {List}\left(\operatorname {List}\left(alpha\right)\right),\; \forall ys \in \operatorname {List}\left(\operatorname {List}\left(alpha\right)\right),\; \operatorname {Connected}\left(I, \operatorname {flatten}\left(xs\right), \operatorname {flatten}\left(ys\right)\right) \iff (\exists w \in \operatorname {Fin}\left(\operatorname {length}\left(xs\right)\right) \to \left(\operatorname {Fin}\left(\operatorname {length}\left(ys\right)\right) \to \operatorname {List}\left(alpha\right)\right),\; (\forall i \in \operatorname {Fin}\left(\operatorname {length}\left(xs\right)\right),\; \operatorname {Connected}\left(I, \operatorname {entry}\left(xs, i\right), \operatorname {flatten}\left(\operatorname {ofFn}\left(\operatorname {w}\left(i\right)\right)\right)\right)) \land (\forall j \in \operatorname {Fin}\left(\operatorname {length}\left(ys\right)\right),\; \operatorname {Connected}\left(I, \operatorname {entry}\left(ys, j\right), \operatorname {flatten}\left(\operatorname {ofFn}\left(( i : \operatorname {Fin}\left(\operatorname {length}\left(xs\right)\right) \mapsto \operatorname {w}\left(i, j\right) )\right)\right)\right)) \land (\forall i \in \operatorname {Fin}\left(\operatorname {length}\left(xs\right)\right),\; \forall ii \in \operatorname {Fin}\left(\operatorname {length}\left(xs\right)\right),\; \forall j \in \operatorname {Fin}\left(\operatorname {length}\left(ys\right)\right),\; \forall jj \in \operatorname {Fin}\left(\operatorname {length}\left(ys\right)\right),\; (\operatorname {lt}\left(i, ii\right)) \implies ((\operatorname {lt}\left(jj, j\right)) \implies (\forall a \in alpha,\; (\operatorname {Mem}\left(a, \operatorname {w}\left(i, j\right)\right)) \implies (\forall b \in alpha,\; (\operatorname {Mem}\left(b, \operatorname {w}\left(ii, jj\right)\right)) \implies (\operatorname {I}\left(a, b\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TraceMatrix.connected_flatten_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robert Cori, Dominique Perrin (1985). *Automates et commutations partielles*. DOI: [10.1051/ita/1985190100211](https://doi.org/10.1051/ita/1985190100211).

*Commentary.*

For arbitrary finite lists of words xs and ys, their concatenations are connected exactly when there is one matrix w of words on Fin(length(xs)) by Fin(length(ys)). Each original row xs[i] is connected to its matrix row, read from left to right, and each original column ys[j] is connected to its matrix column, read from top to bottom. If i < ii and jj < j, every a in w(i,j) and every b in w(ii,jj) satisfy I(a,b). The same w occurs in all row, column and crossing conditions.

Induct on the rows. Separate the first word x from the concatenation of the remaining rows. The two-row result D5.S1.Words.TraceMultiCut.connected_append_flatten_iff gives one upper family p and one lower family r, with each ys[j] connected to p(j) ++ r(j). Apply the induction hypothesis to the remaining rows and the ordered family r, producing a single matrix v. Prepending p to v gives w. Its lower rows and their mutual crossings come from induction. Its column connections compose the two-row column connections with the corresponding column connections of v.

For a crossing involving the first row, a letter b in v(i,jj) belongs to the concatenation of column jj of v. D5.S1.Words.TraceLevi.mem_of_connected transports that membership back to r(jj). The two-row strict crossing law then gives I(a,b) for every a in p(j) when jj < j. This transfers the whole lower-column constraint to each of its individual factors while preserving a common choice.

Conversely, remove the first row of a given matrix and concatenate each remaining column to form r(j). The induction hypothesis connects the remaining source rows to the product of these r(j). Every letter in r(jj) occurs in some lower cell, so the prescribed matrix crossings give the two-row crossings. Applying the same two-row equivalence reconstructs the original connection.

With zero rows, membership preservation forces every column word to be empty; the matrix has empty row index type. Zero columns are included by the two-row equivalence and the induction. Empty individual factors, repeated letters, and empty or infinite alphabets are all included. No decidable equality, nonempty alphabet, nonzero dimension, occurrence matching, order representation, swap schedule, or prior refinement is assumed.

Cori and Perrin's Proposition 1.3 and Corollary 1.4 on printed pages 25–26 give the classical binary and two-row analogues for finite alphabets with reflexive symmetric commutation theta. Their two upper and lower factor families correspond to p and r in the induction. The arbitrary-row matrix follows here by the additional row induction using the native strict two-row result. The substitution theta(a,b) := a=b or I(a,b) alone does not imply strict I(a,b), and the cited source does not state this arbitrary-universe native matrix formula verbatim. No originality, published open-problem resolution, effective reconstruction or complexity bound is asserted.

## References

- Truth anchor: `D5/S1/Words/TraceMatrix.connected_flatten_iff`
- Dependency: [D5/S1/Words/TraceMultiCut](TraceMultiCut.md)
