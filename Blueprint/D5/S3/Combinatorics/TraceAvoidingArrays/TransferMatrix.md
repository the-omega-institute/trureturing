# Counting locally constrained finite words

## Abstract

Finite words with pair and triple conditions are counted by a weighted matrix on classes of row pairs.

**Definition 1.1 (Admissible continuations).**

$$\forall R \in \operatorname{Type},\; \forall P \in R \to \left(R \to \operatorname{Prop}\right),\; \forall Q \in R \to \left(R \to \left(R \to \operatorname{Prop}\right)\right),\; \forall a \in R,\; \forall b \in R,\; \forall xs \in \operatorname{List}\left(R\right),\; \operatorname{tailGood}\left(P, Q, a, b, xs\right) = \operatorname{match} xs \operatorname{with} \mid \operatorname{List}.\operatorname{nil} \mapsto \operatorname{True} \mid \operatorname{List}.\operatorname{cons}\left(c, cs\right) \mapsto (P\left(b, c\right)) \land ((Q\left(a, b, c\right)) \land (\operatorname{tailGood}\left(P, Q, b, c, cs\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.tailGood` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2011). *Trace-avoiding binary arrays: OEIS A185761–A185764*. URL: <https://oeis.org/A185761>.

*Commentary.*

After two specified rows, each new row must satisfy the pair test with its predecessor and the triple test with both preceding rows.

**Definition 1.2 (Locally admissible words).**

$$\forall R \in \operatorname{Type},\; \forall P \in R \to \left(R \to \operatorname{Prop}\right),\; \forall Q \in R \to \left(R \to \left(R \to \operatorname{Prop}\right)\right),\; (\operatorname{good}\left(P, Q, \operatorname{List}.\operatorname{nil}\right) = \operatorname{True}) \land ((\forall a \in R,\; \operatorname{good}\left(P, Q, \operatorname{List}.\operatorname{cons}\left(a, \operatorname{List}.\operatorname{nil}\right)\right) = \operatorname{True}) \land (\forall a \in R,\; \forall b \in R,\; \forall cs \in \operatorname{List}\left(R\right),\; \operatorname{good}\left(P, Q, \operatorname{List}.\operatorname{cons}\left(a, \operatorname{List}.\operatorname{cons}\left(b, cs\right)\right)\right) = \left((P\left(a, b\right)) \land (\operatorname{tailGood}\left(P, Q, a, b, cs\right))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.good` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2011). *Trace-avoiding binary arrays: OEIS A185761–A185764*. URL: <https://oeis.org/A185761>.

*Commentary.*

The empty word and every one-row word are admissible. Longer words satisfy the first pair test and all continuation tests.

**Definition 1.3 (Horizontal trace tests).**

$$\forall R \in \operatorname{Type},\; \forall J \in \operatorname{Type},\; \forall K \in \operatorname{Type},\; \forall tr \in R \to \left(R \to \left(J \to K\right)\right),\; \forall adj \in J \to \left(J \to \operatorname{Prop}\right),\; \forall a \in R,\; \forall b \in R,\; (\operatorname{pairOK}\left(tr, adj, a, b\right)) \Leftrightarrow (\forall j \in J,\; \forall k \in J,\; (adj\left(j, k\right)) \Rightarrow (tr\left(a, b, j\right) \ne tr\left(a, b, k\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.pairOK` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2011). *Trace-avoiding binary arrays: OEIS A185761–A185764*. URL: <https://oeis.org/A185761>.

*Commentary.*

For two rows, traces at adjacent block columns differ.

**Definition 1.4 (Vertical trace tests).**

$$\forall R \in \operatorname{Type},\; \forall J \in \operatorname{Type},\; \forall K \in \operatorname{Type},\; \forall tr \in R \to \left(R \to \left(J \to K\right)\right),\; \forall a \in R,\; \forall b \in R,\; \forall c \in R,\; (\operatorname{tripleOK}\left(tr, a, b, c\right)) \Leftrightarrow (\forall j \in J,\; tr\left(a, b, j\right) \ne tr\left(b, c, j\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.tripleOK` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2011). *Trace-avoiding binary arrays: OEIS A185761–A185764*. URL: <https://oeis.org/A185761>.

*Commentary.*

For three rows, traces at corresponding block columns in the two neighboring row pairs differ.

**Definition 1.5 (All neighboring tests).**

$$\forall R \in \operatorname{Type},\; \forall J \in \operatorname{Type},\; \forall K \in \operatorname{Type},\; \forall tr \in R \to \left(R \to \left(J \to K\right)\right),\; \forall adj \in J \to \left(J \to \operatorname{Prop}\right),\; \forall n \in \operatorname{Nat},\; \forall a \in \operatorname{Fin}\left(n + 1\right) \to R,\; (\operatorname{arrayOK}\left(tr, adj, n, a\right)) \Leftrightarrow ((\forall i \in \operatorname{Fin}\left(n\right),\; \forall k \in \operatorname{Fin}\left(n\right),\; \forall j \in J,\; (\operatorname{val}\left(k\right) = \operatorname{val}\left(i\right) + 1) \Rightarrow (tr\left(a\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right), a\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right), j\right) \ne tr\left(a\left(\operatorname{Fin}.\operatorname{castSucc}\left(k\right)\right), a\left(\operatorname{Fin}.\operatorname{succ}\left(k\right)\right), j\right))) \land (\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in J,\; \forall l \in J,\; (adj\left(j, l\right)) \Rightarrow (tr\left(a\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right), a\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right), j\right) \ne tr\left(a\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right), a\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right), l\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.arrayOK` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2011). *Trace-avoiding binary arrays: OEIS A185761–A185764*. URL: <https://oeis.org/A185761>.

*Commentary.*

The finite indexed array satisfies every horizontal and vertical neighboring-trace inequality.

**Theorem 1.6 (Indexed and recursive tests agree).**

$$\forall R \in \operatorname{Type},\; \forall J \in \operatorname{Type},\; \forall K \in \operatorname{Type},\; \forall tr \in R \to \left(R \to \left(J \to K\right)\right),\; \forall adj \in J \to \left(J \to \operatorname{Prop}\right),\; \forall n \in \operatorname{Nat},\; \forall a \in \operatorname{Fin}\left(n + 1\right) \to R,\; [\operatorname{Inhabited}\left(R\right)] (\operatorname{arrayOK}\left(tr, adj, n, a\right)) \Leftrightarrow (\operatorname{good}\left(\operatorname{pairOK}\left(tr, adj\right), \operatorname{tripleOK}\left(tr\right), \operatorname{List}.\operatorname{ofFn}\left(a\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.arrayOKIffGood` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2011). *Trace-avoiding binary arrays: OEIS A185761–A185764*. URL: <https://oeis.org/A185761>.

*Commentary.*

Reading an indexed array as a list gives exactly the recursive pair and triple tests.

**Theorem 1.7 (The weighted counting formula).**

$$\forall R \in \operatorname{Type},\; \forall S \in \operatorname{Type},\; [\operatorname{Fintype}\left(R\right)] [\operatorname{Fintype}\left(S\right)] [\operatorname{DecidableEq}\left(S\right)] \forall P \in R \to \left(R \to \operatorname{Prop}\right),\; \forall Q \in R \to \left(R \to \left(R \to \operatorname{Prop}\right)\right),\; \forall cl \in R \to \left(R \to S\right),\; \forall T \in \operatorname{Matrix}\left(S, S, \operatorname{Int}\right),\; \forall v \in S \to \operatorname{Int},\; (\forall a \in R,\; \forall b \in R,\; (P\left(a, b\right)) \Rightarrow (\forall s \in S,\; \sum_{(c: R)} \operatorname{if} (P\left(b, c\right)) \land ((Q\left(a, b, c\right)) \land (cl\left(b, c\right) = s)) \operatorname{then} (1 : \operatorname{Int}) \operatorname{else} 0 = T\left(cl\left(a, b\right), s\right))) \Rightarrow ((\forall s \in S,\; \sum_{(a: R)} \sum_{(b: R)} \operatorname{if} (P\left(a, b\right)) \land (cl\left(a, b\right) = s) \operatorname{then} (1 : \operatorname{Int}) \operatorname{else} 0 = v\left(s\right)) \Rightarrow (\forall n \in \operatorname{Nat},\; (\operatorname{Nat}.\operatorname{card}\left(\{a: \operatorname{Fin}\left(n + 2\right) \to R \mid \operatorname{good}\left(P, Q, \operatorname{List}.\operatorname{ofFn}\left(a\right)\right)\}\right) : \operatorname{Int}) = \operatorname{dotProduct}\left(v, \operatorname{Matrix}.\operatorname{mulVec}\left((T)^{n}, (1 : S \to \operatorname{Int})\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.cardMatrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2011). *Trace-avoiding binary arrays: OEIS A185761–A185764*. URL: <https://oeis.org/A185761>.

*Commentary.*

Suppose every allowed row pair in a given class has the same number of legal successors in each destination class, and the initial multiplicities are v. Induction on the continuation length gives the cardinality as the dot product of v with the corresponding matrix power applied to the constant-one vector.

**Theorem 1.8 (Transporting a vector relation).**

$$\forall S \in \operatorname{Type},\; [\operatorname{Fintype}\left(S\right)] [\operatorname{DecidableEq}\left(S\right)] \forall T \in \operatorname{Matrix}\left(S, S, \operatorname{Int}\right),\; \forall v \in S \to \operatorname{Int},\; \forall d \in \operatorname{Nat},\; \forall b \in \operatorname{Nat},\; \forall c \in \operatorname{Fin}\left(d\right) \to \operatorname{Int},\; (\operatorname{Matrix}.\operatorname{mulVec}\left((T)^{b + d}, (1 : S \to \operatorname{Int})\right) = \sum_{(j: \operatorname{Fin}\left(d\right))} \operatorname{HSMul}.\operatorname{hSMul}\left(c\left(j\right), \operatorname{Matrix}.\operatorname{mulVec}\left((T)^{b + \operatorname{val}\left(j\right)}, (1 : S \to \operatorname{Int})\right)\right)) \Rightarrow (\forall n \in \operatorname{Nat},\; \operatorname{dotProduct}\left(v, \operatorname{Matrix}.\operatorname{mulVec}\left((T)^{n + b + d}, (1 : S \to \operatorname{Int})\right)\right) = \sum_{(j: \operatorname{Fin}\left(d\right))} c\left(j\right) \cdot \operatorname{dotProduct}\left(v, \operatorname{Matrix}.\operatorname{mulVec}\left((T)^{n + b + \operatorname{val}\left(j\right)}, (1 : S \to \operatorname{Int})\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.scalarRelationShift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2011). *Trace-avoiding binary arrays: OEIS A185761–A185764*. URL: <https://oeis.org/A185761>.

*Commentary.*

Multiplication by a further matrix power and an initial row vector transports a polynomial relation to every later scalar count.

**Theorem 1.9 (Successive vectors are matrix powers).**

$$\forall S \in \operatorname{Type},\; [\operatorname{Fintype}\left(S\right)] [\operatorname{DecidableEq}\left(S\right)] \forall T \in \operatorname{Matrix}\left(S, S, \operatorname{Int}\right),\; \forall N \in \operatorname{Nat},\; \forall W \in \operatorname{Fin}\left(N + 1\right) \to \left(S \to \operatorname{Int}\right),\; (W\left(0\right) = (1 : S \to \operatorname{Int})) \Rightarrow ((\forall k \in \operatorname{Fin}\left(N\right),\; W\left(\operatorname{Fin}.\operatorname{succ}\left(k\right)\right) = \operatorname{Matrix}.\operatorname{mulVec}\left(T, W\left(\operatorname{Fin}.\operatorname{castSucc}\left(k\right)\right)\right)) \Rightarrow (\forall k \in \operatorname{Fin}\left(N + 1\right),\; \operatorname{Matrix}.\operatorname{mulVec}\left((T)^{\operatorname{val}\left(k\right)}, (1 : S \to \operatorname{Int})\right) = W\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.tabulatedPowers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2011). *Trace-avoiding binary arrays: OEIS A185761–A185764*. URL: <https://oeis.org/A185761>.

*Commentary.*

A finite table starting at the constant-one vector and satisfying each matrix-vector step agrees with the corresponding powers throughout its domain.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.arrayOK`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.arrayOKIffGood`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.cardMatrix`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.good`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.pairOK`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.scalarRelationShift`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.tabulatedPowers`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.tailGood`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.tripleOK`
