# Completed rows and first appearances

## Abstract

The source four-class matrix counts actual literal continuations at every length.

The boundary p is a proper four-letter word on Fin 3. The scanner state s records whether colours 1 and 2 have appeared. A completed admissible row has seen 1; if 2 is unseen, every boundary label differs from 2. The same literal good and finish scanner as the existing strip definitions determines which actual next rows are allowed.

**Definition 1.1 (Actual admissible boundaries).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.admissible`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.admissible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The predicate is s.first=true, horizontal properness of p, and exclusion of pair two when s.second=false. It includes all such boundaries, with no height bound.

**Definition 1.2 (Decision for all admissible boundaries).**

$$\forall s: \operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right), ((\operatorname{HardinSourceContinuations}.\operatorname{instDecidableAdmissible}\left(s, p\right): \operatorname{Decidable}\left(\operatorname{HardinSourceContinuations}.\operatorname{admissible}\left(s, p\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.instDecidableAdmissible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The instance uses inferInstanceAs to decide the conjunction s.first=true, proper p, and the implication from s.second=false to exclusion of pair two at every Fin 4 position.

**Definition 1.3 (The four source classes).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.sourceClass`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.sourceClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Classes 0,1,2,3 are U,A,B,C. U means colour 2 is unseen. Otherwise A has p0=p2 and p1=p3, B has p0=p3, and C contains the remaining two proper equality patterns. In three labels these are exactly abab, abca, and abac or abcb.

**Definition 1.4 (Literal next-row counts).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.M`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.M` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

With row and column order U,A,B,C the matrix is ((16,16,8,32),(0,48,16,64),(0,16,16,32),(0,32,16,48)). Each entry counts actual Fin 6 next rows satisfying horizontal properness, both diagonals, and the current first-appearance scanner. The class count and preservation of admissibility are verified for every boundary and every actual next row.

**Definition 1.5 (The actual first rows).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.r`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.r` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The initial vector is (4,0,2,4). Its ten rows are U:0101,0104,0151,0154; B:0120,0125; C:0102,0121,0124,0152. There is no A first row.

**Definition 1.6 (The source vector recurrence).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.sourceV`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.sourceV` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For every class i, sourceV(0,i)=1 and sourceV(m+1,i)=sum over j of M(i,j)sourceV(m,j). The theorem identifies this recurrence with the existing literal row-continuation count for all admissible scanner states and boundaries.

**Theorem 1.7 (Exact admissible four-class transfer certificate).**

$$(\forall s: \operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right), ((\operatorname{HardinSourceContinuations}.\operatorname{admissible}\left(s, p\right)) \implies (\forall c: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(6\right), (((\operatorname{HardinThinGraphTransport}.\operatorname{proper}\left((\lambda (i: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(i\right)\right)))\right)) \land ((\operatorname{HardinThinGraphTransport}.\operatorname{compatible}\left(\operatorname{true}, p, (\lambda (i: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(i\right)\right)))\right)) \land (\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)))) \implies (\operatorname{HardinSourceContinuations}.\operatorname{admissible}\left(\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right), (\lambda (i: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(i\right)\right)))\right))))))) \land ((\forall c: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(6\right), (((c\left(0\right) = 0) \land ((\operatorname{HardinThinGraphTransport}.\operatorname{proper}\left((\lambda (i: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(i\right)\right)))\right)) \land (\operatorname{HardinA233175PairStrip}.\operatorname{good}\left((\operatorname{false}, \operatorname{false}), c\right)))) \implies (\operatorname{HardinSourceContinuations}.\operatorname{admissible}\left(\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left((\operatorname{false}, \operatorname{false}), c\right), (\lambda (i: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(i\right)\right)))\right)))) \land ((\forall s: \operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right), ((\operatorname{HardinSourceContinuations}.\operatorname{admissible}\left(s, p\right)) \implies (\forall j: \operatorname{Fin}\left(4\right), (\sum_{c: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(6\right)} (((\operatorname{if} (((\operatorname{HardinThinGraphTransport}.\operatorname{proper}\left((\lambda (i: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(i\right)\right)))\right)) \land ((\operatorname{HardinThinGraphTransport}.\operatorname{compatible}\left(\operatorname{true}, p, (\lambda (i: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(i\right)\right)))\right)) \land (\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)))) \land (\operatorname{HardinSourceContinuations}.\operatorname{sourceClass}\left(\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right), (\lambda (i: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(i\right)\right)))\right) = j)) \operatorname{then} (1) \operatorname{else} (0)): \operatorname{Int})) = \operatorname{HardinSourceContinuations}.\operatorname{M}\left(\operatorname{HardinSourceContinuations}.\operatorname{sourceClass}\left(s, p\right), j\right)))))) \land (\forall j: \operatorname{Fin}\left(4\right), (\sum_{c: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(6\right)} (((\operatorname{if} (((c\left(0\right) = 0) \land ((\operatorname{HardinThinGraphTransport}.\operatorname{proper}\left((\lambda (i: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(i\right)\right)))\right)) \land (\operatorname{HardinA233175PairStrip}.\operatorname{good}\left((\operatorname{false}, \operatorname{false}), c\right)))) \land (\operatorname{HardinSourceContinuations}.\operatorname{sourceClass}\left(\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left((\operatorname{false}, \operatorname{false}), c\right), (\lambda (i: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(i\right)\right)))\right) = j)) \operatorname{then} (1) \operatorname{else} (0)): \operatorname{Int})) = \operatorname{HardinSourceContinuations}.\operatorname{r}\left(j\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.four_class_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The certificate proves admissible successors and initial states, every actual six-colour transition count M, and the normalized initial distribution r. At saturated Seen flags, scanner_fibres pushes the transition projection to sixteen times the proper three-colour successor count. The exact budget and class adapter followed by integer division supplies the proper diagonal sectors of the width-four defect strips. Their raw initial distributions are separate.

**Theorem 1.8 (Universal literal interpretation of M and r).**

$$\forall m: \operatorname{Nat}, ((\forall s: \operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right), ((\operatorname{HardinSourceContinuations}.\operatorname{admissible}\left(s, p\right)) \implies (\operatorname{HardinA233251TriangleStrip}.\operatorname{widthV}\left((\lambda (c: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(6\right)) \mapsto (\operatorname{HardinThinGraphTransport}.\operatorname{proper}\left((\lambda (i: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(i\right)\right)))\right))), (\lambda (c: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(6\right)) \mapsto ((\lambda (i: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(i\right)\right))))), (\lambda (p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right)) \mapsto ((\lambda (c: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(6\right)) \mapsto (\operatorname{HardinThinGraphTransport}.\operatorname{compatible}\left(\operatorname{true}, p, (\lambda (i: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(i\right)\right)))\right))))), m, s, p\right) = \operatorname{HardinSourceContinuations}.\operatorname{sourceV}\left(m, \operatorname{HardinSourceContinuations}.\operatorname{sourceClass}\left(s, p\right)\right))))) \land ((\operatorname{Nat}.\operatorname{card}\left(\operatorname{HardinThinGraphTransport}.\operatorname{literalStrip}\left(\operatorname{true}, m, 3\right)\right): \operatorname{Int}) = \sum_{j: \operatorname{Fin}\left(4\right)} (\operatorname{HardinSourceContinuations}.\operatorname{r}\left(j\right) \cdot \operatorname{HardinSourceContinuations}.\operatorname{sourceV}\left(m, j\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.four_class_result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The first equality holds for every continuation length m, scanner state s and admissible boundary p. Here widthV uses rowOK(c)=proper(beta composed with c), pairs(c)=beta composed with c, and nextOK(p,c)=the two diagonal inequalities at all three adjacent positions. The proof decomposes by the unique next literal row, uses the exact class counts, and inducts on m. The second equality reads the actual (m+1)-by-4 rectangular literal strip through the existing width_counting_bridge and the exact first-row vector. It asserts an interpretation of every source class and continuation, independently of the existing terminal generating-function theorem. The construction neither divides by a group order nor replaces actual arrays by a finite-height sample.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.M`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.admissible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.four_class_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.four_class_result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.instDecidableAdmissible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.r`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.sourceClass`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.sourceV`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport](HardinThinGraphTransport.md)
