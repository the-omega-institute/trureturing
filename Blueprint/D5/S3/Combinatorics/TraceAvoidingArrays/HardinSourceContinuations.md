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

**Definition 1.2 (The four source classes).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.sourceClass`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.sourceClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Classes 0,1,2,3 are U,A,B,C. U means colour 2 is unseen. Otherwise A has p0=p2 and p1=p3, B has p0=p3, and C contains the remaining two proper equality patterns. In three labels these are exactly abab, abca, and abac or abcb.

**Definition 1.3 (Literal next-row counts).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.M`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.M` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

With row and column order U,A,B,C the matrix is ((16,16,8,32),(0,48,16,64),(0,16,16,32),(0,32,16,48)). Each entry counts actual Fin 6 next rows satisfying horizontal properness, both diagonals, and the current first-appearance scanner. The class count and preservation of admissibility are verified for every boundary and every actual next row.

**Definition 1.4 (The actual first rows).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.r`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.r` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The initial vector is (4,0,2,4). Its ten rows are U:0101,0104,0151,0154; B:0120,0125; C:0102,0121,0124,0152. There is no A first row.

**Definition 1.5 (The source vector recurrence).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.sourceV`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.sourceV` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For every class i, sourceV(0,i)=1 and sourceV(m+1,i)=sum over j of M(i,j)sourceV(m,j). The theorem identifies this recurrence with the existing literal row-continuation count for all admissible scanner states and boundaries.

**Theorem 1.6 (Universal literal interpretation of M and r).**

$$\forall m: \operatorname{Nat}\left(\right), (\forall s: \operatorname{Seen}\left(\right), \forall p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right), \operatorname{admissible}\left(s, p\right) \implies \operatorname{widthV}\left(\operatorname{rowOK}\left(\right), \operatorname{pairs}\left(\right), \operatorname{nextOK}\left(\right), m, s, p\right) = \operatorname{sourceV}\left(m, \operatorname{sourceClass}\left(s, p\right)\right)) \land \operatorname{Nat}.\operatorname{card}\left(\operatorname{HardinThinGraphTransport}.\operatorname{literalStrip}\left(\operatorname{true}\left(\right), m, 3\right)\right) = \sum_{j: \operatorname{Fin}\left(4\right)} \operatorname{r}\left(j\right) \cdot \operatorname{sourceV}\left(m, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.four_class_result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The first equality holds for every continuation length m, scanner state s and admissible boundary p. Here widthV uses rowOK(c)=proper(beta composed with c), pairs(c)=beta composed with c, and nextOK(p,c)=the two diagonal inequalities at all three adjacent positions. The proof decomposes by the unique next literal row, uses the exact class counts, and inducts on m. The second equality reads the actual (m+1)-by-4 rectangular literal strip through the existing width_counting_bridge and the exact first-row vector. It asserts an interpretation of every source class and continuation, independently of the existing terminal generating-function theorem. The construction neither divides by a group order nor replaces actual arrays by a finite-height sample.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.M`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.admissible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.four_class_result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.r`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.sourceClass`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.sourceV`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233170DiagonalStrip](HardinA233170DiagonalStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport](HardinThinGraphTransport.md)
