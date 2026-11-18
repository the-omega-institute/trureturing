# Deleting the preceding pair preserves every source object

## Abstract

Literal path contraction and the prior even-marked partitions.

**Definition 1.1 (All four complementary pairs).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.beta8`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.beta8` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The literal palette is Fin 8. Its complementary pairs are 0/7, 1/6, 2/5 and 3/4. The pair label is min(c,7-c), with first representatives 0,1,2,3.

**Definition 1.2 (The actual eight-colour scanner).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.good8`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.good8` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The three flags record whether representatives 1,2,3 have appeared. Every 2,3,4,5,6 requires an earlier 1; every 3,4,5 requires an earlier 2; every 4 requires an earlier 3. The private good8_iff proves these exact earlier-occurrence clauses for every length and every initial flag state. Absent colours impose no condition.

**Definition 1.3 (The independent literal A233162 domain).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.Path8`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.Path8` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Path8 n consists of actual Fin 8 words on n+1 path vertices, with first colour zero, the literal earlier-occurrence clauses, and adjacent colours neither equal nor complementary to seven. This definition precedes the counting identification; it is not defined as a shift of another sequence.

**Definition 1.4 (Both word inverses at every length).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.contractEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.contractEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Let p be the previous pair label and c the current one. Delete p from the ordered palette: the contracted label is c if c<p, and c-1 if c>p. The source bond excludes c=p. The inverse inserts the missing label: send d to d if d<p, and d+1 otherwise. Retain the high/low sign. The complete finite step certificate proves the two local inverses, admissibility and equality of the updated used-pair states. Induction gives both inverse identities for arbitrary word length, including the empty tail. The previous pair is always in the used palette; a new pair corresponds exactly to a new contracted label. This is the class-level correspondence of Britnell–Wildon Proposition 8.1.

**Definition 1.5 (The actual path and independent vertices).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.pathEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.pathEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For every n≥0, Path8(n+1) is equivalent to Legal of the edgeless graph on Fin(n+1). Removing the forced initial zero gives the source tail, contractEquiv transforms that entire tail, and the target scanner is exactly the existing six-colour normalization. Both inverse maps preserve all literal entries. Thus a path on m≥2 vertices corresponds to the actual independent-vertex problem on m-1 vertices.

**Definition 1.6 (Even subsets of marked block elements).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.EvenMarking`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.EvenMarking` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For an ordered partition word p, a marking is an actual Boolean function on the vertices. For each nonempty class, the bit at its minimum plus the number of marked nonminimal vertices in that class is even. There is exactly one minimum; every other vertex lies in Free p. This is the even-marked partition convention of Britnell–Wildon, rather than a free choice of the minimum mark.

**Definition 1.7 (The minimum mark is determined by parity).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.evenMarkEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.evenMarkEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Choose the bits at nonminimal vertices. Mark the minimum precisely when their marked count is odd. Forgetting the minimum and filling it by parity are inverse. Every block of size b therefore has 2^(b-1) possible even markings.

**Definition 1.8 (The full four-pair marked-partition correspondence).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.markedPartitionEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.markedPartitionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Compose pathEquiv with the existing literalPartitionEquiv and the parity equivalence, reusing the actual unlabelled StablePartition and its canonical inverse. The result is an equivalence from the original eight-colour path on n+2 vertices to even-marked partitions of n+1 vertices into at most three nonempty blocks. In the source convention a marked colour is its pair's first representative. Accordingly the sign-to-mark map complements the high-colour bit at nonminimal vertices before filling the minimum by parity. No uniform orbit division is used.

**Definition 1.9 (The original three-pair path).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.Path6`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.Path6` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

This domain has Fin 6 colours, complement sum five, the existing Normal scanner, and the literal path bonds. It retains the original source graph and scanner.

**Definition 1.10 (The existing one-row owner is reused).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.sixLiteralEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.sixLiteralEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Reading the only row identifies Path6 n with HardinThinGraphTransport.literalStrip true 0 n. The earlier-occurrence conditions are exactly widthNormal in the one-row domain, and the original colour_bond_iff identifies every adjacent bond.

**Definition 1.11 (Restricting the same inverse to three pairs).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.sixContractEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.sixContractEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Embed the three-pair palette into Fin 8 by retaining pair labels and high/low signs. A finite scanner certificate and induction preserve every predecessor clause. The path avoids pair three exactly when the contracted independent-vertex word avoids pair two. Restrict the same all-length inverse along this equivalence; the original four-pair source remains intact.

**Definition 1.12 (The prior at-most-two-block interpretation).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.sixMarkedPartitionEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.sixMarkedPartitionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The original literal one-row strip on n+2 path vertices corresponds bijectively to actual even-marked unlabelled partitions on n+1 vertices with at most two nonempty classes. This construction consumes sixLiteralEquiv to pass through Path6(n+1) and the same contraction inverse. The bound is on the cardinality of the actual equivalence-relation classes. The existing partition inverse and Mathlib quotient-to-range equivalence translate the contracted label bound into this class bound. The original path width is k=n+2, so its count is A007582(k-2), including n=0 and A007582(0)=1. The existing universal path_result supplies 2·count=4^n+2^n and its original recurrence onset k≥4.

**Definition 1.13 (The literal sequence and its exceptional first index).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.b`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.b` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Set the empty-series coefficient b_0=0 and b_(m+1)=card(Path8 m). In particular b_1=1 counts the single forced zero. This is separate from the strip-series convention T(0,1)=0. For m≥2 the path correspondence identifies b_m with T(m-1,1).

For m≥2, the source formula is b_m=2^(m-6)(90+9·2^m+2·3^m)/9. The exponent m-6 is an integer exponent in the rationals, including its negative values at m=2,3,4,5. Equivalently, b_(n+2)=6^(n+1)/48+4^(n+1)/16+5·2^(n+1)/16 for every n≥0. The full generating series is x(1-11x+35x²-29x³)/((1-2x)(1-4x)(1-6x)), with recurrence b_m=12b_(m-1)-44b_(m-2)+48b_(m-3) from m≥5. The first values b_1 through b_5 are 1,1,3,11,45. These are applications of the literal correspondence and the existing edgeless count, with the exceptional first coefficient retained.

Britnell and Wildon, Bell numbers, partition moves and the eigenvalues of the random-to-top shuffle in Dynkin Types A, B and D, arXiv:1507.04803v1, §4.1, equation (9) and Proposition 8.1, supply the prior even-marked interpretation and path correspondence. Equation (9) counts exactly j blocks by 2^(t-j) times the Stirling number; summing j≤r gives the at-most-r-block count B†_t(r). The text near A007582 contains an apparent exact-versus-cumulative notation discrepancy; this return uses the explicitly defined cumulative objects and does not silently alter the primary text. No new-priority claim is made.

The source return is Hardin A233170 revision 2, release 443827011; revision 3 changes only the title. Haobo Ma is affiliated with ChronoAI Pte Ltd, Singapore only. Wenlin Zhang is affiliated with the National University of Singapore and ChronoAI Pte Ltd, Singapore. The original 34/4/11 queue and ten-delivery accounting remain unchanged. Later six-row and sibling sources are separate.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.EvenMarking`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.Path6`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.Path8`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.b`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.beta8`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.contractEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.evenMarkEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.good8`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.markedPartitionEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.pathEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.sixContractEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.sixLiteralEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.sixMarkedPartitionEquiv`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport](HardinThinGraphTransport.md)
