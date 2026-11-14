# Independent signs after the first vertex of each class

## Abstract

First occurrences and exact complementary-pair fibers on finite ordered graphs.

Vertices are Fin (n+1), with their natural order. The map beta has fibers {0,5}, {1,4}, {2,3}. Normal uses the existing good scanner with both flags initially false and fixes vertex zero to colour zero. By good_iff, every 2, 3 or 4 has an earlier 1, and every 3 has an earlier 2. No condition requires an absent colour to appear.

**Definition 1.1 (The literal scanner convention).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.Normal`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.Normal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The domain is nonempty. In a strip the vertex index is its row-major rank. The source convention of a zero empty-series coefficient is separate from the one empty function on an empty graph.

**Definition 1.2 (The minimum of a pair class).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.First`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.First` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

First p i says that no strictly earlier vertex has the same pair label as i. This predicate is also defined on Fin 0.

**Definition 1.3 (The order of the three pair classes).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.Ordered`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.Ordered` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The first label is zero. Every occurrence of label two has an earlier occurrence of label one. Together these conditions order all nonempty classes by their first vertex; labels may be absent.

**Theorem 1.4 (The exact first-appearance characterization).**

$$\forall n: \operatorname{Nat}\left(\right), \forall f: \operatorname{Fin}\left(n + 1\right) \to \operatorname{Fin}\left(6\right), \operatorname{Normal}\left(f\right) \iff (\operatorname{Ordered}\left(\operatorname{beta}\left(\right) \circ f\right) \land \forall i: \operatorname{Fin}\left(n + 1\right), \operatorname{First}\left(\operatorname{beta}\left(\right) \circ f, i\right) \implies \operatorname{Fin}.\operatorname{val}\left(f\left(i\right)\right) = \operatorname{Fin}.\operatorname{val}\left(\operatorname{beta}\left(f\left(i\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.normal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For a literal assignment, the pair labels are Ordered and the colour at every pair-class minimum equals its label. Conversely those two properties imply every literal predecessor requirement. To recover a required predecessor, take the least occurrence of its pair label at or before the current vertex. Its sign is fixed. If the current colour is 3 or 4 that predecessor is strictly earlier; if it uses pair two, Ordered first supplies the earlier pair-one class. This argument applies to arbitrary length, rather than to a finite sample.

**Definition 1.5 (The two colours of a pair).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.lift`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.lift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

A false sign selects p; a true sign selects 5-p. Here p is a Fin 3 label. The two choices are distinct, have the same beta label, and exhaust its two-element fiber.

**Definition 1.6 (The free vertices).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.Free`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.Free` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Free p is the subtype of vertices that are not first in their pair class. One vertex is omitted for each used label, including when only one or two labels occur.

**Definition 1.7 (Literal lifts of an ordered pair word).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.Fiber`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.Fiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The fiber retains the entire six-colour assignment, its Normal property and the equality of its beta projection with p.

**Definition 1.8 (Mutually inverse literal lifts and free signs).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.fiberEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.fiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The forward map reads whether the actual colour is at least three at each free vertex. The inverse fixes every first sign to false and uses the supplied Boolean function at every other vertex. beta_lift, lift_sign and sign_lift prove both inverse identities. First occurrences are in bijection with the range of p, so the number of free vertices is N-j, where j is the number of nonempty classes.

**Definition 1.9 (Literal graph assignments).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.Legal`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For every edge, the actual colours are unequal and their natural values do not sum to five. The existing colour_bond_iff identifies this exact condition with unequal beta labels. No connectivity or bipartiteness assumption enters.

**Definition 1.10 (The fiber over an actual proper colouring).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.GraphFiber`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.GraphFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The parameter p is a SimpleGraph.Coloring (Fin 3), not an assumed adjacency summary. Mathlib's colorClasses_isPartition and isIndepSet_colorClass identify its nonempty fibers as independent sets, and card_colorClasses_le bounds their number by three. The partitionEquiv below identifies the ordered colourings with all unlabelled independent-set partitions into at most three blocks.

**Theorem 1.11 (The exact graph fiber cardinality).**

$$\forall n: \operatorname{Nat}\left(\right), \forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n + 1\right)\right), \forall p: \operatorname{G}.\operatorname{Coloring}\left(\operatorname{Fin}\left(3\right)\right), \operatorname{Ordered}\left(p: \operatorname{Fin}\left(n + 1\right) \to \operatorname{Fin}\left(3\right)\right) \implies \operatorname{Nat}.\operatorname{card}\left(\operatorname{GraphFiber}\left(G, p\right)\right) = 2^{n + 1 - \operatorname{Fintype}.\operatorname{card}\left(\operatorname{Set}.\operatorname{range}\left(p: \operatorname{Fin}\left(n + 1\right) \to \operatorname{Fin}\left(3\right)\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For every finite graph on N=n+1 ordered vertices and every Ordered proper pair colouring p, the number of literal lifts is exactly 2^(N-j), with j the cardinality of the range of p. The graph condition adds no further sign restriction, because every sign lift preserves beta. A one-class assignment has N-1 free signs; the singleton therefore has exactly one lift. Fewer than three used labels are retained. In particular this count is not a uniform division of all labelled six-colourings by 48.

**Definition 1.12 (Actual unlabelled independent-set partitions).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.StablePartition`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.StablePartition` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The object is an equivalence relation on all N=n+1 vertices, with no edge inside a class, and at most three nonempty equivalence classes. Mathlib quotientEquivClasses identifies the quotient with its actual sets of vertices; isPartition_classes supplies the ordinary partition interpretation. No palette labelling is built into this object.

**Definition 1.13 (Ordered proper pair colourings).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.OrderedColoring`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.OrderedColoring` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

This is the subtype of actual proper Fin 3 colourings satisfying Ordered, including colourings using one or two classes.

**Definition 1.14 (One ordered colouring for every unlabelled partition).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.partitionEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.partitionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For any three-label word, keep its initial class as zero, name the class of the earliest differing vertex one, and name the remaining class two. The two tests preserve equality of labels. Minimality gives an earlier one whenever two occurs. For an already Ordered word this relabelling is the identity. Equal equivalence relations have the same earliest differing vertex, so their canonical words agree. Conversely embed the finite quotient of any StablePartition into Fin 3, compose with the quotient map, and apply this relabelling. This gives a proper colouring with exactly the original relation. The resulting equivalence proves both inverse identities for every graph and every positive N.

**Definition 1.15 (All literal assignments as partitions and independent signs).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.literalPartitionEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.literalPartitionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Project the actual six-colour assignment by beta to its proper pair colouring. The existing sigma-fiber equivalence decomposes all assignments by that exact projection, graphFiberEquiv removes the redundant edge witness, and fiberEquiv gives the Boolean choices off the minima. Reindexing by partitionEquiv gives Legal G ≃ Σ S : StablePartition G, (Free ((partitionEquiv G).symm S).val → Bool). Every literal assignment is recovered by the inverse; no quotient divisor or finite-size bound appears.

**Definition 1.16 (The palette fibre of a fixed partition).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.PaletteFiber`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.PaletteFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For any natural q, retain precisely the proper Fin q colourings whose equality relation is the fixed unlabelled partition. Unused palette names remain available.

**Definition 1.17 (Injective palette names on the actual classes).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.paletteFiberEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.paletteFiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

A colouring constant exactly on the partition classes descends to an injection from its quotient into Fin q. Conversely compose that injection with the quotient map; independence of the classes gives the proper-colouring law. Quotient induction proves both inverses, including empty fibres when q is too small.

**Definition 1.18 (Every colouring decomposes by its unlabelled partition).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.paletteColoringEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.paletteColoringEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For q≤3 the nonempty colour classes are a StablePartition, by the existing Mathlib palette-cardinality bound. Decomposition by the actual equality relation followed by paletteFiberEquiv gives G.Coloring (Fin q) ≃ Σ S : StablePartition G, (Quotient S.relation ↪ Fin q). This includes q=1,2,3 without presupposing how many labels are used. The subsequent numerical sums and 48L elimination remain separate exact-check obligations.

The source graph identity and its boundaries

For every nonempty finite ordered graph, write s_j for its partitions into j nonempty independent sets. The further partition correspondence in the revision-2 source gives L = Σ(j=1..3) 2^(N-j)s_j. Injectively assigning q palette names to the blocks gives P(q) = Σ_j (q)_j s_j, hence P(1)=s_1, P(2)=2s_1+2s_2 and P(3)=3s_1+6s_2+6s_3. Eliminating s_1,s_2,s_3 gives 48L=2^N(P(3)+3P(2)+15P(1)). An order-free partition sum would imply order independence of the total, rather than equality of the sets of legal assignments. The equivalences above establish the literal partition correspondence and the injective palette-label fibres. Their cardinal sums, the displayed numerical elimination, and order independence still require their own checked applications; they are not claimed by the fixed-fiber theorem alone.

Connected graphs and the empty boundary

For a connected bipartite graph with an edge, P(1)=0 and P(2)=2, so the source specialization is L=2^(N-4)(P(3)/3+2) in rational arithmetic. N=2 and N=3 must remain in this range: a negative exponent is an integer exponent in the rationals, not truncated natural subtraction. A singleton has L=1 and P(q)=q. An empty graph has one empty colouring and one empty assignment under the combinatorial convention; the displayed 48L identity is restricted to N>0 and must not be applied to that empty graph. Empty generating-series coefficients of the strip owners are zero by a separate convention.

The four-column interpretation

The authoritative full series is HardinA233170DiagonalStrip.result: F=2x(5-240x+2048x²)/((1-16x)(1-112x+1024x²)), with a_1=10, a_2=800, a_3=78336 and a_n=128a_(n-1)-2816a_(n-2)+16384a_(n-3) for n≥4. In the source presentation U means pair two is unseen, A has pattern abab, B has abca, and C has abac or abcb. For these four classes the row-continuation matrix is M=((16,16,8,32),(0,48,16,64),(0,16,16,32),(0,32,16,48)) and the first-row vector is r=(4,0,2,4). The source equations v(0)=1, v(m+1)=Mv(m), a_n=rv(n-1) assert a literal next-row decomposition at every continuation length. These particular four-class equations require their own interpretation proof; the existing full-series result is not by itself that interpretation.

The source next-row decomposition is literal: a candidate q has q_j≠q_(j+1), p_j≠q_(j+1) and p_(j+1)≠q_j for j=0,1,2. For p=0101 the compatible words are 0101,0102,0121,0201,0202,2101,2102,2121, with class totals A/B/C=(3,1,4). For p=0120 they are 0120,0121,2120,2121, with totals (1,1,2). For p=0102 they are 0101,0102,0201,0202,2101,2102, with totals (2,1,3). Permuting labels covers every representative; reversing positions interchanges the two C shapes. When both representatives 1 and 2 have appeared, each pair word has sixteen literal lifts. In U only one word avoids pair two and has sixteen lifts; every other word first fixes colour two and has eight lifts. This gives the displayed M, rather than a uniform orbit divisor.

The ten first rows are U:0101,0104,0151,0154; B:0120,0125; C:0102,0121,0124,0152; none is in A. Their first two entries must be 01, their third is 0,2 or 5, and the literal scanner and horizontal exclusions give precisely those fourth entries. Each array has a unique next row, and the previous pair word and two scanner flags retain exactly the compatibility and predecessor data. Thus the source induction is an exhaustive disjoint next-row decomposition at every continuation length. The separate kernel obligation is to connect these particular four classes and counts to that literal recursion.

The source continuation series

For g_j=Σ_(m≥0)v_j(m)x^m, g=1+xMg. Row A plus row B is twice row C, yielding g_A+g_B=2g_C. The reduced equations are g_U=1+x(16g_U+32g_A+24g_B), g_A=1+x(80g_A+48g_B), and g_B=1+x(32g_A+32g_B). With Q=1-112x+1024x², they give g_A=(1+16x)/Q, g_B=(1-48x)/Q and g_U=(1-56x+384x²)/((1-16x)Q). Finally F=x(4g_U+2g_B+4g_C)=x(4g_U+2g_A+4g_B). All denominators have constant term one; these are formal-series equations.

Actual diagonal and square strips

For T(n,k), horizontal and both diagonal edges are present, while vertical and wraparound edges are absent. For k≥2 every row is connected, a diagonal joins consecutive rows, and column parity gives a bipartition; for k=1 there are no edges. Square strips instead have horizontal and vertical edges. These graphs remain different. At width two, the six proper boundary words each have three successors in either graph. At width three the aba,abc classes have initial counts (6,6) and the common class-count matrix K=((3,2),(2,2)); P(3)=(6,6)K^(n-1)(1,1)ᵀ. Equal all-height counts require proving those decompositions and their induction. Bipartiteness alone does not prove the equality.

The source width-two successor lists are diagonal 01→01,02,21 and square 01→10,12,20. At width three they are diagonal 010→010,012,020,210,212 and 012→010,012,210,212; square 010→101,102,121,201,202 and 012→101,120,121,201. Grouping each list by aba or abc gives the displayed K in both cases. Label permutations cover the other boundary words. Induction on the number of rows would then give the common all-height P(3). This argument does not identify the graphs or prove equality for every palette size.

Columns one through three

The source formulas, for n≥1, are T(n,1)=6^n/48+4^n/16+5·2^n/16 and T(n,2)=(12^(n-1)+4^(n-1))/2. C_2=x(1-8x)/((1-4x)(1-12x)) and C_3=x(3-64x+192x²)/((1-8x)(1-40x+128x²)). The column-one recurrence has coefficients 12,-44,48 and onset n≥4; column two has 16,-48 and onset n≥3; column three has 48,-448,1024 and onset n≥4. The square-strip series already belong to HardinA233123SquareStrip.result and HardinA233124SquareStrip.result, for their distinct literal counts. With λ±=20±4√17, the source closed form is T(n,3)=8^(n-1)+((√17-3)λ_-^n+(√17+3)λ_+^n)/(32√17), with initial values 3,80,2688. The source diagonal-to-square connection and the closed forms need their own exact applications.

Row one and the credited A007582 shift

T(1,1)=1 and T(1,k)=(4^(k-2)+2^(k-2))/2 for k≥2. The recurrence is T(1,k)=6T(1,k-1)-8T(1,k-2) for k≥4. The graph is the actual path, with P(3)=3·2^(k-1). The source identifies this count with A007582(k-2), where A007582(0)=1. Britnell–Wildon equation (9) and Proposition 8.1 supply the earlier paired-partition interpretation; the other interpretations of that sequence are outside the present scope.

Rows two and three

The full literal series already belong to HardinA233175PairStrip.result and HardinA233176Ladder.result. They are R_2=x(3-28x-16x²+224x³)/((1-4x)(1-8x-32x²)) and R_3=x(11-272x-576x²+20992x³-53248x⁴)/((1-8x)(1-24x-256x²+1024x³)). Their recurrences have coefficients 12 at lag 1 and -128 at lag 3 for k≥5, and 32,64,-3072,8192 at lags 1,2,3,4 for k≥6. The two-row singleton is 3; its next values are 8,80,800. The three-row singleton is 11; its next values are 80,2688,78336,2469888. For k≥2 the two-row closed form is T(2,k)=2^(2k-3)+(√3/32)((4+4√3)^k-(4-4√3)^k).

The source B and H interpretations

In two rows, a column has equal or unequal labels, with initial counts (3,6). Disjoint consecutive supports give B=((2,2),(1,0)) and P(3)=(3,6)B^(k-1)(1,1)ᵀ. In three rows, the classes 000, 001 or 011, 010 have initial counts (3,12,6) and H=((2,4,2),(1,1,0),(1,0,0)). For k≥2, P(3)=(3,12,6)H^(k-1)(1,1,1)ᵀ. The omitted class 012 has no successor and no predecessor from the other classes. It contributes exactly six colourings only at k=1, where the actual P(3) is 27 and the literal normalized count is 11. Thus the H formula is not valid at k=1. The characteristic polynomials of B and H are z²-2z-2 and z³-3z²-4z+2. These matrix interpretations are separate from the already proved terminal series.

The four-pair A233162 source

A233162 counts an actual path of m vertices with eight colours 0 through 7, complementary pairs summing to seven, and first representatives 0,1,2,3. Every 2,3,4,5,6 requires an earlier 1; every 3,4,5 requires an earlier 2; every 4 requires an earlier 3. Adjacent pair labels differ. This is a four-pair problem, not the six-colour edgeless problem by definition. Britnell–Wildon Proposition 8.1 gives the reversible marked-partition correspondence leading to b_m=T(m-1,1) for m≥2, with b_1=1 separately. In particular b_1 differs from T(0,1)=0 under the series convention. The formula is b_m=2^(m-6)(90+9·2^m+2·3^m)/9 for m≥2, the series is x(1-11x+35x²-29x³)/((1-2x)(1-4x)(1-6x)), and the recurrence coefficients are 12,-44,48 for m≥5. Its negative rational exponents at m=2,3,4,5 must not be implemented as natural subtraction. The actual four-pair path correspondence remains required to use these formulas for the source sequence.

Scope and source attribution

The application scope is precisely A233174 columns 1–4 and rows 1–3, A233123, A233124, A233175, A233176, and the stated A233162 and A007582 connections. A233174 columns 5–7 and rows 4–7, A233171–A233173 and A233177–A233180 are excluded. This revision-2 source is distinct from Hardin–Barker/Stern A233126 revision 5. Its authors are Haobo Ma, ChronoAI Pte Ltd, Singapore, and Wenlin Zhang, National University of Singapore and ChronoAI Pte Ltd, Singapore. The source supplies written graph and application arguments; the exact fiber theorem here proves only the explicitly stated foundation. No new solved-question, publication, coauthor or mathematical-priority claim follows.

The marked-partition interpretation is prior work of Britnell and Wildon, arXiv:1507.04803v1, equation (9) and Proposition 8.1, subsequently JCTA 148 (2017), 116–144, DOI 10.1016/j.jcta.2016.12.003. The graphical Stirling expansion is established in Duncan and Peele, Bell and Stirling Numbers for Graphs, JIS 12 (2009), Article 09.7.1, with attribution to Biggs, Proposition 9.2. The present finite-word characterization connects the actual scanner to its sign fibers; it makes no priority claim.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.Fiber`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.First`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.Free`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.GraphFiber`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.Normal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.Ordered`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.OrderedColoring`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.PaletteFiber`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.StablePartition`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.fiberEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.lift`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.literalPartitionEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.normal_iff`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.paletteColoringEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.paletteFiberEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.partitionEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
