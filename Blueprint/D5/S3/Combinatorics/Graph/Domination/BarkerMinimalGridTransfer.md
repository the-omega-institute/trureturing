# Actual subsets and the all-length open-grid transfer

## Abstract

Actual labelled subsets, finite windows and all-length runs for the open three-row grid

**Definition 1.1 (Inclusion minimality).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.MinimalDominating`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.MinimalDominating` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Domination uses SimpleGraph.IsDominating and is required separately. Every proper finite subset must fail domination. No minimum-cardinality, total-domination, independence or symmetry condition is added.

**Definition 1.2 (Closed neighbourhoods).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.Closed`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.Closed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Closed G u v means u=v or G.Adj u v.

**Definition 1.3 (Existential private witnesses).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.ClosedPrivate`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.ClosedPrivate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ClosedPrivate G S v z means z is closed-adjacent to v and every selected closed neighbour of z equals v. Witnesses are propositions and are never counted choices.

**Theorem 1.4 (Private-witness characterization).**

$$\forall (V : Type), (\operatorname{Finite}\left(V\right)) \Rightarrow (\forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (S : \operatorname{Finset}\left(V\right)), (\operatorname{MinimalDominating}\left(G, S\right)) \Leftrightarrow ((\operatorname{IsDominating}\left(G, S\right)) \land (\forall (v : V), (v \in S) \Rightarrow (\exists (z : V), \operatorname{ClosedPrivate}\left(G, S, v, z\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.minimal_iff_closed_private` (`✓ std3`). ∎

*Citation.* Silvere Gangloff; Alexandre Talon (2019). *Asymptotic growth rate of square grids dominating sets: a symbolic dynamics approach*. DOI: [10.48550/arXiv.1906.10779](https://doi.org/10.48550/arXiv.1906.10779). URL: <https://arxiv.org/abs/1906.10779>.

*Commentary.*

The proof applies TrapezohedralMinimalDomination.minimalDominating_iff_private and minimalDominating_iff_proper. Finite subsets and their underlying sets have the same domination predicate, and every subset of the finite vertex type has a finite-set representative. The isolated-or-outside-private-neighbour characterization, under the domination premise, is published as Proposition 1 of Gangloff and Talon, arXiv:1906.10779v2, https://arxiv.org/abs/1906.10779. No novelty is claimed for that characterization. No external prose or proof code is transplanted.

**Definition 1.5 (The ordinary open grid).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.grid`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.grid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vertices are Fin 3 × Fin n; (r,c) represents the source label (r+1,c+1). Adjacency is exactly Nat.dist r s + Nat.dist c d = 1. The finite column type supplies open ends.

**Definition 1.6 (Read the masks).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.encode`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.encode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each column mask has one Boolean bit for each of the three labelled rows. The bit is true exactly when the actual vertex belongs to the subset.

**Definition 1.7 (Recover the subset).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.decode`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.decode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decoded subset contains precisely the vertices whose column-mask bit is true.

**Theorem 1.8 (Selected bits).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.mem_decode`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.mem_decode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every width n, word w and vertex v, membership v ∈ decode w is equivalent to w(v.column)(v.row)=true.

**Definition 1.9 (One subset, one word).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.subsetWordEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.subsetWordEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finset (Vertex n) and Word n are equivalent through mutually inverse encode and decode. No automorphisms or witness choices are identified.

**Definition 1.10 (Real empty versus absent).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.padded`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.padded` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A signed column in 0 ≤ c < n returns some mask; other coordinates return none. The present all-false mask differs from absence.

**Definition 1.11 (The original family).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.minimalSets`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.minimalSets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter every actual labelled vertex subset by MinimalDominating (grid n). The original family is defined before transport to words.

**Definition 1.12 (The source count).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

actualCount n is the cardinality of minimalSets n. The requested generating series uses positive n and separately sets its constant coefficient to zero.

**Definition 1.13 (Acceptance against the actual graph).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.ValidWord`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.ValidWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Acceptance means domination of decode w and an existential closed private witness for each selected vertex.

**Theorem 1.14 (Exact acceptance).**

$$\forall (n : \mathbb{N}), \forall (w : \operatorname{Word}\left(n\right)), (\operatorname{ValidWord}\left(w\right)) \Leftrightarrow (\operatorname{MinimalDominating}\left(\operatorname{grid}\left(n\right), \operatorname{decode}\left(w\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.validWord_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the general characterization to the independently defined actual decoded subset.

**Definition 1.15 (Restrict the bijection).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.minimalWordEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.minimalWordEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict subsetWordEquiv to the actual minimal dominating subsets and accepted words.

**Definition 1.16 (Five-column criterion).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.ColumnTest`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.ColumnTest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every centre vertex is closed-dominated. Every selected centre vertex has an actual closed-neighbour witness; uniqueness is tested among selected vertices at column distance at most two. Actual finite-grid vertex types exclude absent witnesses.

**Theorem 1.17 (Every real centre at every width).**

$$\forall (n : \mathbb{N}), \forall (S : \operatorname{Finset}\left(\operatorname{Vertex}\left(n\right)\right)), (\operatorname{MinimalDominating}\left(\operatorname{grid}\left(n\right), S\right)) \Leftrightarrow (\forall (c : \operatorname{Fin}\left(n\right)), \operatorname{ColumnTest}\left(S, c\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.minimal_iff_column_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A witness is at column distance at most one, and every selected neighbour of it is at distance at most two by the natural-distance triangle inequality. This proves that the five-column restriction retains the complete proper-subset condition, including widths one and two.

The actual subset family is the source of the count throughout the transfer construction. The column criterion supplies the local tests, and the subset-word equivalence preserves every labelled choice without counting existential witnesses.

**Definition 1.18 (All states).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.columns`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.columns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

State is Fin 4672. The first 64 states are (8,8,a,b), the next 512 are (8,a,b,c), and the final 4096 are (a,b,c,d), with real masks in lexicographic order. Real masks are 0 through 7; the absent symbol is 8.

**Definition 1.19 (Append one real mask).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.append`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.append` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Append drops the first symbol, appends the supplied real mask, and encodes the resulting four columns in the next appropriate state block.

**Theorem 1.20 (Literal column shift).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.columns_append`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.columns_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every state s, real mask m and i in Fin 4, the i-th column of append s m is the (i+1)-th column of s when i<3, and is m when i=3. This includes all three state blocks.

**Definition 1.21 (Exact binary masks).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.maskEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.maskEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positional-base equivalence finFunctionFinEquiv, composed with finTwoEquiv at every row, identifies all Fin 8 masks with Fin 3 → Bool.

**Theorem 1.22 (Little-endian row bits).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.maskEquiv_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.maskEquiv_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m in Fin 8 and row r in Fin 3, maskEquiv m r is exactly Nat.testBit m.val r.val. All 24 entries are kernel checked.

**Definition 1.23 (Present and absent symbols).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.symbol`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.symbol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An absent Option mask is encoded by 8. A present mask is encoded by its inverse under maskEquiv and therefore has value less than 8, including the present empty mask 0.

**Definition 1.24 (Actual signed column coordinates).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.paddedWindow`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.paddedWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every actual word w of width n and real centre c, the five symbols encode the padded columns c+i−2 for i in Fin 5.

**Definition 1.25 (Existing vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.present`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.present` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex exists in the five-column window exactly when its column symbol is less than 8. The real empty symbol 0 still has all three vertices.

**Definition 1.26 (Selected vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.selected`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.selected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex is selected exactly when it exists and the corresponding row bit in its column symbol is set. An absent symbol never selects a vertex.

**Definition 1.27 (Boolean witness existence).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.Local`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.Local` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each of the three middle-column vertices has a selected closed neighbour. Every selected middle vertex has an existing closed-neighbour witness whose selected closed neighbourhood contains only that vertex. Candidate witnesses and selected vertices exclude absent columns. Witnesses are existential propositions and are not path choices.

**Theorem 1.28 (Exact finite-window fidelity).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.local_paddedWindow_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.local_paddedWindow_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every width n, word w and actual centre c, Local (paddedWindow w c) is equivalent to ColumnTest (decode w) c. Signed-coordinate transport preserves every existing selected vertex, Manhattan distance, witness existence and uniqueness, including both open ends.

**Theorem 1.29 (Every real centre).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.validWord_iff_local`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.validWord_iff_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every width n and word w, ValidWord w is equivalent to Local (paddedWindow w c) at every c in Fin n. This follows through the actual-grid column criterion.

**Definition 1.30 (Executable accepted words).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.acceptedWords`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.acceptedWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite family filters every numeric Fin n → Fin 8 word by the exact Local test at all padded real centres.

**Theorem 1.31 (Actual subset cardinality).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_eq_acceptedWords`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_eq_acceptedWords` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every width n, actualCount n equals the cardinality of acceptedWords n. The proof composes the actual subset-word equivalence with the pinned numeric mask equivalence and the all-width local fidelity theorem.

**Theorem 1.32 (The original first coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual width-one minimal dominating subset count is exactly 2. The proof transports to all eight numeric masks and checks the actual local predicate; the two subsets are the middle singleton and the pair of ends.

**Definition 1.33 (The executable finite predicate).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.accepts`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.accepts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

accepts is the Boolean decision of Local over the finite five-column vertex domain.

**Definition 1.34 (Append a fifth symbol).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.window`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.window` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four state columns followed by the supplied symbol form the tested window.

**Definition 1.35 (Both open-end checks).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.terminal`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A terminal state must accept its four columns followed by 8, and must also accept its last three columns followed by 8,8. These check the final two real columns.

**Definition 1.36 (Backward transfer).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.fullStep`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.fullStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every integer state vector v and full state s, fullStep v s sums v(append s m) over precisely the accepted real masks m. Each mask contributes once.

**Definition 1.37 (All-length backward orbit).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.fullOrbit`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.fullOrbit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

fullOrbit 0 is the full terminal vector and fullOrbit(k+1) is fullStep(fullOrbit k). This is defined independently of actualCount.

The full transfer sums contributions from accepted mask words. The two terminal tests enforce the same open boundaries as the actual graph. The all-length counting correspondence and the total quotient then connect these local predicates to the actual subset series.

**Definition 1.38 (runWeight).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.runWeight`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.runWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An appended-mask word receives the product of its accepted transition indicators and its full terminal weight. It is always zero or one.

**Theorem 1.39 (sum runWeight).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.sum_runWeight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.sum_runWeight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every suffix length k and every full state s, summing runWeight k s over every Fin k → Fin 8 word is exactly fullOrbit k s. The first-mask function equivalence supplies the induction.

**Definition 1.40 (expanded).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.expanded`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.expanded` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Signed coordinates −2,−1,0,1 read the four history columns; the supplied suffix supplies successive real masks, and subsequent columns are absent.

**Definition 1.41 (expandedWindow).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.expandedWindow`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.expandedWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The five symbols centred at a nonnegative coordinate are read from the history-and-suffix stream.

**Theorem 1.42 (runWeight iff tests).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.runWeight_iff_tests`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.runWeight_iff_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k, full state s and suffix w, runWeight k s w equals one exactly when every centre in Fin(k+2) satisfies the corresponding Local window test. The base k=0 is precisely the two terminal checks.

**Definition 1.43 (start).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.start`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.start` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two labelled real masks a,b encode the full start state 8*a+b in the first block.

**Theorem 1.44 (accepted cons iff).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.accepted_cons_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.accepted_cons_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every suffix length k, masks a,b and suffix w, the concatenated numeric word belongs to acceptedWords(k+2) exactly when its unique run from start a b has weight one.

**Theorem 1.45 (actualCount fullOrbit).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_fullOrbit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_fullOrbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k, the actual inclusion-minimal dominating subset count of the ordinary open grid of width k+2, cast to the integers, equals the sum of fullOrbit k over all 64 starts. This includes width two with no transitions.

The generic CycleItalianDominationRecurrence.sum_pathWeight sums arbitrary intermediate states between fixed endpoints u and v for n+1 edges. At a positive suffix length k its parameters would be the state type Fin 4672, the unit admitted-edge matrix M, and n=k−1, followed by a terminal-weighted endpoint sum and a mask-word correspondence. The argument here defines each continuation by append and identifies its weight with the actual local tests for every k, including zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.Closed`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.ClosedPrivate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.ColumnTest`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.Local`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.MinimalDominating`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.ValidWord`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.acceptedWords`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.accepted_cons_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.accepts`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_eq_acceptedWords`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_fullOrbit`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_one`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.append`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.columns`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.columns_append`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.decode`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.encode`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.expanded`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.expandedWindow`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.fullOrbit`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.fullStep`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.grid`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.local_paddedWindow_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.maskEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.maskEquiv_apply`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.mem_decode`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.minimalSets`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.minimalWordEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.minimal_iff_closed_private`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.minimal_iff_column_tests`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.padded`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.paddedWindow`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.present`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.runWeight`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.runWeight_iff_tests`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.selected`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.start`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.subsetWordEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.sum_runWeight`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.symbol`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.terminal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.validWord_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.validWord_iff_local`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.window`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination](TrapezohedralMinimalDomination.md)
