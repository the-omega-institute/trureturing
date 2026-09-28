# Exact Boolean Budgets at Low Cycle Rank

## Abstract

Connected partial Boolean tasks with cycle rank at most two have an exact uniform region of ordered message budgets.

**Definition 1.1 (Partial Boolean tables).**

Lean statement: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.Task`

*Formalization.* `D5/S3/Observer/Separation/BooleanLowCycleBudgets.Task` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary types X and Y, Task(X,Y) is the type of functions t:X -> Y -> Option(ZMod 2). Write mathbb B for ZMod 2, identified with the two bits 0 and 1; its addition is XOR. The legal domain D(t) consists exactly of the pairs (x,y) for which t(x,y) is not none. If t(x,y)=some(c), the required output on that pair is c. The value none means that the pair is illegal and imposes no output condition. It is not a third output. The classification below ranges over all finite X and Y and every such partial table.

**Definition 1.2 (Support with distinct input sides).**

Lean statement: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.support`

*Formalization.* `D5/S3/Observer/Separation/BooleanLowCycleBudgets.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph support(t) has vertex type X disjoint-union Y. Its only edges join inl(x) to inr(y), and such an edge exists exactly when (x,y) belongs to D(t). Adjacency is symmetric, with no edges inside either side and no loops. Thus legal pairs correspond bijectively to its unordered edges, even when X and Y have common underlying values.

**Definition 1.3 (Original left conflicts).**

Lean statement: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.conflictLeft`

*Formalization.* `D5/S3/Observer/Separation/BooleanLowCycleBudgets.conflictLeft` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph conflictLeft(t) has vertices X. Two vertices x and u are adjacent exactly when there exist y in Y and bits c,d with t(x,y)=some(c), t(u,y)=some(d), and c different from d. Both pairs must be legal and the same y must occur in them. These conditions already exclude loops. Every correct left encoder separates adjacent vertices.

**Definition 1.4 (Original right conflicts).**

Lean statement: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.conflictRight`

*Formalization.* `D5/S3/Observer/Separation/BooleanLowCycleBudgets.conflictRight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph conflictRight(t) is conflictLeft of the transposed table. Its vertices y and v are adjacent exactly when there exist x in X and distinct bits c,d with t(x,y)=some(c) and t(x,v)=some(d). Both conflict graphs use the original table, including all edges attached to a cycle. They are not recomputed from a smaller graph when edges are removed.

**Definition 1.5 (Deterministic simultaneous messages).**

Lean statement: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.HasBudget`

*Formalization.* `D5/S3/Observer/Separation/BooleanLowCycleBudgets.HasBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a table t and natural numbers p,q, HasBudget(t,p,q) means that there exist arbitrary message types A,B, maps alpha:X->A and beta:Y->B, and a total decoder delta:A->B->mathbb B. The natural cardinalities of the ranges of alpha and beta are at most p and q respectively. For every x in X, every y in Y, and every bit c, t(x,y)=some(c) implies delta(alpha(x),beta(y))=c.

In the finite input setting both ranges are finite even if A or B is infinite. Only these reachable ranges are charged. Alice sees x alone, Bob sees y alone, and the decoder sees only their two messages. Correctness is required only on D(t); other message pairs may receive arbitrary Boolean values. There is no requirement to detect illegal inputs. Budgets are ordered upper bounds on symbol counts.

For finite X,Y this definition is equivalent, for every p,q, to the existence of alpha:X->Fin p, beta:Y->Fin q and delta:Fin p->Fin q->mathbb B satisfying the same legal-pair equation. Embed each finite reachable range into its Fin alphabet. On pairs of embedded messages reconstruct the original messages and apply the original decoder; elsewhere choose zero. Injectivity makes reconstruction independent of the chosen preimages. Conversely, ranges inside Fin p and Fin q have at most p and q elements. This equivalence does not restrict the original message types.

**Definition 1.6 (The full class at a given cycle-rank bound).**

Lean statement: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.InClass`

*Formalization.* `D5/S3/Observer/Separation/BooleanLowCycleBudgets.InClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite types X,Y, a table t and a natural number s, InClass(t,s) requires all of the following. For every x there exist y and c with t(x,y)=some(c), and for every y there exist x and c with t(x,y)=some(c). At least one legal pair exists. The support is connected. Each of the two original conflict graphs has chromatic number at most two. Finally, the integer cycle-rank expression below is at most s. Thus X and Y are precisely the nonempty active input sets; no size bound on either set is imposed.

$mu(t) = \lvert D(t) \rvert + 1 - \lvert X \rvert - \lvert Y \rvert \leq s, mu(t) \in \mathbb{Z}$

Every cardinality in this expression is coerced to the integers before subtraction. In particular, neither subtraction is truncated at zero. The chromatic bounds also express the original one-sided message costs: a correct encoder is a proper coloring, while a proper coloring gives a decoder by taking the common output at a fixed opposite input and color. Empty entries of that response table can be filled arbitrarily.

**Definition 1.7 (A guarantee for every task in the class).**

Lean statement: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.UniformBudget`

*Formalization.* `D5/S3/Observer/Separation/BooleanLowCycleBudgets.UniformBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural s,p,q, UniformBudget(s,p,q) means: for every type X with a finite enumeration, every type Y with a finite enumeration, and every t:Task(X,Y), InClass(t,s) implies HasBudget(t,p,q). The existential choice of alphabets, encoders and decoder occurs separately for each table after these universal quantifiers. Different tasks need not share a decoder. A particular task may admit smaller budgets than this guarantee for the whole class.

**Definition 1.8 (Labels on unordered edges).**

Lean statement: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.edgeValue`

*Formalization.* `D5/S3/Observer/Separation/BooleanLowCycleBudgets.edgeValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every unordered pair e of vertices in X disjoint-union Y, edgeValue(t,e) is the bit c if e joins x and y with t(x,y)=some(c), in either endpoint order. It is zero for illegal cross pairs and pairs within one side. The cycle arguments evaluate it only on edges of support subgraphs, where it agrees exactly with the original required output.

**Theorem 1.9 (Exact ordered budgets for cycle ranks zero, one and two).**

$$\forall s , p , q \in \mathbb{N}, (s \leq 2 \land 0 < p \land 0 < q) \implies (UniformBudget(s , p , q) \Leftrightarrow (2 \leq p \land 2 \leq q \land s + 4 \leq p + q))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/BooleanLowCycleBudgets.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural s at most two and every pair of positive natural numbers p,q, the displayed equivalence gives the entire uniform budget region. Its minimal ordered pairs are (2,2) when s=0; (2,3) and (3,2) when s=1; and (2,4), (3,3) and (4,2) when s=2. Every coordinatewise larger pair belongs to the same region.

Write G for the support and V for its full vertex set. The binary graph cycle-space theorem identifies its dimension with |E(G)|-|V|+k(G), where k counts connected components including isolated vertices. The legal-edge bijection and connectedness give dimension at most s. For any support subgraph H, all simple cycles have label XOR zero exactly when there is a potential h:V->mathbb B whose endpoint sums equal the edge labels. This applies component by component, with an independent root bit in each component and a free bit at every isolated vertex. A spanning forest constructs the potentials by path XOR; the remaining edges agree by their fundamental cycles.

Fix proper Boolean colorings cx and cy of the original left and right conflict graphs. Define a completed two-bit response rx(x) on the colors of cy, and ry(y) on the colors of cx. Properness makes each occupied entry single-valued, and empty entries are assigned zero. Sending cx(x) and ry(y), with decoding by evaluation, gives (2,4). Sending rx(x) and cy(y) gives (4,2). These constructions work at every cycle rank.

Every two-bit Boolean response is either constant or has the form j |-> r(0)+j. A constant rx(x) makes x monochromatic on all of its original legal edges; a nonconstant rx(x) satisfies f(x,y)=rx(x)(0)+cy(y) on every original legal edge. The analogous statement holds for ry(y). If a cycle has nonzero label XOR, its labels cannot all agree with the endpoint sums of the potential formed from rx(x)(0) and cy(y). An edge of disagreement therefore has an endpoint x with constant rx(x). Using cx(x) and ry(y)(0) gives such a y as well. Hence any nonzero-XOR cycle in any support subgraph contains a selectable vertex on either specified side that is monochromatic in the original table, including its attached edges.

All cycle spaces can be compared inside the fixed space of Boolean functions on E(G): let K(H) be the span of the edge indicator vectors of simple cycles in H. Removing every edge incident to a chosen vertex a gives a subgraph cut(H,a), so K(cut(H,a)) is contained in K(H). If a lies on a cycle, select one incident cycle edge e. Every vector in K(cut(H,a)) has zero e-coordinate, while that cycle's indicator has e-coordinate one. The inclusion is therefore strict and the dimension strictly decreases. Dimension zero precludes a cycle, since any cycle has a nonzero edge indicator. The vertex type remains V throughout: isolated surviving vertices, and even the selected vertices now made isolated, remain present. No connectedness assumption is made on a residual graph.

Once the residual graph is balanced, its unselected vertices send their potential bits. There is at most one selected x and at most one selected y in this construction. Each selected vertex sends its own special symbol, using alphabets mathbb B disjoint-union the selected singleton or empty set on the respective side. Two ordinary symbols decode by XOR. An Alice special symbol decodes to her original monochromatic bit; otherwise a Bob special symbol decodes to his bit. If both endpoints of a legal edge were selected, their original bits equal that edge's output, so the priority given to Alice is consistent. Distinct special bits cannot be joined by a legal edge. This defines actual total encoders and decoder with at most two ordinary symbols plus one selected symbol on each side.

At rank zero the support is already balanced, giving (2,2). At rank at most one, one deletion on either specified side, if needed, leaves dimension zero and gives (3,2) or (2,3). At rank at most two, first select an Alice vertex on a nonzero-XOR cycle. If the residual graph is still unbalanced, select a Bob vertex on a residual nonzero-XOR cycle. Two strict dimension decreases leave dimension zero, giving (3,3). Together with the response-table endpoints and monotonicity of upper budgets, these protocols give every pair in the stated region.

Necessity uses the following actual partial tables. Rows and columns are indexed from zero, and each star denotes an illegal pair, not an output.

$\begin{gathered}F_{0} = \begin{pmatrix}0 & * \\ 1 & 0\end{pmatrix} \\ F_{1} = \begin{pmatrix}* & * & 0 \\ 0 & 1 & 1 \\ 1 & 1 & *\end{pmatrix} \\ F_{2} = \begin{pmatrix}0 & 0 & * & * \\ 0 & 1 & * & * \\ * & * & 0 & 1 \\ * & * & 1 & 1 \\ * & 0 & 1 & *\end{pmatrix}\end{gathered}$

F0 has three edges and four active vertices, connected support of rank zero, and one conflict edge on each side. Its entries at (0,0) and (1,0) force two Alice messages; those at (1,0) and (1,1) force two Bob messages. It belongs to every class under consideration, so p and q must both be at least two.

F1 has six edges and six active vertices, connected support of rank one, and conflict colorings 010 and 011. A (2,2) protocol would force equal Alice messages at rows 0 and 2 and equal Bob messages at columns 1 and 2. The legal pairs (0,2) and (2,1) would then have identical message pairs but outputs zero and one. Thus (2,2) is impossible at rank one.

F2 has ten edges and nine active vertices. Its support is two four-cycles joined through row 4 and has rank two. Its conflict graphs are the paths 0-1-4-2-3 on rows and 0-1-2-3 on columns, with colorings 01100 and 0101. With two Alice messages, the row classes are {0,3,4} and {1,2}; the four columns have respective responses 00,01,10,11, each coordinate determined by a legal pair. Equal Bob messages for any two columns would cause a legal output collision, so four Bob messages are required. With two Bob messages, the column classes are {0,2} and {1,3}; the five row responses are 00,01,01,11,10. All four distinct responses occur, requiring four Alice messages. This excludes both (2,3) and (3,2). The finite-image equivalence makes these arguments apply to arbitrary message alphabets. Along with F0 and F1, they exclude every positive ordered pair outside the stated uniform region.

## References

- Truth anchor: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.HasBudget`
- Truth anchor: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.InClass`
- Truth anchor: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.Task`
- Truth anchor: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.UniformBudget`
- Truth anchor: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.conflictLeft`
- Truth anchor: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.conflictRight`
- Truth anchor: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.edgeValue`
- Truth anchor: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.result`
- Truth anchor: `D5/S3/Observer/Separation/BooleanLowCycleBudgets.support`
- Dependency: [D5/S3/Fourier/CharacterSelection/SimpleGraphCycleSpace](../../Fourier/CharacterSelection/SimpleGraphCycleSpace.md)
