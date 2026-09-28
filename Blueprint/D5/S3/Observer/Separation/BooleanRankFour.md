# Boolean Tasks at Cyclomatic Rank Four

## Abstract

A Boolean task of cyclomatic rank four determines the exact ordered message budgets for every higher rank bound.

In the definitions, X and Y are arbitrary types, T is a task on X and Y, x,u range over X, y,v range over Y, p,q are natural numbers, and s is an integer. Boolean values 0 and 1 mean false and true. Finiteness of the input types is imposed in the uniform class below. Message alphabets may be arbitrary types. For finite inputs, budgets count distinct messages actually sent, and are upper bounds.

**Definition 1.1 (A partial Boolean task).**

$$\begin{gathered}\operatorname{Task}(X , Y) = X \to \left(Y \to \operatorname{Option}(\operatorname{Bool})\right) \\ \operatorname{D}(T) = \{(x , y) \mid x \in X,y \in Y,\exists c: \operatorname{Bool}, \operatorname{T}(x , y) = \operatorname{some}(c)\}\end{gathered}$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankFour.Task` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Task(X,Y) is the type X -> Y -> Option Bool. The value none means that the pair is illegal; some(c) means it is legal with output c. D(T) denotes the set of legal pairs. No condition is imposed on a protocol's answer at an illegal pair.

**Definition 1.2 (The original left conflict graph).**

$$\operatorname{Adj}(\operatorname{leftConflict}(T) , x , u) \iff \exists y: Y, \exists c,e: \operatorname{Bool}, \operatorname{T}(x , y) = \operatorname{some}(c) \land \operatorname{T}(u , y) = \operatorname{some}(e) \land c \neq e$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankFour.leftConflict` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertices are X. Two rows are adjacent exactly when one common column is legal in both and has different Boolean outputs. This symmetric, loopless graph depends only on the original task.

**Definition 1.3 (The original right conflict graph).**

$$\operatorname{Adj}(\operatorname{rightConflict}(T) , y , v) \iff \exists x: X, \exists c,e: \operatorname{Bool}, \operatorname{T}(x , y) = \operatorname{some}(c) \land \operatorname{T}(x , v) = \operatorname{some}(e) \land c \neq e$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankFour.rightConflict` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertices are Y. Two columns conflict when a common legal row gives different outputs. Equivalently, this is the left conflict graph of the transposed task. Both chromatic hypotheses below refer to these original graphs, before any messages are chosen.

**Definition 1.4 (The bipartite support).**

$$\operatorname{support}(T) = (\operatorname{Sum}(X , Y) , \{\{\operatorname{inl}(x) , \operatorname{inr}(y)\} \mid (x , y) \in \operatorname{D}(T)\})$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankFour.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertex set is the disjoint union X plus Y. An undirected edge joins inl(x) to inr(y) precisely when (x,y) is legal. There are no edges within either side; the Boolean label does not affect support.

**Definition 1.5 (All inputs active, with nonempty connected support).**

$$\operatorname{ActiveConnected}(T) \iff \operatorname{Nonempty}(\operatorname{D}(T)) \land (\forall x: X, \exists y: Y, (x , y) \in \operatorname{D}(T)) \land (\forall y: Y, \exists x: X, (x , y) \in \operatorname{D}(T)) \land \operatorname{Connected}(\operatorname{support}(T))$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankFour.ActiveConnected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At least one legal pair exists, every x has a legal partner, every y has a legal partner, and the support graph is connected. Thus both input types are nonempty and contain exactly active inputs.

**Definition 1.6 (Integer cyclomatic rank).**

$$\operatorname{cycleRank}(T)=\operatorname{NatCard}(\operatorname{D}(T))-\operatorname{NatCard}(X)-\operatorname{NatCard}(Y)+1\in\mathbb{Z}$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankFour.cycleRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NatCard denotes Nat.card: the finite cardinality of a type, and zero for an infinite type. Each cardinality is coerced to the integers before subtraction. For finite active connected support this is the cyclomatic number |D(T)|-|X|-|Y|+1; subtraction is not truncated at zero.

**Definition 1.7 (Reachable message budgets and a total decoder).**

$$\operatorname{Admits}(T , p , q) \iff \exists A,B: \operatorname{Type}, \exists a: X \to A, \exists b: Y \to B, \exists d: A \to \left(B \to \operatorname{Bool}\right), \operatorname{NatCard}(\operatorname{range}(a)) \leq p \land \operatorname{NatCard}(\operatorname{range}(b)) \leq q \land (\forall x: X, \forall y: Y, \forall c: \operatorname{Bool}, \operatorname{T}(x , y) = \operatorname{some}(c) \implies \operatorname{d}(\operatorname{a}(x) , \operatorname{b}(y)) = c)$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankFour.Admits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There exist arbitrary types A and B, encoders a:X->A and b:Y->B, and a total decoder d:A->B->Bool. Only Nat.card(range(a)) and Nat.card(range(b)) are charged. For every x, y and Boolean c, T(x,y)=some(c) requires d(a(x),b(y))=c. The decoder is defined even on unreachable message pairs. Neither encoder must be surjective onto its ambient alphabet. With finite inputs, both reachable images are finite even if A or B is infinite.

**Definition 1.8 (The ordered budget region).**

$$\operatorname{Region}(p , q) \iff 2 \leq p \land 2 \leq q \land 4 \leq \operatorname{max}(p , q)$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankFour.Region` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Alice has budget p and Bob has budget q. Each budget is at least two and at least one is at least four. Equivalently, this is the union of p>=2,q>=4 and p>=4,q>=2.

**Definition 1.9 (A uniform bound over all finite input types).**

$$\operatorname{Uniform}(s , p , q) \iff \forall X,Y: \operatorname{Type}, \operatorname{Fintype}(X) \land \operatorname{Fintype}(Y) \implies \forall T: \operatorname{Task}(X , Y), (\operatorname{ActiveConnected}(T) \land \operatorname{cycleRank}(T) \leq s \land \operatorname{chromaticNumber}(\operatorname{leftConflict}(T)) \leq 2 \land \operatorname{chromaticNumber}(\operatorname{rightConflict}(T)) \leq 2) \implies \operatorname{Admits}(T , p , q)$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankFour.Uniform` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every pair of types X,Y with finite enumerations, and every task on them, assume ActiveConnected(T), cycleRank(T)<=s, and chromatic number at most two for each original conflict graph. Uniform(s,p,q) requires Admits(T,p,q) for every such task. The alphabets, encoders and decoder may be chosen separately for each task. The chromatic bounds permit one used color and unused colors; they do not require chromatic number exactly two.

**Definition 1.10 (The six by five task).**

$$\begin{gathered}F_{4}:\operatorname{Task}(\operatorname{Fin}(6) , \operatorname{Fin}(5)) \\ F_{4} = \begin{pmatrix}1 & - & 0 & - & - \\ - & 0 & - & 1 & 1 \\ 1 & - & - & 1 & - \\ 0 & - & - & 0 & - \\ - & 1 & 0 & 0 & - \\ 0 & - & - & - & 1\end{pmatrix}\end{gathered}$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankFour.F4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rows are indexed 0 through 5 and columns 0 through 4. A dash denotes none; 0 and 1 denote some(false) and some(true). The six rows have respectively 2,3,2,2,3,2 legal entries, so there are fourteen support edges on eleven vertices.

**Theorem 1.11 (Exact individual and uniform regions).**

$$\begin{gathered}\operatorname{ActiveConnected}(F_{4}) \land \operatorname{cycleRank}(F_{4}) = 4 \\ \land \operatorname{chromaticNumber}(\operatorname{leftConflict}(F_{4})) = 2 \land \operatorname{chromaticNumber}(\operatorname{rightConflict}(F_{4})) = 2 \\ \land (\forall p,q: \mathbb{N}, \operatorname{Admits}(F_{4} , p , q) \iff \operatorname{Region}(p , q)) \\ \land (\forall s: \mathbb{Z}, 4 \leq s \implies \forall p,q: \mathbb{N}, \operatorname{Uniform}(s , p , q) \iff \operatorname{Region}(p , q))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/BooleanRankFour.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The six conclusions hold together: F4 is active and connected, its integer cycle rank is four, each original conflict graph has chromatic number exactly two, its individual region is Region(p,q) for every natural p,q, and the same equivalence holds uniformly for every integer s>=4 and every natural p,q.

For the upper bound, take any finite task whose left conflict graph has a coloring a:X->Fin 2. For each y and color i, set b(y)(i) to the common output among legal rows of color i in column y, or to false when there is no such row. Two different outputs in one color would contradict proper coloring. The actual message alphabets are Fin 2 and Fin 2->Bool, with decoder d(i,t)=t(i). They have respectively two and four elements, so their reachable images give (2,4). Transposing the task gives (4,2). Enlarging either budget gives every point in Region.

An entirely unused color, or a color absent from a particular column, simply receives the default false coordinate. A one-color task is included; neither endpoint requires both colors or all four response words to occur. This construction also permits empty input types, although ActiveConnected excludes them from the uniform class. It uses no rank bound.

For F4, proper left and right colorings are (0,0,0,1,1,1) and (0,0,1,1,1). Rows 0 and 3 conflict at column 0, and columns 0 and 2 conflict at row 0, so both chromatic numbers are exactly two. Every vertex is active. Starting at column 0 reaches rows 0,2,3,5; row 2 reaches column 3, which reaches rows 1,4. Rows 1 and 0 reach all remaining columns. The support is connected, and its rank is 14-6-5+1=4.

For any finite input type and encoder a with at most k reachable messages, inject the finite type range(a) into Fin k and compose with x mapping to a(x) in that range. The resulting encoder a' satisfies a'(x)=a'(u) exactly when a(x)=a(u). This relabels only the reachable image; it puts no finiteness condition on the ambient alphabet and preserves every message collision.

Correctness forces each encoder to separate adjacent vertices of its original conflict graph: a shared message at two opposite legal outputs would give the same decoder input two values. Relabeling therefore gives p>=2 and q>=2 for F4. To rule out both budgets at most three, relabel both reachable images into Fin 3. The complete list of left conflict edges is (0,3),(0,5),(1,3),(1,4),(2,3), (2,4),(2,5). Up to equality of color classes, every proper map of the six rows into Fin 3 is one of the nine rows below. In each row the first tuple is the normalized Alice partition P_k and the second is an ordered tuple C_k of four distinct Bob columns; k runs from 0 to 8.

$\begin{pmatrix}(0 , 0 , 0 , 1 , 1 , 1) & (0 , 1 , 2 , 4) \\ (0 , 0 , 0 , 1 , 1 , 2) & (0 , 1 , 2 , 4) \\ (0 , 0 , 0 , 1 , 2 , 1) & (0 , 1 , 2 , 4) \\ (0 , 0 , 0 , 1 , 2 , 2) & (0 , 1 , 2 , 4) \\ (0 , 0 , 1 , 2 , 2 , 2) & (0 , 1 , 2 , 4) \\ (0 , 1 , 0 , 2 , 2 , 2) & (0 , 1 , 2 , 4) \\ (0 , 1 , 1 , 2 , 2 , 2) & (0 , 1 , 2 , 4) \\ (0 , 1 , 0 , 2 , 2 , 1) & (0 , 1 , 2 , 3) \\ (0 , 1 , 1 , 2 , 0 , 2) & (0 , 1 , 3 , 4)\end{pmatrix}$

Normalization labels classes in order of first occurrence, without changing which rows have equal messages. The nine tuples exhaust the equality partitions of assignments of six labels in Fin 3 satisfying those seven inequalities. For each k, the following six entries give row pairs (i,t), in the column position order (0,1),(0,2),(0,3),(1,2),(1,3),(2,3). An entry at positions (j,l) has P_k(i)=P_k(t), with F4(i,C_k(j)) and F4(t,C_k(l)) both legal and opposite. Thus the table supplies all 9 times 6 = 54 witnesses.

$\begin{pmatrix}(0 , 1) & (0 , 0) & (3 , 5) & (4 , 4) & (1 , 1) & (0 , 1) \\ (0 , 1) & (0 , 0) & (5 , 5) & (4 , 4) & (1 , 1) & (0 , 1) \\ (0 , 1) & (0 , 0) & (3 , 5) & (4 , 4) & (1 , 1) & (0 , 1) \\ (0 , 1) & (0 , 0) & (5 , 5) & (4 , 4) & (1 , 1) & (0 , 1) \\ (0 , 1) & (0 , 0) & (3 , 5) & (4 , 4) & (1 , 1) & (0 , 1) \\ (3 , 4) & (0 , 0) & (3 , 5) & (4 , 4) & (1 , 1) & (4 , 5) \\ (2 , 1) & (0 , 0) & (3 , 5) & (4 , 4) & (1 , 1) & (4 , 5) \\ (3 , 4) & (0 , 0) & (5 , 1) & (4 , 4) & (1 , 1) & (0 , 2) \\ (2 , 1) & (0 , 4) & (3 , 5) & (1 , 1) & (1 , 1) & (3 , 5)\end{pmatrix}$

Fix k and any two distinct selected columns. If Bob gave them the same message, their displayed row pair would also have equal Alice messages. For their opposite legal values c and e, correctness would force the equality below. This is impossible for any decoder. The reverse column order uses the reversed row pair.

$c = \operatorname{d}(\operatorname{a}(i) , \operatorname{b}(C_{k}(j))) = \operatorname{d}(\operatorname{a}(t) , \operatorname{b}(C_{k}(l))) = e$

Consequently all four selected Bob columns require distinct messages: their induced incompatibilities form a K4 for this Alice partition. This K4 is distinct from the original right conflict graph, whose chromatic number is two. An injection from these four columns into Fin 3 is impossible. Hence max(p,q)>=4, completing the individual equivalence for all natural budgets, including zero and one. The boundary points (2,4) and (4,2) are feasible; (3,3) and all pairs with either budget below two are infeasible.

For every integer s>=4, this same F4 belongs to the entire class with cycleRank(T)<=s. Any uniform budget must therefore satisfy its individual lower bound. Conversely, the two response-word constructions work for every finite task with the two original chromatic bounds. This proves the full uniform equivalence without restricting input sizes or choosing only one endpoint orientation.

## References

- Truth anchor: `D5/S3/Observer/Separation/BooleanRankFour.ActiveConnected`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankFour.Admits`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankFour.F4`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankFour.Region`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankFour.Task`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankFour.Uniform`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankFour.cycleRank`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankFour.leftConflict`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankFour.result`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankFour.rightConflict`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankFour.support`
