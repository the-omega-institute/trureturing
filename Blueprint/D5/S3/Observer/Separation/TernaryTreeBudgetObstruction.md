# A Ternary Tree Obstruction to Two Messages per Side

## Abstract

A ternary partial table has tree support and exact one-sided costs two, yet no deterministic simultaneous protocol can use at most two reachable messages on each side.

**Definition 1.1 (Partial ternary tasks).**

Lean statement: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.Task`

*Formalization.* `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.Task` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary types X and Y, Task(X,Y) is X -> Y -> Option(Fin 3). The output type O = Fin 3 consists of 0, 1, 2. A value some(o) prescribes output o; none marks an illegal input pair and is not an output. Write D(t) for the set of pairs (x,y) with t(x,y) different from none, and write t transpose for the table (y,x) |-> t(x,y).

**Definition 1.2 (The actual table).**

$$F=\begin{pmatrix}0&*&*\\1&0&*\\*&1&2\end{pmatrix}$$

*Formalization.* `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.table` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here X = Y = O = Fin 3, and F denotes table. Rows and columns are ordered 0,1,2. An asterisk denotes none; each numeral denotes some of that output. The five legal entries are F(0,0)=0, F(1,0)=1, F(1,1)=0, F(2,1)=1, F(2,2)=2. All three output labels occur, and every row and column is active.

**Definition 1.3 (The actual simple bipartite support).**

Lean statement: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.support`

*Formalization.* `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertices of support(t) are the disjoint union X + Y. Its adjacency relates inl(x) and inr(y), in either order, exactly when t(x,y) is not none. There are no edges within either side and no loops. Thus each legal pair gives one unordered simple edge. Below G means support(F), E(G) its unordered edge set, and V its full vertex type Fin 3 + Fin 3.

**Definition 1.4 (Original row conflicts).**

Lean statement: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.conflictLeft`

*Formalization.* `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.conflictLeft` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vertices x and u in conflictLeft(t) are adjacent exactly when there exist y in Y and a,b in O such that t(x,y)=some(a), t(u,y)=some(b), and a differs from b. The shared column and both legal entries belong to the original table. Write GA for conflictLeft(F).

**Definition 1.5 (Original column conflicts).**

Lean statement: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.conflictRight`

*Formalization.* `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.conflictRight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

conflictRight(t) is conflictLeft(t transpose). Thus y and v are adjacent exactly when one original row x has two legal entries t(x,y)=some(a) and t(x,v)=some(b) with a different from b. Write GB for conflictRight(F).

**Definition 1.6 (All ambient simultaneous protocols).**

$$\operatorname{HasBudget}\left(t, p, q\right) \Leftrightarrow (\exists A \in \operatorname{Type},\; \exists B \in \operatorname{Type},\; \exists \alpha:X \to A, \exists \beta:Y \to B, \exists \delta:A \to \left(B \to O\right), (\left(|\operatorname{range}\left(\alpha\right)| \le p \land |\operatorname{range}\left(\beta\right)| \le q\right) \land \left(\forall x \in X,\; \forall y \in Y,\; \forall o \in O,\; t\left(x, y\right) = \operatorname{some}\left(o\right) \Rightarrow \delta\left(\alpha\left(x\right), \beta\left(y\right)\right) = o\right)))$$

*Formalization.* `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.HasBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural p,q, HasBudget(t,p,q) quantifies over arbitrary ambient types A,B, separate encoders alpha:X->A and beta:Y->B, and a total decoder delta:A->B->O. Neither alphabet is required to be finite. The charged quantities are Nat.card(Set.range alpha) and Nat.card(Set.range beta). For this table both ranges are finite because the inputs are finite, even when the ambient alphabets are infinite. The vertical bars in the displayed definitions denote these natural cardinalities. Correctness is required for every x,y,o with t(x,y)=some(o), and imposes no condition on illegal pairs. The decoder receives only the two messages. The ordered budgets count reachable symbols.

**Definition 1.7 (The original one-sided budget).**

$$\operatorname{HasOriginalBudget}\left(t, p\right) \Leftrightarrow (\exists A \in \operatorname{Type},\; \exists \alpha:X \to A, \exists \delta:A \to \left(Y \to O\right), (|\operatorname{range}\left(\alpha\right)| \le p \land \left(\forall x \in X,\; \forall y \in Y,\; \forall o \in O,\; t\left(x, y\right) = \operatorname{some}\left(o\right) \Rightarrow \delta\left(\alpha\left(x\right), y\right) = o\right)))$$

*Formalization.* `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.HasOriginalBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

HasOriginalBudget(t,p) quantifies over an arbitrary ambient type A, an encoder alpha:X->A and a total decoder d:A->Y->O. At most p values of alpha are reachable, and d(alpha(x),y)=o for every legal entry t(x,y)=some(o). This decoder retains the other party's original input y. Transposing t gives the corresponding right-sided definition.

**Definition 1.8 (Exact original input costs).**

$$\operatorname{originalCost}\left(t\right) = \operatorname{sInf}\left(\{p:\mathbb{N}\mid \operatorname{HasOriginalBudget}\left(t, p\right)\}\right)$$

*Formalization.* `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.originalCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

originalCost(t) is the infimum in the natural numbers of the budgets p satisfying HasOriginalBudget(t,p). For F and its transpose the proof exhibits budget two and proves that every feasible budget is at least two; the infimum is therefore an attained minimum. These are actual one-sided protocol costs, as well as the chromatic numbers computed below.

**Definition 1.9 (The six-vertex path order).**

$$\operatorname{pathIndex}\left(\operatorname{inl}\left(i\right)\right)=2i,\quad \operatorname{pathIndex}\left(\operatorname{inr}\left(j\right)\right)=2j+1$$

*Formalization.* `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.pathIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

pathIndex sends inl(0), inr(0), inl(1), inr(1), inl(2), inr(2) to 0,1,2,3,4,5 respectively in Fin 6. Hence its path order is exactly x0-y0-x1-y1-x2-y2.

**Definition 1.10 (The complete seventeen-clause positive certificate).**

Lean statement: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.ActualProperties`

*Formalization.* `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.ActualProperties` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ActualProperties is the conjunction of the following seventeen clauses, in this order. Every clause concerns the same table F. Cardinalities are finite; the rank expression is evaluated in the integers.

1. The output type Fin 3 has cardinality 3.

2. For every o in Fin 3, there exist x,y in Fin 3 with F(x,y)=some(o).

3. For every x in Fin 3, there exist y,o in Fin 3 with F(x,y)=some(o).

4. For every y in Fin 3, there exist x,o in Fin 3 with F(x,y)=some(o).

5. The set D(F) of legal input pairs has cardinality 5.

6. The actual unordered simple edge set E(G) has cardinality 5.

7. The full vertex type V = Fin 3 + Fin 3 has cardinality 6; clauses 3 and 4 make all six vertices active.

8. pathIndex:V->Fin 6 is bijective.

9. For every v,w in V, G.Adj(v,w) holds if and only if pathIndex(v).val+1=pathIndex(w).val or pathIndex(w).val+1=pathIndex(v).val.

10. G is a tree: it is connected and acyclic.

11. The integer expression |D(F)|-|Fin 3|-|Fin 3|+1 equals 0. This is 5-3-3+1, without truncated natural subtraction.

12. GA equals pathGraph 3, with exactly the edges 0-1 and 1-2.

13. GB equals pathGraph 3, with exactly the edges 0-1 and 1-2.

14. The chromatic number of GA equals 2.

15. The chromatic number of GB equals 2.

16. originalCost(F) equals 2.

17. originalCost(F transpose) equals 2.

**Definition 1.11 (The proposed ternary implication).**

$$\operatorname{claim} \Leftrightarrow (\operatorname{ActualProperties} \Rightarrow \operatorname{HasBudget}\left(F, 2, 2\right))$$

*Formalization.* `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

claim is the closed proposition ActualProperties implies HasBudget(F,2,2). The antecedent contains all seventeen positive properties. Its consequent asserts existence of a correct protocol over some arbitrary ambient alphabets, with at most two reachable messages on each side.

**Theorem 1.12 (The positive certificate holds and every two-by-two protocol fails).**

$$\neg (\operatorname{ActualProperties} \Rightarrow \operatorname{HasBudget}\left(F, 2, 2\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem is the negation of the entire proposed implication. Equivalently, ActualProperties holds and HasBudget(F,2,2) is false. The proof constructs every positive clause and excludes existence of any correct protocol, for all choices of A,B,alpha,beta,delta in the definition above.

Legal pairs map bijectively to unordered edges by (x,y) |-> {inl(x),inr(y)}. The five actual edges connect all six vertices in the stated order; connectedness and the edge count give a tree. Checking the original entries gives both exact conflict paths and hence both chromatic numbers two.

For each one-sided protocol use the encoder 010 into Fin 2. For F, the total decoder has rows (0,1,2) and (1,0,0), indexed by the message and columns indexed by the original y. For F transpose, the total decoder has rows (0,1,2) and (0,0,1), with columns indexed by the original x. All five required equations hold in each case. Conversely, the entries (0,0),(1,0) force two distinct left messages; the entries (1,0),(1,1) force two distinct right messages. Thus every one-sided budget is at least two, proving the exact minima.

Now suppose an arbitrary ambient protocol is correct on the five legal entries. The pairs (0,0),(1,0) force alpha(0) different from alpha(1), and (1,1),(2,1) force alpha(1) different from alpha(2). The pairs (1,0),(1,1) force beta(0) different from beta(1), and (2,1),(2,2) force beta(1) different from beta(2). If either encoder also separated its endpoints, it would be injective on Fin 3 and its reachable image would have cardinality three. The two-message bounds therefore force alpha(0)=alpha(2) and beta(0)=beta(2). The legal inputs (0,0) and (2,2) then give the same message pair, which the total decoder would have to send both to 0 and to 2. This contradiction applies to all ambient types, rather than only a fixed two-symbol decoder enumeration.

The conclusion concerns this three-output task. It shows that exact original costs two cannot replace the Boolean output hypothesis in a forest guarantee. The Boolean forest theorem remains valid; no conclusion about the unresolved uniform Boolean region at cycle rank three follows from this example.

## References

- Truth anchor: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.ActualProperties`
- Truth anchor: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.HasBudget`
- Truth anchor: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.HasOriginalBudget`
- Truth anchor: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.Task`
- Truth anchor: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.claim`
- Truth anchor: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.conflictLeft`
- Truth anchor: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.conflictRight`
- Truth anchor: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.originalCost`
- Truth anchor: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.pathIndex`
- Truth anchor: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.result`
- Truth anchor: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.support`
- Truth anchor: `D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.table`
