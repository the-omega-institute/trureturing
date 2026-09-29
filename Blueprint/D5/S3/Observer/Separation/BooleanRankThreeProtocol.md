# A Rank-Three Protocol Beyond Balanced Deletion

## Abstract

A Boolean rank-three task admits three messages per side while all four whole-class deletions remain unbalanced.

**Definition 1.1 (The original partial Boolean table).**

$$F_{\theta}=\begin{pmatrix}0& 0& *& *& *& *\\ 1& 1& *& *& *& *\\ 1& *& 0& *& *& *\\ *& *& 0& 1& *& *\\ *& 1& *& 0& *& *\\ 0& *& *& *& 1& *\\ *& *& *& *& 1& 0\\ *& 0& *& *& *& 1\end{pmatrix}$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankThreeProtocol.Ftheta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let X={0,...,7}, Y={0,...,5}, and V=X disjoint union Y. A table F maps X times Y to Option Bool. A star is a missing, illegal pair, not a third output. The legal domain D consists exactly of pairs with an entry. The simple bipartite support G has vertex set V and one edge for each legal pair, with its original Boolean label.

**Definition 1.2 (Arbitrary alphabets and reachable messages).**

$$Protocol(F, p, q, \alpha, \beta, \delta)\Leftrightarrow \lvert \alpha(X)\rvert\leq p\land \lvert \beta(Y)\rvert\leq q\land \forall (x,y)\in D,\delta(\alpha(x), \beta(y))=f(x, y)$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankThreeProtocol.Protocol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary types A and B with decidable equality, alpha:X to A and beta:Y to B are total encoders and delta:A to B to Bool is a total decoder. A and B may be infinite. Only their finite reachable images are charged. Correctness is required exactly on legal pairs; decoder values at unreachable message pairs are unrestricted.

**Definition 1.3 (The explicit three-message protocol).**

$$\begin{gathered}\alpha=(0, 1, 1, 0, 1, 0, 0, 2)\\ \beta=(0, 0, 1, 2, 2, 1)\\ \delta=\begin{pmatrix}0& 0& 1\\ 1& 0& 0\\ 0& 1& 0\end{pmatrix}\end{gathered}$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankThreeProtocol.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here A=B=Nat. The encoder strings, in increasing input order, are 01101002 and 001221. The displayed decoder rows are 001, 100 and 010, indexed by messages 0,1,2. All other ambient message pairs have decoder value false. Each encoder reaches exactly the three symbols 0,1,2. The following sixteen rows list (input pair, message pair, decoded bit, target bit); they exhaust the original legal domain.

$\begin{gathered}(0,0); (0,0); 0; 0\\ (0,1); (0,0); 0; 0\\ (1,0); (1,0); 1; 1\\ (1,1); (1,0); 1; 1\\ (2,0); (1,0); 1; 1\\ (2,2); (1,1); 0; 0\\ (3,2); (0,1); 0; 0\\ (3,3); (0,2); 1; 1\\ (4,1); (1,0); 1; 1\\ (4,3); (1,2); 0; 0\\ (5,0); (0,0); 0; 0\\ (5,4); (0,2); 1; 1\\ (6,4); (0,2); 1; 1\\ (6,5); (0,1); 0; 0\\ (7,1); (2,0); 0; 0\\ (7,5); (2,1); 1; 1\end{gathered}$

**Definition 1.4 (Whole original monochromatic classes).**

$$\begin{gathered}M_{X}^{c}=\{x\in X\mid\forall y,(x,y)\in D\implies f(x, y)=c\}\\ M_{Y}^{d}=\{y\in Y\mid\forall x,(x,y)\in D\implies f(x, y)=d\}\\ H_{cd}=G[V\setminus (M_{X}^{c}\cup M_{Y}^{d})]\end{gathered}$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankThreeProtocol.residual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex belongs to M_X^c or M_Y^d precisely when every incident edge in the original legal domain has that bit. H_cd is the induced graph on all remaining vertices. Every surviving isolated vertex remains in its vertex set. Labels are restricted along this vertex inclusion; neither conflicts nor monochromatic classes are recomputed after deletion. The original classes are M_X^0={0}, M_X^1={1}, M_Y^0={2}, M_Y^1={4}.

**Definition 1.5 (Balance on actual simple cycles).**

$$Balanced(F_{\theta}, c, d)\Leftrightarrow \forall v\in V(H_{cd}),\forall p\in Walk(H_{cd}, v, v),IsCycle(p)\implies parity(p)=0$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankThreeProtocol.Balanced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Balanced(F,c,d) means that every actual simple closed cycle in the induced residual has label sum zero in ZMod 2. Odd refers to label parity, not cycle length. The bipartite cycles below have length eight.

**Definition 1.6 (Four surviving simple odd cycles).**

$$\begin{gathered}C(c, d)=P_{1-c}\cup Q_{1-d}\\ \forall c,d\in \{0, 1\}, IsCycle(C(c, d))\land parity(C(c, d))=1\end{gathered}$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankThreeProtocol.cycleWalk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The support is the union of four internally vertex-disjoint paths from y_0 to y_1: P_0=(y_0,x_0,y_1), P_1=(y_0,x_1,y_1), Q_0=(y_0,x_2,y_2,x_3,y_3,x_4,y_1), and Q_1=(y_0,x_5,y_4,x_6,y_5,x_7,y_1). Their label words are respectively 00, 11, 100101 and 011010. For each c,d, traverse P_(1-c) then reverse Q_(1-d). The resulting walk closes in H_cd, has eight distinct cyclic vertices, and has label sum one. H_00 deletes x_0,y_2 and retains P_1 union Q_1; H_01 deletes x_0,y_4 and retains P_1 union Q_0; H_10 deletes x_1,y_2 and retains P_0 union Q_1; H_11 deletes x_1,y_4 and retains P_0 union Q_0.

**Definition 1.7 (The complete concrete task data).**

$$TaskData\Leftrightarrow (\begin{gathered}\lvert D\rvert=16\land \lvert E(G)\rvert=16\land \lvert V\rvert=14\\ \land (\forall x\in X,\exists y\in Y,(x,y)\in D)\\ \land (\forall y\in Y,\exists x\in X,(x,y)\in D)\\ \land Connected(G)\land cycleRank(F_{\theta})=3\\ \land chromaticNumber(G_{A})=2\land chromaticNumber(G_{B})=2\\ \land M_{X}^{0}=\{0\}\land M_{X}^{1}=\{1\}\\ \land M_{Y}^{0}=\{2\}\land M_{Y}^{1}=\{4\}\\ \land (\forall c,d\in \{0, 1\}, IsCycle(C(c, d))\land parity(C(c, d))=1)\\ \land \lvert \alpha(X)\rvert=3\land \lvert \beta(Y)\rvert=3\end{gathered})$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankThreeProtocol.TaskData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

TaskData is the conjunction of all displayed clauses. There are sixteen legal pairs, sixteen support edges, and fourteen vertices. Every row and column is active, and the support is connected. Cycle rank uses integer subtraction: 16-8-6+1=3. In the original Alice conflict graph, x and x' are adjacent exactly when some common legal y gives different labels; the Bob graph exchanges the coordinates. Their edge sets are {01,02,04,15,17,25,34,47,67} and {02,04,13,15,23,45}, respectively. The proper two-color strings are 01101010 and 011010. Both graphs have an edge, so both original chromatic numbers are exactly two. The cycle clause includes both simplicity and parity for each of the four deletions. The final two clauses give the exact reachable image cardinalities.

**Definition 1.8 (The proposed necessity of balanced deletion).**

$$claim\Leftrightarrow (TaskData\implies (Protocol(F_{\theta}, 3, 3, \alpha, \beta, \delta)\implies \exists c,d\in \{0, 1\}, Balanced(F_{\theta}, c, d)))$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankThreeProtocol.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The claim says that the complete concrete task data and correctness of the displayed protocol would force at least one of the four whole-class deletions to be balanced.

**Theorem 1.9 (A finite counterexample to deletion necessity).**

$$\neg (TaskData\implies (Protocol(F_{\theta}, 3, 3, \alpha, \beta, \delta)\implies \exists c,d\in \{0, 1\}, Balanced(F_{\theta}, c, d)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/BooleanRankThreeProtocol.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negated implication is classically equivalent to the full positive conjunction: TaskData holds, the explicit protocol is correct, and every one of the four deletions fails balance. Thus no false antecedent accounts for the refutation. Connectivity follows along the four paths. The two-colorings and an edge in each conflict graph give the exact chromatic numbers. The table determines the original monochromatic classes, and each displayed induced-residual simple cycle has parity one. The sixteen legal-pair checks establish the protocol. These facts occur in the same finite task. This counterexample does not assert a general rank-three feasibility theorem.

$\begin{gathered}\neg (TaskData\implies (Protocol(F_{\theta}, 3, 3, \alpha, \beta, \delta)\implies \exists c,d\in \{0, 1\}, Balanced(F_{\theta}, c, d)))\\ \Leftrightarrow (TaskData\land Protocol(F_{\theta}, 3, 3, \alpha, \beta, \delta)\land (\forall c,d\in \{0, 1\}, \neg Balanced(F_{\theta}, c, d)))\end{gathered}$

## References

- Truth anchor: `D5/S3/Observer/Separation/BooleanRankThreeProtocol.Balanced`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankThreeProtocol.Ftheta`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankThreeProtocol.Protocol`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankThreeProtocol.TaskData`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankThreeProtocol.claim`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankThreeProtocol.cycleWalk`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankThreeProtocol.delta`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankThreeProtocol.residual`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankThreeProtocol.result`
- Dependency: [D5/S3/Fourier/CharacterSelection/SimpleGraphCycleSpace](../../Fourier/CharacterSelection/SimpleGraphCycleSpace.md)
