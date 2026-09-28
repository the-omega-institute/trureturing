# Boolean Tasks and the Complete Rank-Three Odd Fiber

## Abstract

Whole original bit-class deletion gives a sufficient protocol construction and a necessary rank-three odd-fiber shape.

Let X and Y be finite sets and let T:X times Y -> Option(F_2) be a partial Boolean table. Write mathcal F for the class of finite sets and T(X,Y) for all such partial tables. The value none denotes an illegal pair; some c assigns the bit c to a legal pair. Write D for the legal pairs and f for their labels. The original support G is the simple bipartite graph on the disjoint union of X and Y, with one edge for each pair in D. Admissibility A(T) means that every vertex on both sides has an incident legal edge, D is nonempty, G is connected, and both original conflict graphs have chromatic number at most two. Two X vertices conflict exactly when they have different legal labels at one common Y vertex; the definition on Y is symmetric. The one-way message costs equal these chromatic numbers. The rank mu(T)=|D|-|X|-|Y|+1 is an integer.

A budget B(T) means that there exist arbitrary ambient message types A and B, encoders alpha:X->A and beta:Y->B, and a total decoder delta:A times B->F_2, with at most three reachable messages on each side. Only the images of the encoders incur cost. Correctness is required on every legal pair, and there is no restriction on illegal pairs. Each encoder sees only its own input, and the decoder sees only the two messages.

$B(T)\iff\exists A,B,\alpha:X\to A,\beta:Y\to B,\delta:A\times B\to\mathbb{F}_{2}, \lvert\alpha(X)\rvert\leq3\land \lvert\beta(Y)\rvert\leq3\land (\forall (x,y)\in D,\delta(\alpha(x), \beta(y))=f(x, y))$

For c,d in F_2, M_X^c and M_Y^d are the entire original globally monochromatic bit classes. Membership tests every original incident legal edge, including edges outside a chosen cycle. Form H_cd by deleting both whole classes. Equivalently, retain the original vertex carrier and isolate the deleted vertices; this preserves all surviving simple cycles. These classes are fixed from T before deletion. They are neither completed response classes nor classes recomputed from the residual graph.

$\begin{gathered}M_{X}^{c}=\{x\in X\mid\forall y\in Y,(x,y)\in D\implies f(x, y)=c\}\\M_{Y}^{d}=\{y\in Y\mid\forall x\in X,(x,y)\in D\implies f(x, y)=d\}\\H_{cd}=G-(M_{X}^{c}\cup M_{Y}^{d})\\U(T)\iff\forall c,d\in\mathbb{F}_{2},\neg Balanced(H_{cd})\end{gathered}$

A support subgraph is balanced when every simple cycle has label sum zero in F_2. Thus odd means label parity one, although all cycle lengths in this bipartite graph are even. Let U(T) mean that all four H_cd are unbalanced. Let Z(G) be the binary cycle space, realized as the span of the edge indicators of actual simple cycles. For z in Z(G), lambda(z) is the sum over original edges of f(e) times z(e).

The shape S(T) consists of simple cycles C_ij indexed by all four pairs (i,j) in F_2 times F_2. Their edge indicators z_ij must be pairwise distinct, and the whole original odd fiber must equal their set. Each C_ij contains an original monochromatic X vertex of bit i and an original monochromatic Y vertex of bit j. Every original monochromatic X vertex on that cycle has bit i, and every original monochromatic Y vertex on it has bit j. The four indicators sum to zero and their linear span has dimension three. Cycles are distinguished by edge indicators, independently of starting point or orientation.

$\begin{gathered}S(T)\iff\exists C:\mathbb{F}_{2}^{2}\to Cycle(G),\\(\forall i,j,k,l\in\mathbb{F}_{2},z_{ij}=z_{kl}\implies(i=k\land j=l))\\\land(\forall z\in Z(G),\lambda(z)=1\iff\exists i,j\in\mathbb{F}_{2},z_{ij}=z)\\\land(\forall i,j\in\mathbb{F}_{2},(\exists x\in V(C_{ij}),x\in M_{X}^{i})\land(\exists y\in V(C_{ij}),y\in M_{Y}^{j}))\\\land(\forall i,j,c\in\mathbb{F}_{2},\forall x\in V(C_{ij}),x\in M_{X}^{c}\implies c=i)\\\land(\forall i,j,d\in\mathbb{F}_{2},\forall y\in V(C_{ij}),y\in M_{Y}^{d}\implies d=j)\\\land z_{00}+z_{01}+z_{10}+z_{11}=0\land dim_{\mathbb{F}_{2}}span_{\mathbb{F}_{2}}\{z_{ij}\mid i,j\in\mathbb{F}_{2}\}=3\end{gathered}$

**Theorem 1.1 (Balanced deletion, the complete odd fiber, and failure of sufficiency).**

$$\begin{gathered}(\forall X,Y\in\mathcal{F},\forall T\in T(X, Y),A(T)\implies(((\exists c,d\in\mathbb{F}_{2},Balanced(H_{cd}))\implies B(T))\land (U(T)\implies(3\leq\mu(T)\land (\mu(T)=3\implies S(T))))\land (\neg B(T)\implies(3\leq\mu(T)\land (\mu(T)=3\implies S(T))))))\\\land\\(\exists T\in T(Fin(8), Fin(6)),A(T)\land \mu(T)=3\land U(T)\land S(T)\land B(T))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/BooleanRankThreeFiber.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universal assertion ranges over every finite X and Y with decidable equality and every admissible partial Boolean table T on them. If some H_cd is balanced, then B(T) holds. If all four are unbalanced, mu(T)>=3, and equality forces S(T). In particular, the absence of a (3,3) protocol implies the same rank bound and the same conditional shape. The existential assertion concerns a table on Fin 8 times Fin 6: it is admissible, has rank three, satisfies U(T) and S(T), and nevertheless has a (3,3) protocol. Thus the rank-three shape is necessary for infeasibility but is not sufficient. No assertion of feasibility for every rank-three task follows.

For a balanced H_cd, the cycle-space potential theorem gives a vertex potential whose endpoint sum equals each surviving edge label. Each surviving vertex sends its potential bit, and every vertex in the deleted class on a side sends one special message. Decode ordinary pairs by addition in F_2, a special Alice message by c, and a special Bob message by d. When both are special, any legal edge forces c=d; if c differs from d, that corner has no legal edge. This proves correctness on all original legal pairs using at most three messages per side, regardless of the sizes of the deleted classes.

A proper two-coloring of Bob's original conflict graph makes each nonmonochromatic row equal, on its legal entries, to a row-dependent bit plus Bob's color. If an odd simple cycle contained no original globally monochromatic X vertex, these edge labels would telescope around the cycle to zero. This is impossible. The symmetric argument supplies an original globally monochromatic Y vertex. Choose C_ij in H_(1-i,1-j). Its original monochromatic vertices can only have the remaining bits i and j. The witnesses on both sides then force distinct indicators for distinct index pairs: equal indicators give equal edge sets and hence equal vertex supports.

The graph-to-linear correspondence uses the actual support. Sending a legal pair (x,y) to the unordered edge joining its two tagged vertices is a bijection. Connectedness gives exactly one component, so the finite-graph cycle-space dimension formula yields dim Z(G)=|D|-|X|-|Y|+1=mu(T). A simple cycle traverses each of its edges once. Consequently the coordinate pairing defining lambda on its indicator is exactly the sum of its walk labels, without multiplicity or orientation ambiguity.

All four chosen indicators lie in lambda^(-1)(1), so lambda is nonzero. Translation by one of them identifies this fiber with ker lambda, whose dimension is dim Z(G)-1. Its cardinality is therefore 2^(dim Z(G)-1). The injection from the four bit pairs gives mu(T)>=3. At rank three the fiber has exactly four elements, so this injection is surjective: it exhausts every original odd cycle-space vector, including any vector not initially presented as a simple cycle. A coset of a two-dimensional binary kernel has the form {z,z+u,z+v,z+u+v}; its four elements sum to zero and span the whole three-dimensional space. The infeasibility assertion is the contrapositive of the balanced-deletion construction followed by this argument.

For nonsufficiency, take the following actual table; a star is an illegal pair.

$T_{\theta}=\begin{pmatrix}0&0&*&*&*&*\\1&1&*&*&*&*\\1&*&0&*&*&*\\*&*&0&1&*&*\\*&1&*&0&*&*\\0&*&*&*&1&*\\*&*&*&*&1&0\\*&0&*&*&*&1\end{pmatrix}$

Its support consists of four internally disjoint paths from y_0 to y_1: P_0=(y_0,x_0,y_1), P_1=(y_0,x_1,y_1), Q_0=(y_0,x_2,y_2,x_3,y_3,x_4,y_1), and Q_1=(y_0,x_5,y_4,x_6,y_5,x_7,y_1). Their label words are respectively 00, 11, 100101, and 011010. All fourteen vertices are active and connected, and there are sixteen edges, giving rank 16-8-6+1=3. Proper colorings of the two original conflict graphs are 01101010 and 011010. The original bit classes are M_X^0={x_0}, M_X^1={x_1}, M_Y^0={y_2}, M_Y^1={y_4}. Each H_cd still contains the odd simple cycle P_(1-c) united with Q_(1-d). Thus all four residuals are unbalanced and the entire odd fiber consists of the four indicators of P_i united with Q_j.

The actual encoders and decoder below use three reachable messages on each side. Substitution at each of the sixteen legal entries gives exactly its table bit. Hence the same task simultaneously has rank three, the entire four-cycle odd fiber, four unbalanced residuals, and an actual (3,3) protocol.

$\begin{gathered}\alpha=(0,1,1,0,1,0,0,2)\\\beta=(0,0,1,2,2,1)\\\delta=\begin{pmatrix}0&0&1\\1&0&0\\0&1&0\end{pmatrix}\end{gathered}$

## References

- Truth anchor: `D5/S3/Observer/Separation/BooleanRankThreeFiber.result`
- Dependency: [D5/S3/Fourier/CharacterSelection/SimpleGraphCycleSpace](../../Fourier/CharacterSelection/SimpleGraphCycleSpace.md)
