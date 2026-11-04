# Exact counting complexity of Kay–Bennink parity collisions

## 1. The joint event and its encoding

**Definition 1.1 (Labelled parity collision).** Let $n\ge1$ and $1\le m\le2^n-1$. An admissible matrix $A=(a_1,\ldots,a_m)\in\mathbb F_2^{n\times m}$ has distinct nonzero columns, with their labels retained. For $t\ge1$ and $x=(x_1,\ldots,x_t)\in\mathbb F_2^{n\times t}$, put

$$
I_i^A(x)=\sum_{j=1}^t\langle a_i,x_j\rangle_2\quad(1\le i\le m).
$$

Each inner product is a bit; the displayed sum is in $\mathbb Z$. Define

$$
\begin{aligned}
C(A,t)&=\left|\left\{(x,y)\in
(\mathbb F_2^{n\times t})^2:
I_i^A(x)=I_i^A(y)\ \text{for every }i\right\}\right|,\\
P(A,t)&=2^{-2nt}C(A,t).
\end{aligned}
$$

Thus $P$ is the probability of all indicator equalities holding jointly for independent uniform labelled matrices $x,y$. Both the pair and the $t$ positions are ordered. There is no quotient by column permutations and no multiplication of separate marginal probabilities. This is the combinatorial event defined by Kay and Bennink [KB, “A Combinatorial Problem”].

**Convention 1.2 (Total functions and bit cost).** Fix a finite delimiter alphabet $\{0,1,\#\}$, represented in binary by a fixed length code for its three symbols; unused codewords are malformed. A main input is

$$
\operatorname{bin}(n)\#\operatorname{bin}(m)\#
\operatorname{row}(A)\#1^t,
$$

where binary integers have no leading zero, except that zero is written $0$, and $\operatorname{row}(A)$ lists exactly $nm$ bits in row order. Require the hypotheses of Definition 1.1 and a nonempty final unary field. Every other string has $C=0$ and $P=0/1$. The integer output is ordinary binary, with zero written $0$. The rational output is the pair of ordinary binary integers $(p,q)$ with $p\ge0$, $q\ge1$, $\gcd(p,q)=1$, and value $p/q$; zero is uniquely $(0,1)$. Fixed-$t$ functions $C_t,P_t$ omit the final separator and unary field and use that specified positive constant.

Validity is decidable in polynomial bit time: parse the fields, compare the binary product $nm$ with the actual payload length, check positivity, then check nonzero and pairwise distinct columns. Once the dense payload has the required length and $n,m\ge1$, both dimensions are at most the input length $L$. The bound $m\le2^n-1$ follows from the nonzero distinctness check, without enumerating $2^n$ vectors. These encodings are polynomially equivalent to ordinary explicit dense matrix encodings. Time below includes reading inputs, oracle answers and writing binary outputs. Polynomial-time Turing reductions allow exact function queries followed by polynomial bit arithmetic; all completeness statements use this reduction type.

## 2. Witnesses and exact rational output

**Proposition 2.1 (Membership and interconversion).** For positive unary $t$, $C$ belongs to $\#\mathrm P$ and $P$ belongs to $\mathrm{FP}^{\#\mathrm P}$. On the same inputs, $C$ and $P$ are polynomial-time interconvertible using one query. The statements also hold at every specified fixed positive $t$.

Proof. Reject invalid strings deterministically. For a valid string, nondeterministically choose precisely the $2nt$ entries of $x,y$. For each $i,j$, compute the two mod-two inner products, add their bits in ordinary integers, and accept exactly when all $m$ resulting sums agree. Every ordered labelled pair has exactly one computation path. There are $O(nmt)$ bit contributions and the running sums use $O(\log(t+1))$ bits. Since $n,m,t\le L$, this is a polynomial-time counting machine. Equivalently, a fixed polynomial length witness can pad the $2nt$ bits with required zero bits, preserving exactly one witness per pair.

Let $D=2^{2nt}$. The inequality $0\le C(A,t)\le D$ bounds the integer output length by $2nt+1$. Given the integer answer, compute $g=\gcd(C,D)$ and output $(C/g,D/g)$. Conversely, given the canonical rational answer $(p,q)$, output $pD/q$. On valid inputs this division is exact because the rational equals $C/D$. On invalid inputs return the prescribed zero without a query. The exponent $2nt$ and the bit strings for $D,C,p,q$ have polynomial size for unary $t$; multiplication, division and the Euclidean algorithm on such integers have polynomial bit cost. The conversions therefore include rational reduction and output writing, rather than treating these as unit cost operations. One query to the $\#\mathrm P$ function $C$ gives the asserted upper bound for $P$. The fixed-$t$ cases use the same argument. ∎

## 3. Hardness within the original matrix domain

Let $H$ have three vertices $O,A,R$, a loop at every vertex, and the two nonloop edges $\{O,A\},\{O,R\}$. Its adjacency relation permits every ordered colour pair except $(A,R)$ and $(R,A)$. For an explicitly given finite simple labelled graph $\Gamma$, write $\operatorname{hom}(\Gamma,H)$ for its number of adjacency-preserving vertex maps.

The fixed-target theorem of Dyer and Greenhill [DG, Theorem 1.1; DGC] states that counting homomorphisms to a fixed undirected graph is $\#\mathrm P$-complete unless each component is a complete graph with all loops or a complete bipartite graph without loops. Our $H$ is connected, looped and not complete, so its homomorphism count is hard under polynomial-time Turing reductions. This is an attributed input to the following reduction. Restricting source graphs to be simple and loopless causes no problem: loops and repeated edges of a source graph impose no additional constraints for this reflexive $H$ and can be removed. The corrigendum repairs the disconnected bipartite part of the general argument; $H$ here is connected and reflexive.

**Lemma 3.1 (A graph represented by admissible parity columns).** For a simple labelled graph $\Gamma=(V,E)$ on $V=\{1,\ldots,N\}$ with $N\ge1$, form $A_\Gamma$ from the columns

$$
e_v\quad(v\in V),\qquad e_u+e_v\quad(\{u,v\}\in E),
$$

where the vectors are in $\mathbb F_2^N$. Then $A_\Gamma$ is admissible, has rank $N$, and

$$
C(A_\Gamma,2)=2^N\operatorname{hom}(\Gamma,H).
$$

Proof. The column supports are distinct singletons and distinct two-element edge sets, so all columns are nonzero and distinct. They form a subset of the $2^N-1$ nonempty subsets of $V$, giving the required column bound. The singleton columns contain the identity matrix, hence the rank is $N$. Their order can be any prescribed labelled order, including lexicographic order: reordering the conjunction of indicator equalities changes no pair counted.

For $t=2$, write the $v$th rows of the two sampled matrices as $x_v,y_v\in\{0,1\}^2$. The singleton column $e_v$ requires these rows to have equal integer weight. The possible row pairs split as follows:

| Colour | Row pairs $(x_v,y_v)$ |
| --- | --- |
| $O$ | $((0,0),(0,0))$, $((1,1),(1,1))$ |
| $A$ | $((0,1),(0,1))$, $((1,0),(1,0))$ |
| $R$ | $((0,1),(1,0))$, $((1,0),(0,1))$ |

This list is exhaustive: weights zero and two each have one binary row, and weight one has two choices for each of $x_v,y_v$.

For an edge $\{u,v\}$, its column imposes

$$
(x_{u1}\mathbin\oplus x_{v1})+
(x_{u2}\mathbin\oplus x_{v2})
=
(y_{u1}\mathbin\oplus y_{v1})+
(y_{u2}\mathbin\oplus y_{v2}),
$$

where $\oplus$ denotes bitwise XOR and the two displayed additions are integer additions. If $u$ has colour $O$, then $x_u=y_u=(c,c)$. XOR with this row preserves the other row's weight if $c=0$ and replaces it by $2$ minus that weight if $c=1$. The singleton equality at $v$ therefore proves the edge equality for either choice of $c$. The same argument applies when $v$ has colour $O$.

Otherwise both rows have weight one. For $w=u,v$, write

$$
x_w=(s_w,1-s_w),\qquad
y_w=(s_w\oplus z_w,\,1-(s_w\oplus z_w)),
$$

with $z_w=0$ for colour $A$ and $z_w=1$ for colour $R$. The two sides of the edge equality are respectively

$$
2(s_u\oplus s_v),\qquad
2(s_u\oplus s_v\oplus z_u\oplus z_v).
$$

They agree if and only if $z_u=z_v$. Thus an edge forbids exactly the two colour pairs $A,R$ and $R,A$, independently of the choices $s_u,s_v$.

Consequently every counted pair determines an $H$-colouring, and every $H$-colouring admits exactly two row-pair choices independently at each vertex. All such choices satisfy every edge constraint, and there are no other columns. They give $2^N$ distinct ordered pairs of labelled matrices, proving the identity. ∎

**Theorem 3.2 (Exact parity-collision complexity).** The total function $C$ is $\#\mathrm P$-complete under polynomial-time Turing reductions, already for $C_2$. The exact rational function $P$ is $\#\mathrm P$-hard under these reductions and belongs to $\mathrm{FP}^{\#\mathrm P}$, already for $P_2$.

Proof. Given a source graph on $N\ge1$ vertices, construct $A_\Gamma$. It has $N$ rows and at most $N+\binom N2$ columns, so its explicit dense encoding has $O(N^3)$ bits. Construction and, if desired, lexicographic column sorting take polynomial time. Query $C_2(A_\Gamma)$ and divide its answer by $2^N$. Lemma 3.1 proves that the quotient is exactly $\operatorname{hom}(\Gamma,H)$. Both the query answer, of at most $4N+1$ bits, and the divisor have polynomial length. For the graph on no vertices the homomorphism count is $1$, which is returned directly. Malformed graph encodings can likewise be rejected before any query. This is a polynomial-time Turing reduction from the hard fixed-target count to $C_2$.

Proposition 2.1 supplies membership. Appending the constant unary field $11$ reduces $C_2$ to the main function $C$. The rational claims follow by the exact conversions of Proposition 2.1, with $t=2$ in the same reduction. Here the rational function is classified as hard and in $\mathrm{FP}^{\#\mathrm P}$; its rational output is not an integer-valued $\#\mathrm P$ function. ∎

## 4. Counting codeword tuples, including dependent generators

**Definition 4.1 (Integer-sum energy of an image code).** For an explicitly given binary matrix $G\in\mathbb F_2^{d\times m}$, put

$$
B_G=\{uG:u\in\mathbb F_2^d\}\subseteq\mathbb F_2^m
$$

using row-vector multiplication over $\mathbb F_2$. Define

$$
E(G,t)=
\left|\left\{((b_1,\ldots,b_t),(c_1,\ldots,c_t))\in B_G^t\times B_G^t:
\sum_{j=1}^t b_j=\sum_{j=1}^t c_j\ \text{in }\mathbb Z^m
\right\}\right|.
$$

This counts codeword tuples, not tuples of messages for a possibly redundant generator. Use the encoding of Convention 1.2 with $d$ in place of $n$, allowing $d,m\ge0$ and arbitrary binary columns, including zero or repeated columns; malformed strings have $E=0$. The output is ordinary binary. A zero dimension gives the unique zero codeword and $E=1$. The fixed-$t$ encoding again omits its unary field.

**Theorem 4.2 (Exact image-code complexity).** For positive unary $t$, $E$ is $\#\mathrm P$-complete under polynomial-time Turing reductions, already at $t=2$, without a full-rank hypothesis on its input generator. If $A$ is admissible and has binary rank $r$, then

$$
C(A,t)=2^{2t(n-r)}E(A,t).
$$

Proof. First suppose both generator dimensions are positive. Gaussian elimination over $\mathbb F_2$ computes $r=\operatorname{rank}G$ and a matrix $R$ of $r$ independent rows spanning the same image code, in polynomial bit time. The map $u\mapsto uR$ is a bijection from $\mathbb F_2^r$ to $B_G$: spanning gives surjectivity and independence gives injectivity. Guess $2tr$ coefficient bits in this basis and verify the integer coordinate sums of the resulting codewords. Each ordered pair of codeword tuples has exactly one such witness. The computation and the sums of at most $t$ bits per coordinate have polynomial size, as in Proposition 2.1. In particular,

$$
E(G,t)\le |B_G|^{2t}=2^{2tr},
$$

so the output length is at most $2tr+1$. If $r=0$, accept one deterministic path. If either dimension is zero, the same one-path machine handles the unique zero codeword without iterating over a possibly large binary dimension header. Shape validity is checked by binary multiplication against the payload length before these cases are processed. Thus all encodings in Definition 4.1 give a $\#\mathrm P$ function, even when $G$ has dependent rows.

For the multiplicity formula, let $L_A(u)=uA$. Its kernel has dimension $n-r$, and each fibre over its image has exactly $2^{n-r}$ elements: it is a translate of the kernel. For any $x$, the $j$th output codeword is $x_j^{\mathsf T}A$, whose $i$th coordinate is $\langle a_i,x_j\rangle_2$. Thus the original joint event is exactly equality of the two integer codeword sums. Each ordered pair of codeword tuples has $2t$ independently chosen preimages, giving the stated factor $2^{2t(n-r)}$. The uniform row-space description is also present in Ramírez et al. [R, Theorem 3]; the factor here explicitly retains the labelled message multiplicities needed for this count.

Finally choose $G=A_\Gamma$ from Lemma 3.1. This generator has rank $N=d$, so the factor is $1$. Consequently

$$
E(A_\Gamma,2)=C(A_\Gamma,2)
=2^N\operatorname{hom}(\Gamma,H).
$$

The same query and division as in Theorem 3.2 prove hardness. Using a full-rank subfamily for hardness does not restrict the inputs of the membership result. ∎

## 5. Boundaries of the classification

At $t=1$ the row-space calculation gives a polynomial-time boundary. Indeed, if $r=\operatorname{rank}A$, equality of indicators is $A^{\mathsf T}(x_1-y_1)=0$ over $\mathbb F_2$. For each of the $2^n$ choices of $x_1$ there are $2^{n-r}$ choices of $y_1$ in its kernel coset. Hence

$$
C(A,1)=2^{2n-r},\qquad P(A,1)=2^{-r},\qquad E(G,1)=2^{\operatorname{rank}G}.
$$

The last equality holds because two single codewords have the same integer coordinates precisely when they are equal. Gaussian elimination and writing these powers of two take polynomial time in the explicit input sizes. The probability formula agrees with [R, equation (49)]; these rank identities are supporting boundary calculations, not a new hardness source. Invalid inputs retain their prescribed zeros.

**Proposition 5.1 (Binary-$t$ output obstruction).** If only the encoding of $t$ is changed to ordinary binary while ordinary binary integer and reduced rational outputs are retained, neither the resulting $C$ nor the resulting $P$ has a polynomial-time algorithm on all inputs, by output length alone.

Proof. Fix the admissible one-entry matrix $A=[1]$. A row of length $t$ and weight $k$ has $\binom tk$ choices, so

$$
C([1],t)=\sum_{k=0}^t\binom tk^2=\binom{2t}{t}.
$$

The identity follows by choosing a $t$-element subset of two disjoint $t$-element sets according to how many elements come from the first. Moreover,

$$
\binom{2t}{t}=\prod_{j=1}^t\frac{t+j}{j}\ge2^t,
$$

so its binary output has at least $t+1$ bits.

Reduction of the rational output also leaves a long denominator. Take $t=2^k$ with $k\ge0$. Counting multiples of successive powers of two among the factors of a factorial gives

$$
v_2\!\left(\binom{2t}{t}\right)
=\sum_{j\ge1}
\left(\left\lfloor\frac{2t}{2^j}\right\rfloor
-2\left\lfloor\frac{t}{2^j}\right\rfloor\right)=1.
$$

For $1\le j\le k$ the summand is zero, at $j=k+1$ it is one, and afterwards it is zero. Since the unreduced denominator of $P([1],t)$ is $2^{2t}$, its reduced denominator is exactly $2^{2t-1}$, whose ordinary binary encoding has $2t$ bits. The binary input lengths along $t=2^k$ are $bk+O(1)$ bits, where $b\ge2$ is the fixed codeword width of Convention 1.2, while both output lengths grow exponentially in $k$. A machine writing one output symbol per step cannot produce either output in polynomial input time. ∎

This obstruction is about explicit output representation; it is not a complete classification of binary-$t$ functions or compressed representations. Theorems 3.2 and 4.2 assert fixed-$2$ and unary-$t$ completeness, without asserting a classification for every other fixed $t$.

The restricted graph family selects weight-two columns according to an arbitrary edge set. It is not the family containing all vectors up to a weight bound in [KB, Question 1]. That question, including its printed “fix $m$ and $k\le m$” parameterisation despite column vectors having length $n$, is left unresolved here. No replacement of that parameterisation by $m=n$ is assumed. The classification of all efficiently solvable matrix families in Question 2 and the approximation problem in Question 4 are also unresolved here. The exact-function result supplies a counting formulation of the arbitrary-$A$ issue in Question 3, whose printed “NP-Complete” wording does not specify a decision language. No parsimonious completeness, threshold complexity, physical advantage or circuit-simulation consequence is asserted.

## 6. Mathematical sources and their scope

The proof combines the original integer indicator event with an explicit three-colour lifting identity and the established fixed-graph counting dichotomy. The graph hardness theorem and the row-space facts remain attributed prior results. The restricted-event inference is given in full in Lemma 3.1; no worldwide priority assertion is needed for the stated complexity conclusions.

[KB] Bill Kay and Ryan Bennink, “An Application of Probabilistic Combinatorics to Quantum Circuit Expressiveness,” in S. G. Aksoy et al., *Seven open problems in applied combinatorics*, Journal of Combinatorics **14**(4), 559–601 (2023), [DOI 10.4310/JOC.2023.v14.n4.a8](https://doi.org/10.4310/JOC.2023.v14.n4.a8), [arXiv:2303.11464v1](https://arxiv.org/abs/2303.11464v1), source section Sections/kay_bennink.tex. The definitions and numbered questions are taken from that section.

[DG] Martin Dyer and Catherine Greenhill, *The complexity of counting graph homomorphisms*, Random Structures & Algorithms **17**(3–4), 260–289 (2000), [author manuscript](https://web.maths.unsw.edu.au/~csg/papers/hcompl.pdf), Theorem 1.1. [DGC] The same authors, *Corrigendum: The complexity of counting graph homomorphisms*, updated 9 June 2004, [author correction](https://web.maths.unsw.edu.au/~csg/papers/corrigendum.pdf). These supply the fixed-target hardness theorem used in §3, not the parity-column representation.

[B] Ryan S. Bennink, *Counting Abelian Squares for a Problem in Quantum Computing*, [arXiv:2208.02360v1](https://arxiv.org/abs/2208.02360v1). Its maximal family reduces to abelian-square counting with an efficient recurrence. This structured family is not a hardness result for arbitrary admissible $A$.

[R] Jorge M. Ramírez, Elaine Wong, Caio Alves, Sarah Chehade and Ryan Bennink, *Expressiveness of Commutative Quantum Circuits: A Probabilistic Approach*, [arXiv:2404.19727v2](https://arxiv.org/abs/2404.19727v2), [DOI 10.1109/TQE.2024.3488518](https://doi.org/10.1109/TQE.2024.3488518), Theorem 3 and equation (49). Its uniform row-space distribution and first-moment rank formula are the support identified above; its asymptotic estimates do not supply the exact restricted-event reduction.

[YR] Richard Yu, Jorge Ramirez Osorio and Elaine Wong, *Probabilistic Representation of Commutative Quantum Circuit Models*, [arXiv:2410.19173v2](https://arxiv.org/abs/2410.19173v2). Its commuting-Pauli and stabilizer representation extends the probabilistic description and the ingredients for asymptotic frame-potential calculations. Those statements are not an exact counting classification for Definition 1.1.

[N] Yoshifumi Nakata, Yuki Takeuchi, Martin Kliesch and Andrew Darmawan, *On Computational Complexity of Unitary and State Design Properties*, [arXiv:2410.23353v4](https://arxiv.org/abs/2410.23353v4), Definition 7, Theorems 3–6 and 17, and §IV. Their general frame-potential hardness uses efficiently described arbitrary state or unitary sets, with a Boolean counting instance embedded in the states or reflections. That encoding does not provide the distinct-nonzero binary-column instances of Lemma 3.1. Its promise-gap classifications are not transferred to the present exact functions.

## 追加锚（本行以下为增补区）
