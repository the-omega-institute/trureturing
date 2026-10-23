# FIB Critical Mixed Gain Words and Clock-Pencil Obstructions

## 1. Domain, clocks, outputs, and the critical question

Fix a declared maximum degree $d\ge1$ and write $m=d+1$. A world is a triple $(P,g,\delta)$ with $P$ a strictly entrywise positive real $2\times2$ matrix of rank one and trace one,

$$
g(t)=\sum_{j=0}^{m-1}\beta_jt^j,\qquad
\beta\in\mathbb R^m\setminus\{0\},\qquad \delta\in\mathbb R.
\tag{1.1}
$$

All lower actual degrees, coefficient signs, sampled roots, repeated roots, and constant drifts belong to the domain. Put

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
A_0=I,\qquad A_i=E_iA_{i-1},\qquad
z_i=g(i)\operatorname{tr}(A_iP)+\delta,
\tag{1.2}
$$

where each chronological action $E_i$ is one $M$ or one $J$, immediately followed by its read. The initial read counts. Thus $N$ reads have original clocks $0,\ldots,N-1$. No construction uses resets, copies, skipped reads, unread compound actions, additional sensors, empty-action reads, or clock renumbering.

For a terminal word $w$, let $Z_w=(z_0,\ldots,z_{N-1})^{\mathsf T}$. A fixed real $m\times N$ matrix succeeds if

$$
CZ_w=s\beta\qquad\text{with }s\in\mathbb R\setminus\{0\}.
\tag{1.3}
$$

The output concerns the entire declared coefficient vector, not just the highest coefficient or the actual-degree truncation. Either sign of $s$ is allowed. A countable palette has at most countably many fixed matrices per terminal word. Its selector may be any function of actual history, with no regularity assumption. Matrices whose entries themselves depend on observations are outside this contract.

A fixed acquisition word is preassigned independently of observations. A deterministic adaptive protocol may choose actions, stopping, and its answer from actual history. Complete-target recovery means recovering $(P,g,\delta)$, and is different from gain-only extraction. Lower bounds for complete recovery equipped with (1.3) do not automatically apply to unrestricted nonlinear recovery.

The critical mixed budget is

$$
N=2m+1=2d+3,
\tag{1.4}
$$

with exactly $2m$ actions and both letters present. The results below classify the possible universal identities at this budget, resolve the countable-palette issue at their exceptional sources, and give an exact positive interpolation condition for fixed mixed acquisition. Positive interpolation itself is impossible for $m=3,4$, independently of the block determinant condition. Together with the degree-one case, this gives sharp fixed mixed thresholds of six, eight, and ten reads for $d=1,2,3$, respectively, even with arbitrary countable palettes. For $m\ge5$ the exact positive criterion remains open. A separate common-open-domain argument gives a six-read lower bound for degree-one complete-target protocols with the specified countable linear gain-output mechanism; no analogous adaptive lower bound is deduced in degrees two or three.

The Hermite thresholds and constructions, critical classification, and quadratic/cubic feasibility proofs are supplied results, reproduced with complete proofs and credited in Section 18. The thresholds here concern the full immediate-read model, not a known-factor subspace or an unrestricted nonlinear recovery problem.

## 2. Elementary algebra and evaluation facts

Write $\mathcal P_s$ for real polynomials of degree at most $s$, including zero. For any list of distinct clocks, evaluation of $\mathcal P_{m-1}$ has rank the smaller of $m$ and the number of clocks. Indeed, a nonzero polynomial of degree at most $m-1$ has at most $m-1$ distinct roots; at at most $m$ nodes, Lagrange polynomials give arbitrary values. Throughout,

$$
V_{ij}=i^j\quad(0\le j<m),\qquad 0^0=1,
\qquad U=\operatorname{range}V.
\tag{2.1}
$$

A diagonal operator preserving the evaluation space of $\mathcal P_{m-1}$ on $n\ge m+1$ distinct nodes is scalar. To prove this, take a polynomial whose roots are any chosen $m-1$ nodes. Its diagonal image is represented by a polynomial of degree at most $m-1$ with those roots, hence is a scalar multiple of it. All diagonal entries outside those roots are equal. For any two nodes, the other $n-2\ge m-1$ nodes supply the roots, proving equality of those two entries. This includes zero diagonal entries.

The identities

$$
M^2=M+I,\quad J^2=I,\quad M^{-1}=M-I,
\quad JM=2I+J-MJ,\quad JMJ=I+2J-M
\tag{2.2}
$$

follow by multiplication. The four matrices $I,M,J,MJ$ are independent: the entries of a linear combination are

$$
aI+bM+cJ+eMJ=
\begin{pmatrix}a+e&b+c\\b+c+e&a+b+e\end{pmatrix},
$$

so vanishing successively forces $e,a,b,c$ to be zero. In particular, $I,M,J,JM$ are also independent. Set $F_{-1}=1,F_0=0,F_1=1$ and $F_{k+1}=F_k+F_{k-1}$. Induction in (2.2) gives

$$
M^k=F_{k-1}I+F_kM\quad(k\ge0),\qquad F_k>0\quad(k\ge1).
\tag{2.3}
$$

Distinct nonnegative powers of $M$ are nonproportional: a proportionality, after multiplication by an inverse power, would make $M^k$ scalar for some $k>0$, contrary to its nonzero off-diagonal entry $F_k$. Right multiplication by any integral power of $M$ preserves $\operatorname{span}\{I,M\}$ bijectively. Inverses here are auxiliary algebra and are never acquired actions.

Every mixed word has cumulative-matrix span at least three. If its first run is $M^a$, $a\ge1$, the first $J$ gives $JM^a$. The matrices $I,M$ are symmetric, whereas the off-diagonal entries of $JM^a$ differ by $F_a>0$. If the first run is $J^b$, the first $M$ gives $M$ or $MJ$; neither is in $\operatorname{span}\{I,J\}$, by its diagonal or off-diagonal entries.

Two useful charts of the complete legal source domain are

$$
P(x,r)=\frac1{1+xr}\begin{pmatrix}1&r\\x&xr\end{pmatrix},\quad x,r>0,
\tag{2.4}
$$

and

$$
P(\theta,c)=\begin{pmatrix}1-\theta&\theta(1-\theta)/c\\c&\theta\end{pmatrix},
\quad 0<\theta<1,\quad c>0.
\tag{2.5}
$$

These are surjective and unique: rank one gives $P_{11}P_{22}=P_{12}P_{21}$, and trace one determines the remaining entry. For (2.4), $x=P_{21}/P_{11}$ and $r=P_{12}/P_{11}$. For (2.5), use $\theta=P_{22},c=P_{21}$. Both are charts of a nonempty open two-dimensional parameter domain.

The legal sources span $\operatorname{Mat}_2(\mathbb R)$. Choose two independent strictly positive columns and two independent strictly positive rows. Their four outer products are a basis of the matrix space; their positive traces allow normalization without loss of independence. The trace pairing on all matrices is nondegenerate, as testing against matrix units shows.

## 3. Universal identities and the covering principle

For an auxiliary real matrix $S$, put $a_i(S)=\operatorname{tr}(A_iS)$. A nonzero universal identity is a pair $(C,L)$, $L\ne0$, with

$$
C\mathbf1=0,\qquad
C\operatorname{diag}(a(S))V=\operatorname{tr}(LS)I_m
\quad\text{for every }S\in\operatorname{Mat}_2(\mathbb R).
\tag{3.1}
$$

Auxiliary $S$ are a way to express linear identities, not additional physical sources.

**Lemma 3.1.** If a fixed matrix is collinear with $\beta$ at every world, allowing zero output in this hypothesis, it satisfies (3.1) for some possibly zero $L$. Success at one world forces $L\ne0$.

**Proof.** Varying $\delta$ for each fixed $\beta\ne0$ puts $C\mathbf1$ in every line $\mathbb R\beta$. Their intersection is zero because $m\ge2$. At fixed $P$, the linear coefficient map sends every vector into its own line. Its action on basis vectors is diagonal, and its action on each sum of two basis vectors makes all diagonal entries equal. One diagonal entry defines a linear functional of $S$, represented uniquely by $\operatorname{tr}(LS)$. The other entries agree with this scalar on all legal $P$, and hence on all matrices by the source-span fact. If $L=0$, the output is zero at every world. $\square$

**Lemma 3.2 (countable covering).** If no nonzero identity exists for a word, no countable palette for that word succeeds on the entire domain. The same conclusion holds for finitely many words none of which has a nonzero identity.

**Proof.** Collinearity is the system

$$
\beta_j(CZ_w)_k-\beta_k(CZ_w)_j=0\quad(0\le j<k<m).
\tag{3.2}
$$

After substitution of (2.4) and multiplication by $1+xr$, these are polynomials on

$$
(0,\infty)^2\times(\mathbb R^m\setminus\{0\})\times\mathbb R.
\tag{3.3}
$$

For every matrix successful somewhere, at least one polynomial is nonzero; otherwise Lemma 3.1 supplies a forbidden nonzero identity. A nonzero real polynomial has no open zero set: induction on the number of variables, expanding in the last variable on a product of intervals, reduces this to the univariate root bound. Its zero set is closed and nowhere dense relative to (3.3).

A nonempty Euclidean open set is not a countable union of such sets. For this form of the Baire principle, start with a positive-radius closed ball inside the open set and choose nested positive-radius closed subballs avoiding successive zero sets, with diameters tending to zero. Completeness supplies a common point, which avoids every set. There are only countably many word-matrix pairs. Every successful world must belong to the zero set for its selected pair, a contradiction. No regularity of the selection sets has entered. $\square$

The same proof works on any nonempty open parameter domain of realized observations with polynomial, or nowhere-singular rational, dependence. In particular, to obstruct covering an exceptional source stratum, it suffices to prove that every fixed matrix collinear throughout that stratum is zero throughout it. Every matrix successful there then supplies a nonzero collinearity polynomial on that parameter domain. Realization of every parameter value is required; a continuous or measurable choice of source realizing it is not.

## 4. The critical three-dimensional span

**Theorem 4.1.** For a critical mixed identity (3.1), let

$$
H=\operatorname{span}\{A_0,\ldots,A_{2m}\},\qquad
E=\ker\operatorname{tr}(L\,\cdot),\qquad K=\ker C.
$$

Then $\dim K=m+1$, no $A_i$ is proportional to $L$, $\dim H=3$, and $L\in H$.

**Proof.** A choice of $S$ with $\operatorname{tr}(LS)\ne0$ in (3.1) gives $\operatorname{rank}C=m$. Thus $\dim K=m+1$, and $K$ contains $\mathbf1$ and every $\operatorname{diag}(a(S))U$ for $S\in E$.

Let $Q=\{i:A_i\text{ is proportional to }L\}$ and $q=|Q|$. Adjacent cumulative matrices are never proportional, since $A_{i+1}=cA_i$ would imply $E_{i+1}=cI$. Hence $q\le m+1$. For $i\notin Q$, the restriction of $a_i$ to $E$ is nonzero; a linear functional vanishing on $\ker\operatorname{tr}(L\,\cdot)$ is proportional to that functional. Avoiding finitely many proper hyperplanes in $E$, choose $S$ such that $a_i(S)\ne0$ precisely off $Q$. Such avoidance follows, for example, because the product of the nonzero linear defining polynomials cannot vanish identically.

If $1\le q\le m$, there are at least $m+1$ complementary nodes. The nuisance image has dimension $m$ and vanishes on $Q$. The subspace of $K$ vanishing on $Q$ has dimension at most $m$, since $\mathbf1\in K$ does not vanish there. It therefore equals this image. For every $T\in E$, division by the chosen nonzero entries shows that the diagonal operator $a_i(T)/a_i(S)$ on the complementary nodes preserves degree-$(m-1)$ evaluation. Section 2 makes it scalar. All restrictions $a_i|_E$ consequently span at most one dimension, including their zero restrictions on $Q$. Lifting from $E$ to the full matrix space adds at most the functional represented by $L$. Hence $\dim H\le2$, contrary to mixedness.

If $q=m+1$, nonadjacency among $2m+1$ indices forces $Q=\{0,2,\ldots,2m\}$. Since $A_0=I$, every even cumulative matrix is scalar. Each pair $E_{2j}E_{2j-1}$ therefore has scalar product. Of $MM,MJ,JM,JJ$, (2.2) and their entries show that only $JJ$ is scalar. The word would be pure $J$. Thus $q=0$.

Choose $S\in E$ with $a=a(S)$ nonzero at every node, and let $r_0=\dim a(E)\le3$. Suppose $r_0=3$. Retain three coordinate positions witnessing this rank, and choose $m-2$ other positions $R$ disjoint from them; for $m=2$, take $R$ empty. Evaluation of $\operatorname{diag}(a)U\subset K$ on $R$ is surjective. Therefore

$$
K_R=\{v\in K:v|_R=0\}
\quad\text{has dimension }(m+1)-(m-2)=3.
$$

Put $p_R(t)=\prod_{r\in R}(t-r)$. Both $a(T)p_R$ and $a(T)t p_R$ are in $K_R$ for every $T\in E$, since their polynomial factors have degrees at most $m-1$. Restrict to the remaining $m+3$ positions and divide by the nonzero values of $p_R$. The restricted space $W=a(E)|_{R^c}$ has dimension three by the retained coordinates. It and its clock multiple lie in a three-dimensional transformed copy of $K_R$. Thus $tW\subset W$. But $W$ contains the full-support vector $a|_{R^c}$. Its successive clock multiples through degree $m+2$ are independent by Vandermonde evaluation, and lie in $W$, a contradiction. Therefore $r_0\le2$.

Restriction of linear functionals to $E$ has kernel the line represented by $L$. Accordingly $r_0$ is the dimension of the image of $H$ in the quotient by that line. If $L\notin H$, then $r_0=\dim H\ge3$, impossible. If $L\in H$, then $\dim H=r_0+1$. Mixedness forces $r_0=2$ and $\dim H=3$. $\square$

## 5. The clock pencil or one exceptional read

**Theorem 5.1.** Every critical mixed identity has one of the following structures.

1. There are matrices $B,D$, independent modulo $\mathbb RL$, and scalars $w_i\ne0,\lambda_i$ such that

$$
A_i=\lambda_iL+w_i(B+iD).
\tag{5.1}
$$

Moreover $K$ is $\operatorname{diag}(w)$ times degree-at-most-$m$ evaluation, so $w_iR(i)=1$ for some $R\in\mathcal P_m$. The projective classes of $A_i$ modulo $L$ are injective functions of the original clock.

2. There is a unique exceptional index $r$ with $Ce_r=0$, and all $A_i$ with $i\ne r$ span a two-dimensional plane containing $L$. The exceptional $A_r$ is outside that plane.

**Proof.** By Theorem 4.1 choose a full-support vector $a\in a(E)$ and an independent $b\in a(E)$; these span $a(E)$. Put $h_i=b_i/a_i$, a nonconstant vector. The space

$$
W=\operatorname{diag}(a)\bigl(U+\operatorname{diag}(h)U\bigr)
$$

lies in $K$. Its dimension exceeds $m$, for equality would make the diagonal operator $h$ preserve $U$ and therefore make $h$ constant. Hence $W=K$ and $\dim W=m+1$.

Consider the polynomial-pair space

$$
\mathcal T=\{(p,q)\in\mathcal P_{m-1}^2:p(i)=h_iq(i)\text{ at every node}\}.
\tag{5.2}
$$

The map $(p,q)\mapsto(p(i)-h_iq(i))_i$ has image dimension $m+1$, so $\dim\mathcal T=m-1$. A nonzero pair has $q\ne0$, since $q=0$ would give too many roots for $p$. For any two pairs, $pq'-p'q$ has degree at most $2m-2$ and $2m+1$ roots; it is zero.

Reduce the ratio of one nonzero pair to coprime polynomials $p_*,q_*$. Every pair is $(fp_*,fq_*)$ for a polynomial $f$. For nonzero $p_*$ this follows from the cross-product identity and coprimality, which makes $q_*$ divide $q$ and then makes $p=fp_*$. If the numerator is zero, take $(p_*,q_*)=(0,1)$; the same identity makes every numerator zero, and the assertion still holds. Let $s=\max(\deg p_*,\deg q_*)\ge0$, ignoring the degree of a zero numerator.

Let $B_{\rm bad}$ be the nodes where $p_*(i)\ne h_iq_*(i)$. Exactly at these nodes must $f$ vanish. Every zero of $q_*$ is bad, since coprime polynomials have no common root. The degree condition on both components is precisely $\deg f\le m-1-s$. Thus

$$
\dim\mathcal T=\max\{m-s-|B_{\rm bad}|,0\}=m-1,
$$

and $s+|B_{\rm bad}|=1$.

If $s=1$ and there are no bad nodes, $h$ is a nonconstant fractional linear function of clock, with denominator nonzero at every node. The linear polynomials $p_*,q_*$ are independent, or their reduced ratio would be constant. With $w_i=a_i/q_*(i)$, we get

$$
a(E)=\operatorname{diag}(w)\operatorname{span}\{\mathbf1,(i)_i\}.
$$

The two coefficient functionals on $E$ may be extended to the full matrix space and represented by matrices $B,D$. Their restrictions are independent, so $B,D$ are independent modulo $L$. Each $a_i$ differs from $w_i(B+iD)$, as a trace functional, by a multiple of $L$, proving (5.1). Also $K=\operatorname{diag}(w)\operatorname{eval}(\mathcal P_m)$, since $\mathcal P_{m-1}+t\mathcal P_{m-1}=\mathcal P_m$. The inclusion $\mathbf1\in K$ proves the $R$ assertion. Independence of $B,D$ modulo $L$ makes the projective classes $[B+iD]$ pairwise distinct. In particular no two cumulative matrices can be proportional.

If $s=0$ and there is one bad node $r$, $h$ is constant except there. Then

$$
K=\operatorname{diag}(a)U+\mathbb Re_r,
$$

so $Ce_r=0$. Off $r$, the restrictions of $a_i$ to $E$ span a line. Therefore those $A_i$ span at most two dimensions. Deleting one node from at least five leaves an adjacent pair, whose matrices are independent, so the span is exactly two. Its image modulo $L$ is one-dimensional, hence it contains $L$. The full span has dimension three, so $A_r$ is outside it. For uniqueness, if $Ce_s=0$ with $s\ne r$, the displayed formula for $K$ would give $e_s=\operatorname{diag}(a)\operatorname{eval}(p)+te_r$ for $p\in\mathcal P_{m-1}$. Then $p$ has the $2m-1$ distinct zeros outside $\{r,s\}$ and is zero, contradicting the coordinate at $s$. Thus $r$ is the only zero column, and in particular the only possible exceptional index for this identity. $\square$

## 6. Completeness of the legal-word classification

**Lemma 6.1.** A mixed word with three-dimensional cumulative span is precisely of the form

$$
M^aJ^bM^c,\qquad a,c\ge0,\quad a+c>0,\quad b>0,
\tag{6.1}
$$

with $b$ even when both $a,c>0$.

**Proof.** If a word starts with $J^b$ and then takes $M$, its span becomes $\operatorname{span}\{I,J,M\}$ for even $b$ and $\operatorname{span}\{I,J,MJ\}$ for odd $b$. Further $M$ actions remain there, by (2.3). A later $J$ after $k\ge1$ such $M$ actions adds $JM^k$ or $JM^kJ$. In the even case $JM^k=F_{k-1}J+F_kJM$ is outside $\operatorname{span}\{I,J,M\}$. In the odd case $JM^kJ=F_{k-1}I+F_kJMJ$ is outside $\operatorname{span}\{I,J,MJ\}$, using (2.2) and the independent basis. Thus there is no later $J$.

If the word starts with $M^a$, $a\ge1$, its first $J$ adds $JM^a$ to $\operatorname{span}\{I,M\}$. Consecutive $J$ actions toggle $JM^a$ and $M^a$. An $M$ after an odd number of them gives $MJM^a$, outside the current span: right multiplication by $M^{-a}$ reduces this to the independence of $I,M,J,MJ$. After an even number of $J$ actions, $M$ actions return to the pure-$M$ algebra. A later $J$ at a larger exponent would add $JM^{a+k}$, $k\ge1$. Right multiplication by $M^{-a}$ reduces the fourth-direction claim to independence of $J$ and $JM^k$ modulo $\operatorname{span}\{I,M\}$, which follows from $F_k>0$ and the basis $I,M,J,JM$. Thus there is at most one $J$ block, and an interior block must have even length. Conversely all forms in (6.1) with this parity condition stay in the indicated three-plane and are mixed, so have span three. $\square$

**Theorem 6.2.** The clock-pencil alternative (5.1) is impossible for a legal critical mixed word. In the exceptional alternative, the only word families are

$$
M^{2m-1}J,\qquad JM^{2m-1},\qquad
M^aJJM^{2m-2-a}\ (0\le a\le2m-2),\qquad
MJ^{2m-1},\qquad J^{2m-1}M.
\tag{6.2}
$$

For each family the exceptional read is uniquely the one outside its repeated or translated two-plane.

**Proof.** Apply Lemma 6.1. A $J$ block of length at least two repeats its preceding cumulative matrix two clocks later, forbidden by clock-pencil injectivity. Thus a pencil word has one $J$, at an edge. It contains $2m\ge4$ consecutive cumulative matrices in a right-translated $M$ trajectory. The first four are

$$
B,\quad MB,\quad B+MB,\quad B+2MB.
$$

If $L$ lies in their two-plane, their nonzero projections modulo $L$ are projectively identical, contradicting pencil injectivity. Otherwise projection is injective on the plane and preserves projective cross ratio. In the basis $B,MB$ their projective coordinates are $0,\infty,1,2$, with cross ratio $1/2$, using the convention

$$
[x_0,x_1;x_2,x_3]=
\frac{(x_0-x_2)(x_1-x_3)}{(x_0-x_3)(x_1-x_2)}.
$$

Four consecutive clocks have cross ratio $4/3$. Formula (5.1) induces an invertible projective linear map from clock to projected matrix, so these ratios would agree. This is impossible.

For the exceptional case let (6.1) have $a+b+c=2m$. If $b=2h$ is even, the pure states have exponents $0,\ldots,a+c$ and the other state $JM^a$ occurs $h$ times. The positive even integer $a+c$ is at least two. Deleting one pure state leaves two distinct pure powers, which span their plane. Deleting just one index can therefore reduce total rank to two only when it removes the sole occurrence of $JM^a$, that is, $h=1$. This is the $JJ$ family.

If $b$ is odd the $J$ block is at an edge. If the $M$ run has length at least two, its plane contains three distinct projective $M$ states, or three right-translates of such states. Deleting one still leaves that plane. The state outside it occurs $(b+1)/2$ times, so it can be removed by one deletion only if $b=1$. These are the two edge-$J$ words. If the $M$ run has length one, $b=2m-1$, giving the two predominantly-$J$ words.

For a $JJ$ word the unique outside state is $JM^a$, at clock $a+1$; the pure exponents $0,\ldots,2m-2$ leave at least two distinct powers after any other deletion. For an edge-$J$ word the outside state is its last or initial read; the other $2m$ states span the translated $M$ plane after any other deletion. For a predominantly-$J$ word the outside state is its initial or last read; each of the other two states occurs $m\ge2$ times. Thus the exceptional index is unique for the word, not merely for a chosen identity. $\square$

## 7. Edge-$J$ words and their obstruction

**Proposition 7.1.** Neither $M^{2m-1}J$ nor $JM^{2m-1}$ has a nonzero universal identity.

**Proof.** The exceptional column is zero by Theorems 5.1 and 6.2. For $M^{2m-1}J$, deleting it leaves $2m$ consecutive pure-$M$ reads, excluded by the pure-$M$ obstruction proved in Section 12.

For $JM^{2m-1}$, deleting clock zero leaves original clocks $1,\ldots,2m$ with matrices $M^{i-1}J$. In the auxiliary identity put $S'=JS$, an invertible substitution, and express $g(s+1)$ in the monomial basis in $s$. Translation is an invertible fixed change of the full coefficient space: its inverse is translation by $-1$. Multiplying the output by that basis-change matrix would turn the asserted identity into a nonzero $2m$-read pure-$M$ identity, again impossible by Section 12. This change of variables analyzes an identity; it does not renumber any acquired clock or restrict the degree space. $\square$

## 8. Predominantly-$J$ identities and all their exceptional sources

**Proposition 8.1.** The universal identities for $J^{2m-1}M$ have, up to scalar, functional $I-J$. Those for $MJ^{2m-1}$ have functional $M-JM$. Each exists. Neither word admits an all-input countable palette.

**Proof.** For $J^{2m-1}M$, discard the exceptional last column. There are $m$ even and $m$ odd original clocks. Interpolate a degree-at-most-$(m-1)$ polynomial on each group. Their coefficient vectors are

$$
\beta+\delta e_0,\qquad \operatorname{tr}(JP)\beta+\delta e_0.
$$

Their difference is $(1-\operatorname{tr}(JP))\beta$, giving a fixed identity. For $MJ^{2m-1}$, discard the exceptional initial column and interpolate on the odd and even clocks in $1,\ldots,2m$. Their factors are $\operatorname{tr}(MP)$ and $\operatorname{tr}(JMP)$, giving $\operatorname{tr}((M-JM)P)\beta$.

These exhaust the identities. In each case the two scalar trace functionals are independent, and the two Vandermonde blocks are invertible. A universal coefficient identity consequently forces each block map to be a scalar multiple of $I_m$. Applying drift annihilation to $e_0$ forces the two scalars to sum to zero. The exceptional column is zero and the functional lies in the remaining plane, as already proved.

For $P=\left(\begin{smallmatrix}1-\theta&b\\c&\theta\end{smallmatrix}\right)$ with $bc=\theta(1-\theta)$, the first scale is $1-b-c$. Its zero set has $\{b,c\}=\{\theta,1-\theta\}$, since these are precisely the roots of $X^2-X+\theta(1-\theta)$. It is the union of the identical-row and identical-column source families. The second scale is $b-(1-\theta)$; rank one makes its zero set exactly the identical-column family. The maps succeed off these loci, but this does not imply full-domain success.

For the palette obstruction use the actual legal family

$$
P(u)=\begin{pmatrix}u&u\\1-u&1-u\end{pmatrix},\qquad 0<u<1.
\tag{8.1}
$$

On $J^{2m-1}M$ all trace factors are $1$ except the last, which is $1+u$. On $MJ^{2m-1}$ all factors are $2-u$ except clock zero, which is $1$. Thus the factor vector is $f(u)\mathbf1+(h(u)-f(u))e_r$, with $f>0$ and nonconstant $h/f$.

If a fixed $C$ is collinear for every $(u,\beta,\delta)$ on this stratum, drift variation gives $C\mathbf1=0$, and its coefficient matrix is scalar for every $u$. That matrix is

$$
f(u)CV+(h(u)-f(u))(Ce_r)v_r^{\mathsf T},\qquad
v_r^{\mathsf T}=(1,r,\ldots,r^{m-1}).
$$

Divide by $f(u)$ and compare two distinct values of $h/f$. The rank-at-most-one matrix $(Ce_r)v_r^{\mathsf T}$ must be scalar. Since $m\ge2$, it must be zero, and $Ce_r=0$. Then $CV=\lambda I_m$. But $Ve_0=\mathbf1$, so $\lambda e_0=C\mathbf1=0$ and $\lambda=0$. The output vanishes throughout the stratum.

Every matrix successful anywhere on (8.1) therefore has a nonzero collinearity polynomial on the open domain $(0,1)\times(\mathbb R^m\setminus\{0\})\times\mathbb R$. The restricted covering principle of Section 3 excludes countable covering. This argument includes globally nonuniversal maps and every selector, not merely the displayed universal maps. $\square$

## 9. The $JJ$ family and the exceptional-source bridge

Fix the word

$$
w_a=M^aJJM^{2m-2-a},\qquad 0\le a\le2m-2.
$$

Let $r=a+1$ and $T=\{0,\ldots,2m\}\setminus\{r\}$. Then

$$
A_r=JM^a,\qquad A_i=M^{k_i}\ (i\in T),\qquad
k_i=\begin{cases}i&i\le a,\\i-2&i\ge a+2.\end{cases}
\tag{9.1}
$$

In particular the same matrix $M^a$ is read at the two different original clocks $a$ and $a+2$.

**Theorem 9.1.** An all-input countable palette on $w_a$ exists if and only if there is a universal identity whose functional, after nonzero scalar normalization, is

$$
L=\rho I+M,\qquad \rho>0.
\tag{9.2}
$$

In that event one matrix succeeds everywhere, with scale $\rho+\operatorname{tr}(MP)>0$.

**Proof.** Every identity has $Ce_r=0$ and $L\in\operatorname{span}\{I,M\}$. The attainable functionals form a linear subspace $\Lambda$ of this plane, since the defining equations are linear in $(C,L)$. Its dimension is at most one. Two independent functionals would span the plane and, by taking the same linear combination of their matrices, yield functional $I$, prohibited by Theorem 4.1 because $A_0=I$. If $\Lambda=0$, Lemma 3.2 applies.

Otherwise write its line as $L=uI+vM$. Both coefficients are nonzero, because $I$ and $M$ occur among the $A_i$ and proportionality to either is prohibited. Put $t=\operatorname{tr}(MP)=b+c+\theta>0$. If $uv>0$, scaling gives (9.2), and its identity succeeds everywhere.

Suppose instead $uv<0$, and put $t_0=-u/v>0$. We prove that the entire stratum $t=t_0$ cannot be rescued by a countable palette. It is realized by positive sources: choose sufficiently small $\theta>0$, and take $b,c$ to be the positive roots with

$$
b+c=t_0-\theta,\qquad bc=\theta(1-\theta).
\tag{9.3}
$$

For a small interval of such $\theta$, the sum is positive and the discriminant $(t_0-\theta)^2-4\theta(1-\theta)$ is positive, by its positive limit $t_0^2$ as $\theta$ tends to zero. Both roots are positive, so (9.3) gives actual legal sources. Choose either continuous root branch on a small interval.

On $T$ all factors are the fixed positive numbers

$$
\alpha_i=F_{k_i-1}+F_{k_i}t_0.
\tag{9.4}
$$

Positivity also follows directly because each $M^{k_i}$ is nonzero and entrywise nonnegative and $P$ is strictly positive. Let $C_0$ be a nonzero universal identity on the line $\Lambda$. Its restriction $C_{0,T}$ has rank $m$, since the exceptional column is zero. At $t=t_0$ it annihilates

$$
B=\operatorname{diag}(\alpha_i)_{i\in T}V_T,
$$

whose image has dimension $m$. This image is precisely its $m$-dimensional kernel. Drift annihilation therefore gives

$$
\mathbf1_T=B\gamma\quad\text{for a fixed }\gamma\ne0.
\tag{9.5}
$$

This is a drift ambiguity on the whole realized $t_0$ stratum, not just at one source.

The outlier factor $q=\operatorname{tr}(JM^aP)$ varies over an interval there. For $a=0$, it is $t_0-\theta$. For $a\ge1$, (2.3) gives

$$
q=F_{a-1}(t_0-\theta)+F_a(1+c).
\tag{9.6}
$$

It cannot be constant on a $\theta$ interval. Constancy would make $c=s\theta+h$, with rational slope $s=F_{a-1}/F_a$. Substitution in $c(t_0-\theta-c)=\theta(1-\theta)$ and comparison of quadratic coefficients gives $s^2+s=1$. Its roots $(-1\pm\sqrt5)/2$ are irrational, a contradiction. Thus continuity and the intermediate value property give a nonempty open interval $Q_0$ of realized $q$ values. No choice of a source section over $Q_0$ is needed; every value is realized and the observations depend only on $q,t_0,\beta,\delta$.

Now suppose any fixed $C$ is collinear for every $q\in Q_0$, every $\beta\ne0$, and every drift. Again $C\mathbf1=0$ and its coefficient map is scalar. Comparing two $q$ values shows $(Ce_r)v_r^{\mathsf T}$ is scalar of rank at most one, hence zero. Thus $Ce_r=0$ and $C_TB=\lambda I_m$. Applying this to (9.5) gives $\lambda\gamma=C_T\mathbf1_T=0$, so $\lambda=0$. Such a $C$ has zero output throughout the stratum.

The observations are polynomial in $(q,\beta,\delta)$ on $Q_0\times(\mathbb R^m\setminus\{0\})\times\mathbb R$. The restricted covering principle now excludes every countable palette, including maps that are not global identities. The zero-line, positive-sign, and opposite-sign cases exhaust $\Lambda$, proving the equivalence. $\square$

## 10. An exact positive clock-interpolation criterion

For $m\ge2$, $0\le a\le2m-2$, and $\rho>0$, keep $r,T,k_i$ from (9.1) and put

$$
w_i=F_{k_i-1}-\rho F_{k_i},\qquad \lambda_i=F_{k_i}\quad(i\in T).
\tag{10.1}
$$

Let $\mathcal D$ be the $2m\times2m$ matrix with rows, in increasing original-clock order,

$$
\bigl(w_i,w_i i,\ldots,w_i i^{m-1},\lambda_i,\lambda_i i,\ldots,\lambda_i i^{m-1}\bigr).
\tag{10.2}
$$

**Theorem 10.1.** For fixed $m$, an all-input countable-palette gain output on some preassigned critical mixed word exists if and only if there are $a,\rho$ as above and $R\in\mathcal P_{m-1}$ such that

$$
w_iR(i)=1\quad\text{for every }i\in T,
\qquad \mathcal D\text{ is invertible}.
\tag{10.3}
$$

This is also the exact criterion for one universal matrix succeeding everywhere on some critical mixed word.

**Proof.** Theorems 4.1–6.2, Proposition 7.1, and Proposition 8.1 leave only a $JJ$ word for fixed-word all-input success. Theorem 9.1 forces $L=\rho I+M$ with $\rho>0$. On $T$,

$$
A_i=w_iI+\lambda_iL.
\tag{10.4}
$$

The trace functionals represented by $I,L$ are independent. The identity therefore implies

$$
C_T\operatorname{diag}(w)V_T=0,\qquad
C_T\operatorname{diag}(\lambda)V_T=I_m.
\tag{10.5}
$$

Every $w_i$ is nonzero, since otherwise $A_i$ would be proportional to $L$. The first block in (10.5) has rank $m$. The second also has rank $m$, and the two images intersect trivially: applying $C_T$ to a vector in their intersection gives zero from the first representation and its full coefficient vector from the second. Thus the concatenated matrix $\mathcal D$ is invertible. The first image is exactly $\ker C_T$. Drift annihilation is equivalent to $\mathbf1_T$ belonging to that image, which is precisely the polynomial condition in (10.3).

Conversely, (10.3) implies all $w_i\ne0$. Acquire the word $M^aJJM^{2m-2-a}$ with every required immediate read. Set the outlier column to zero and define the fixed matrix

$$
C_T=[\,0_{m\times m}\ \ I_m\,]\mathcal D^{-1}.
\tag{10.6}
$$

For the actual normalized source, (10.4) gives

$$
Z_T=\operatorname{diag}(w)V_T\beta+
\operatorname{diag}(\lambda)V_T
\bigl((\rho+\operatorname{tr}(MP))\beta\bigr)+\delta\mathbf1_T.
$$

The polynomial condition puts the drift in the first-block image. Hence

$$
CZ=(\rho+\operatorname{tr}(MP))\beta\ne0.
\tag{10.7}
$$

All entries of $C$ depend only on $m,a,\rho$. Every original clock, including the ignored outlier read, is acquired. Positivity of the scale does not require a generic source, nonvanishing sampled polynomial, particular sign of a coefficient, or a spectral restriction. This proves sufficiency. $\square$

Subtracting $\rho$ times each second-block column from the corresponding Fibonacci-previous column shows that $\det\mathcal D$ is independent of $\rho$. This identity is not a feasibility decision. Both parts of (10.3), including the positive parameter and the low-degree interpolation on the repeated-state clocks, are required for a construction. Section 13 excludes interpolation itself for $m=3,4$ and excludes even unrestricted-sign $JJ$ identities for $m=2$. These arguments make no assertion that $\mathcal D$ is singular.

For $m\ge5$, existence of a positive solution of (10.3) remains unresolved here. A positive solution gives the explicit conditional construction (10.6); nonexistence at a particular $m$ would, together with the prior upper construction, make $2m+2$ the sharp fixed mixed threshold at that $m$. No conclusion about adaptive choice among multiple words follows merely from having an obstruction for each individual word: exceptional failure sets for different words need not coincide.

## 11. The earlier mixed obstruction, with its precise scope

The following prior supplied result supplies the budgets below the critical one.

**Theorem 11.1.** A mixed word with $N\le2m$ reads has no nonzero identity. Consequently finitely many such words cannot support all-input countable-palette gain extraction.

**Proof.** A nonzero identity gives $\operatorname{rank}C=m$ and $\dim\ker C=N-m$. If $N<m$, it is already impossible. Put $E=\ker\operatorname{tr}(L\,\cdot)$ and $Q=\{i:A_i\propto L\}$, of size $q$. As before, choose $S\in E$ whose factor vector is nonzero exactly off $Q$. Then the nuisance image in $\ker C$ has dimension $\min(N-q,m)$. Also $q\le\lceil N/2\rceil\le m$ by nonadjacency.

If $q>0$, the nuisance image vanishes on $Q$ and $\mathbf1$ does not. Hence

$$
N-m\ge\min(N-q,m)+1.
$$

If $N-q\ge m$, this forces $N\ge2m+1$. Otherwise it forces $q\ge m+1$. Both are impossible.

If $q=0$, the nuisance image has dimension $m$, so $N\ge2m$ and therefore $N=2m$. It equals $\ker C$. For every $T\in E$, the diagonal ratios $a_i(T)/a_i(S)$ preserve $U$, and hence are scalar by Section 2. Thus $a(E)$ has dimension at most one and the full cumulative-matrix span at most two, contradicting mixedness. Lemma 3.2 gives the palette consequence. $\square$

This theorem concerns gain outputs on mixed terminal words. The assertion that complete-target protocols have only mixed terminal words requires the separate indistinguishability proof in Section 15. It is not an assertion about all adaptive gain-only protocols.

## 12. Credited Hermite obstruction and the fixed-acquisition threshold

Define

$$
\phi=\frac{1+\sqrt5}{2},\qquad \psi=\frac{1-\sqrt5}{2}=-\phi^{-1},
\qquad
\Pi_+=\frac{M-\psi I}{\phi-\psi},\quad
\Pi_-=\frac{\phi I-M}{\phi-\psi}.
\tag{12.1}
$$

The characteristic identity makes these complementary rank-one projectors and gives

$$
M^i=\phi^i\Pi_++\psi^i\Pi_-,\qquad
\alpha(S)=\operatorname{tr}(\Pi_+S),\quad
\eta(S)=\operatorname{tr}(\Pi_-S).
\tag{12.2}
$$

For legal $P$, $\alpha(P)>0$ because $\Pi_+$ is strictly entrywise positive, and $\alpha(P)+\eta(P)=1$. No positivity or nonvanishing of $\eta$ is assumed. The two auxiliary functionals are independent, as evaluation on the projectors gives $(1,0)$ and $(0,1)$.

For $D=x\,d/dx$ and $f(x)=\sum_i c_ix^i$,

$$
(D^jf)(\lambda)=\sum_i c_i i^j\lambda^i,\qquad
((D+1)^jf)(\lambda)=\sum_i c_i(i+1)^j\lambda^i.
\tag{12.3}
$$

Both operators act diagonally on monomials. Their order-$j$ leading derivative term is $x^jf^{(j)}$, by induction, so at a nonzero node their jets through order $d$ are invertible triangular transforms of ordinary derivative jets. In particular homogeneous vanishing is precisely root multiplicity at least $m$.

**Theorem 12.1 (prior pure-$M$ obstruction).** At most $2m$ pure-$M$ reads admit no nonzero identity.

**Proof.** Pad with further $M$ actions and zero output columns to reach $N=2m$. Since the factor sequence is $\alpha(S)\phi^i+\eta(S)\psi^i$, the functional must vanish on $\ker\alpha\cap\ker\eta$ and thus equal $u\alpha+v\eta$, with $(u,v)\ne(0,0)$. For row $k$ of $C$ let $f_k(x)=\sum_{i=0}^{2m-1}C_{ki}x^i$. The identity says

$$
f_k(1)=0,\qquad
(D^jf_k)(\phi)=u\delta_{jk},\qquad
(D^jf_k)(\psi)=v\delta_{jk}\quad(0\le j,k\le d).
\tag{12.4}
$$

Let $H_\phi$ be the unique degree-at-most-$(2d+1)$ polynomial with value one at $\phi$, zero at $\psi$, and derivatives of orders $1,\ldots,d$ zero at both. Existence and uniqueness follow because the homogeneous square Hermite system would give $2m$ roots counted with multiplicity in degree at most $2m-1$. Set $H_\psi=1-H_\phi$. Jet triangularity gives $f_0=uH_\phi+vH_\psi$.

The derivative $H_\phi'$ has degree at most $2d$ and zeros of multiplicity at least $d$ at both endpoints. Its integral from $\psi$ to $\phi$ is one. Therefore

$$
H_\phi'(x)=c(x-\psi)^d(\phi-x)^d,\qquad c>0\quad(\psi<x<\phi).
$$

This positive density is symmetric about $(\phi+\psi)/2=1/2$. Since $\psi<1<\phi$ and $1>1/2$, we have $1/2<H_\phi(1)<1$ and $0<H_\psi(1)<1/2$. The drift equation $f_0(1)=0$ forces $u\ne0$ and

$$
\frac vu=-\frac{H_\phi(1)}{H_\psi(1)}<-1.
\tag{12.5}
$$

For the highest row, the lower jets vanish at both nodes, so

$$
f_d(x)=(x-\phi)^d(x-\psi)^d(ax+b).
$$

Its zero at $1$ gives $b=-a$. The order-$d$ jets yield

$$
u=d!\phi^d(\phi-\psi)^d a(\phi-1),\qquad
v=d!\psi^d(\psi-\phi)^d a(\psi-1).
$$

Since $u\ne0$, $a\ne0$, and $\phi-1=\phi^{-1}$, $\psi-1=-\phi$. Thus

$$
\frac vu=\left(\frac{-\psi}{\phi}\right)^d
\frac{\psi-1}{\phi-1}=-\phi^{2-2d}\in[-1,0)
\quad(d\ge1),
$$

contrary to (12.5). $\square$

**Lemma 12.2 (square interpolation).** Arbitrary Euler jets through order $d$ at $\phi,\psi$ and a value at $1$ specify a unique polynomial of degree at most $2m$. The same holds for $D+1$ jets.

**Proof.** There are $2m+1$ coefficients and conditions. In the homogeneous system, triangularity gives roots of multiplicity $m$ at both spectral nodes and a root at the distinct node $1$. A nonzero polynomial would have degree at least $2m+1$, impossible. The linear map is injective between equal finite dimensions and hence bijective. $\square$

**Theorem 12.3 (prior exact gain and drift).** The pure word $M^{2m}$ recovers $\beta$ and $\delta$ exactly by fixed linear maps in $2m+1=2d+3$ reads.

**Proof.** For $0\le k\le d$, choose $f_k^+,f_k^-\in\mathcal P_{2m}$ by Lemma 12.2 with value zero at $1$ and jets

$$
(D^jf_k^+)(\phi)=\delta_{jk},\quad(D^jf_k^+)(\psi)=0,
\qquad
(D^jf_k^-)(\phi)=0,\quad(D^jf_k^-)(\psi)=\delta_{jk}.
$$

The coefficient-weighted read sums are respectively $U_k=\alpha(P)\beta_k$ and $W_k=\eta(P)\beta_k$, by (12.3). Hence $U+W=\beta$. For $Q(x)=x^2-x-1$, the polynomial $f_\delta=(-1)^mQ^m$ has value one at $1$ and multiplicity-$m$ zeros at both spectral nodes. Its coefficient-weighted sum is exactly $\delta$. This proves both outputs on every world, including $\eta=0$ and every degree drop. $\square$

**Corollary 12.4 (prior sharp unrestricted-word fixed acquisition).** The sharp fixed-acquisition gain-ray threshold is $2d+3$, even with countable palettes.

**Proof.** Theorem 12.3 gives the upper bound. Below it, Theorem 11.1 excludes mixed words and Theorem 12.1 excludes pure-$M$ words, in both cases by Lemma 3.2. On a pure-$J$ word use

$$
P_*=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix}.
$$

The worlds $(P_*,t,0)$ and $(P_*,t+1,-1)$ have the same reads $z_i=i$ at every clock because $JP_*=P_*$. Their full coefficient vectors are noncollinear for every $d\ge1$. No selector, even nonlinear, can return a nonzero ray valid for both. This also covers the empty word. For early stopping on a preassigned word, pad every earlier matrix with zero columns to its final prescribed length; the palette remains countable. $\square$

## 13. Positive interpolation obstructions and sharp mixed thresholds in degrees one through three

**Theorem 13.1.** For $d=1$, the sharp fixed mixed-acquisition gain-ray threshold is six reads, even with arbitrary countable fixed-matrix selection.

**Proof of the lower bound.** Theorem 11.1 excludes at most four reads. At five reads, $m=2$, the critical classification excludes every word except the families (6.2). Edge-$J$ words have no identity. Predominantly-$J$ words have no all-input countable palette, by Proposition 8.1.

A $JJ$ word has no nonzero identity at all when $m=2$. Indeed, normalize any possible functional $uI+vM$ by $v\ne0$ and write $L=\rho I+M$, now allowing either sign of $\rho$. The necessity proof of (10.3) applies to this identity without the positive-sign requirement. At the two clocks $a,a+2$, $w$ is the same and nonzero. A polynomial $R$ of degree at most one satisfying $w_iR(i)=1$ therefore has $R(a)=R(a+2)$ and is constant. Hence every $w_i$ has the same nonzero value. The exponents on $T$ include $0,1,2$. Writing $W(k)=F_{k-1}-\rho F_k$ to distinguish exponent from clock, their values obey $W(2)=W(1)+W(0)$ by the Fibonacci recurrence. Three equal nonzero values cannot satisfy this relation. Lemma 3.2 excludes countable palettes on these words. These cases exhaust all critical mixed words.

The fixed mixed upper bound of six reads is the $m=2$ instance of Theorem 14.1 below. Padding earlier outputs with zero columns also covers early stopping on a preassigned mixed word. $\square$

This result does not contradict the five-read pure-$M$ exact gain output. The extra read concerns the requirement that the fixed acquisition word contain both letters.

For the remaining proofs put $p=\rho>0$ and distinguish exponent from original clock by writing

$$
u_k=F_{k-1}-pF_k,\qquad
u_0=1,\quad u_1=-p,\quad u_{k+2}=u_{k+1}+u_k.
\tag{13.1}
$$

Thus $u_2=1-p$, $u_3=1-2p$, $u_4=2-3p$, $u_5=3-5p$, and $u_6=5-8p$, by successive symbolic substitution. The interpolation part of (10.3) says exactly

$$
R(k)=1/u_k\quad(0\le k\le a),\qquad
R(k+2)=1/u_k\quad(a\le k\le2m-2).
\tag{13.2}
$$

Every $u_k$ in this range must be nonzero. These are equations at the original clocks in $T$, with the outlier $a+1$ still acquired. In particular $R(a)=R(a+2)=1/u_a$. Translations or scalar multiples of $R$ below are auxiliary polynomial consequences of (13.2), not changes to acquisition clocks.

**Lemma 13.2 (Q: quadratic obstruction at every gap).** For $m=3$, every $0\le a\le4$ and every $p>0$, no $R\in\mathcal P_2$ satisfies (13.2).

**Proof.** Suppose otherwise. Writing $R(t)=At^2+Ct+D$ and subtracting its equal values at $a,a+2$ gives $C=-2A(a+1)$. Hence

$$
R(t)=A(t-a-1)^2+B.
$$

This includes the constant and lower-degree cases. For $1\le a\le3$, clocks $a-1,a+3$ are both retained and symmetric about $a+1$. Their exponents are $a-1,a+1$, so equality of their values and nonzero denominators give $u_{a-1}=u_{a+1}$. The recurrence $u_{a+1}=u_a+u_{a-1}$ forces $u_a=0$, contradicting (13.2).

At $a=0$, $R(0)=R(2)=1$, so $R(t)=1+ct(t-2)$. At clock $3$, exponent $1$, this gives $1+3c=-1/p$, whence $c=-(p+1)/(3p)$. The next two retained clocks give

$$
R(4)=-\frac{5p+8}{3p}=\frac1{1-p},\qquad
R(5)=-\frac{4p+5}{p}=\frac1{1-2p}.
$$

The denominators are nonzero under the candidate assumptions. Multiplying the two equalities gives, respectively,

$$
5p^2=8,\qquad 8p^2+5p-5=0.
$$

Substituting the first into the second gives $39/5+5p=0$, impossible for $p>0$.

At $a=4$, the equal values at clocks $4,6$ put the axis at $5$. Since $R(0)=1$, write $R(t)=1+ct(t-10)$. The clock-$1$ equation gives $c=(p+1)/(9p)$. Clocks $2,3$ still have exponents $2,3$, so

$$
R(2)=-\frac{7p+16}{9p}=\frac1{1-p},\qquad
R(3)=-\frac{4p+7}{3p}=\frac1{1-2p}.
$$

These imply $7p^2=16$ and $8p^2+7p-7=0$. Together they give $79/7+7p=0$, again impossible. The interior cases and these two edges exhaust every gap. No determinant hypothesis was used. $\square$

**Lemma 13.3 (L: six consecutive reciprocal Fibonacci values).** Suppose $p>0$, $u_0=1,u_1=-p$, and $u_{k+2}=u_{k+1}+u_k$, with $u_0,\ldots,u_5$ nonzero. No $H\in\mathcal P_3$ satisfies $H(j)=1/u_j$ for $0\le j\le5$.

**Proof.** The fourth forward difference of a cubic is zero, since taking a difference lowers the degree of a nonconstant polynomial by one. At nodes $0,\ldots,4$ it would give

$$
\frac1{2-3p}-\frac4{1-2p}+\frac6{1-p}+\frac4p+1=0.
$$

Multiplication by the nonzero product $p(1-p)(1-2p)(2-3p)$ and expansion yields $\mathscr P(p)=0$, where

$$
\mathscr P(x)=-6x^4+15x^3+18x^2-29x+8.
\tag{13.3}
$$

For completeness the five products before collection are

$$
\begin{aligned}
&p(1-p)(1-2p),\\
&-4p(1-p)(2-3p),\\
&6p(1-2p)(2-3p),\\
&4(1-p)(1-2p)(2-3p),\\
&p(1-p)(1-2p)(2-3p).
\end{aligned}
$$

Put $q=(1-p)/p$ and $v_j=u_{j+1}/u_1$. Then $v_0=1,v_1=-q$ and $v$ has the same recurrence. The polynomial $u_1H(t+1)$ takes values $1/v_j$ at $j=0,\ldots,4$, so the same difference identity gives $\mathscr P(q)=0$. This identity does not require $q>0$: all its denominators are nonzero because $v_0,\ldots,v_4$ are nonzero scalar multiples of $u_1,\ldots,u_5$. In particular $q=0$ and the other poles cannot occur.

Here are the sign bounds needed to exclude simultaneous roots. On $[0,1/2]$,

$$
\mathscr P''(x)=-72x^2+90x+36\ge54x+36>0,
\qquad \mathscr P'(1/2)=-11/4<0.
$$

The inequality uses $x^2\le x/2$. Thus $\mathscr P'$ is increasing but negative on this interval, and $\mathscr P$ is strictly decreasing there. Direct substitution gives

$$
\mathscr P(1/3)=22/27>0,\qquad
\mathscr P(3/7)=-346/2401<0.
$$

For $0\le z\le1$, using $z^4,z^3\le z^2$ gives

$$
\begin{aligned}
\mathscr P(-z)&=-6z^4-15z^3+18z^2+29z+8
 \ge-3z^2+29z+8>0,\\
\mathscr P(1+z)&=6+28z+27z^2-9z^3-6z^4
 \ge6+28z+12z^2>0.
\end{aligned}
$$

For the first strict inequality, $29z-3z^2\ge26z\ge0$. Hence $\mathscr P>0$ on both $[-1,0]$ and $[1,2]$. On $[2/3,1]$ we instead use $x^2\le x$ to get

$$
\mathscr P''(x)\ge18x+36>0,\qquad
\mathscr P'(2/3)=71/9>0,\qquad
\mathscr P(7/10)=561/2500>0.
$$

Consequently $\mathscr P$ is strictly increasing on that interval.

We now cover every allowed positive $p$.

* If $0<p<1/2$, strict decrease and $\mathscr P(1/3)>0$ make $\mathscr P(p)=0$ imply $p>1/3$. Then $1<q<2$, contradicting $\mathscr P(q)=0$.
* If $1/2<p<2/3$, the five denominators $u_0,\ldots,u_4$ have signs $+,-,+,-,+$. The same holds for their reciprocals. By the intermediate value property, $H$ has a root in each of $(0,1),(1,2),(2,3),(3,4)$. These are four distinct roots, impossible for a nonzero cubic; $H(0)=1$ excludes the zero polynomial.
* If $2/3<p<1$, strict increase and $\mathscr P(7/10)>0$ force $p<7/10$. Therefore $3/7<q<1/2$. Strict decrease on $[0,1/2]$ and $\mathscr P(3/7)<0$ give $\mathscr P(q)<0$, a contradiction.
* If $p>1$, then $-1<q<0$, where $\mathscr P(q)>0$.

The boundary parameters $p=1/2,2/3,1$ are forbidden by $u_3=0,u_4=0,u_2=0$, respectively. The possible zero $u_5=0$ at $p=3/5$ is already forbidden by hypothesis, including in the alternating-sign case. These intervals and boundaries exhaust all $p>0$. $\square$

**Lemma 13.4 (S: centered cubic obstruction).** For $m=4$ and $2\le a\le4$, no $R\in\mathcal P_3$ satisfies (13.2). This statement holds even for real $p$ of either sign whenever all required denominators are nonzero.

**Proof.** Put $r=a+1$, $u=u_a$, and $v=u_{a-1}$. The six retained original clocks

$$
r-3,r-2,r-1,r+1,r+2,r+3
$$

lie in $0,\ldots,8$ and have respective exponents $a-2,a-1,a,a,a+1,a+2$. Their denominators, by the recurrence, are

$$
u-v,\quad v,\quad u,\quad u,\quad u+v,\quad 2u+v,
$$

all nonzero. The equal values at $r-1,r+1$ force

$$
R(r+x)=\frac1u+b(x^2-1)+h(x^3-x).
\tag{13.4}
$$

Indeed the coefficients of $x^3$ and $x$ in the odd part must sum to zero, and the even part at $x=1$ must equal $1/u$. This also includes every degree drop.

Taking differences at $x=\pm2$ and $x=\pm3$ gives

$$
12h=\frac1{u+v}-\frac1v=-\frac{u}{v(u+v)},\qquad
48h=\frac1{2u+v}-\frac1{u-v}
=-\frac{u+2v}{(u-v)(2u+v)}.
$$

Set $t=v/u$. Every divisor just used is nonzero. Comparing the two equations yields

$$
t(1+t)(1+2t)=4(1-t)(2+t),\qquad
2t^3+7t^2+5t-8=0.
\tag{13.5}
$$

Now put $S_2=1/v+1/(u+v)$ and $S_3=1/(u-v)+1/(2u+v)$. The sums from (13.4) give $S_2=2/u+6b$ and $S_3=2/u+16b$. Thus $8S_2-3S_3-10/u=0$, or, after multiplying by $u$,

$$
\frac{8(1+2t)}{t(1+t)}-
\frac9{(1-t)(2+t)}-10=0.
\tag{13.6}
$$

Write $H=t(1+t)$ and $G=(1-t)(2+t)$; both are nonzero. Equation (13.5) gives $H(1+2t)=4G$. Multiplying (13.6) by $HG$, substituting $G=H(1+2t)/4$, dividing by $H$, and multiplying by two gives

$$
4(1+2t)^2-18-5H(1+2t)=0,
\qquad 10t^3-t^2-11t+14=0.
\tag{13.7}
$$

Five times the last polynomial of (13.5) minus the last polynomial of (13.7) is $36t^2+36t-54=0$, so $H=3/2$. The polynomial in (13.5) also equals $2tH+5H-8$. It then gives $3t-1/2=0$, so $t=1/6$. But $t(t+1)=7/36\ne3/2$, a contradiction. This proof neither assumes positive $p$ nor makes any determinant claim. $\square$

**Theorem 13.5 (C: cubic obstruction at every gap).** For $m=4$, every $0\le a\le6$ and every $p>0$, no $R\in\mathcal P_3$ satisfies (13.2).

**Proof.** At $a=0$, the retained original clocks $2,\ldots,7$ have exponents $0,\ldots,5$. The auxiliary polynomial $H(t)=R(t+2)$ contradicts Lemma 13.3. At $a=5$ or $a=6$, the retained original clocks $0,\ldots,5$ still have exponents $0,\ldots,5$, so $R$ itself contradicts that lemma. Lemma 13.4 excludes $2\le a\le4$.

It remains to handle $a=1$, including the positivity condition needed for a shifted use of Lemma 13.3. Clocks $1,3$ have exponent $1$ and $R(1)=R(3)=-1/p$. With $x=t-2$ the centered cubic must have the form

$$
R(2+x)=A(x^3-x)+B(x^2-1)-1/p.
\tag{13.8}
$$

The retained clocks $0,4$ have exponents $0,2$. Their equations $R(0)=1$, $R(4)=1/(1-p)$ give

$$
-6A+3B=1+1/p,\qquad
6A+3B=1/(1-p)+1/p,
$$

and hence

$$
A=\frac{p}{12(1-p)},\qquad
B=\frac{2-p^2}{6p(1-p)}.
$$

Here $p$ and $1-p$ are nonzero by hypothesis. At retained clock $5$, exponent $3$, equation (13.8) becomes

$$
R(5)=\frac{2p^2+3p+5}{3p(1-p)}=\frac1{1-2p}.
$$

Multiplication by nonzero denominators gives

$$
4p^3+p^2+10p-5=0.
\tag{13.9}
$$

For $p\ge1$ its left side is at least $4+1+10-5=10>0$. Thus a candidate has $0<p<1$, making $q=(1-p)/p>0$. The retained original clocks $3,\ldots,8$ have exponents $1,\ldots,6$. Define $v_j=u_{j+1}/u_1$ and the auxiliary polynomial $H(t)=u_1R(t+3)$. Then $v_0=1,v_1=-q$, $v$ follows the same recurrence, its first six entries are nonzero, and $H(j)=1/v_j$ for $0\le j\le5$. Lemma 13.3 with the now verified positive parameter $q$ is a contradiction. The cases $a=0$, $a=1$, $2\le a\le4$, and $5\le a\le6$ exhaust every cubic gap. $\square$

**Corollary 13.6 (sharp fixed mixed thresholds).** On the full domain of Section 1, the least read count for a preassigned mixed acquisition word admitting all-input full-gain-ray output by an arbitrary countable palette is six, eight, and ten for $d=1,2,3$, respectively.

**Proof.** Theorem 11.1 and Lemma 3.2 exclude mixed words with $N\le2m$. At $N=2m+1$, Theorem 13.1 handles $m=2$. For $m=3,4$, Theorem 10.1 is the exact fixed-word existence criterion, including the exceptional-source palette arguments in Sections 8–9. Lemma 13.2 and Theorem 13.5 exclude its interpolation requirement for every $a$ and every $\rho>0$, even before invertibility of $\mathcal D$ is considered. Thus every preassigned critical mixed word fails all-input countable-palette extraction. In particular this conclusion does not assert that every such word lacks an unrestricted-sign identity: an identity with an exceptional zero scale would still require the palette analysis already proved.

Theorem 14.1 gives one all-input map on $JM^{2m}$ with $2m+2=2d+4$ reads and strictly positive scale $\operatorname{tr}(JP)$. For the three degrees the upper words are $JM^4,JM^6,JM^8$. Every action is immediately read and the initial read is counted. Padding early outputs with zero columns while finishing a preassigned word preserves countability and does not evade the lower bound. This proves sharpness for fixed mixed acquisition only. Separate failures on different words do not imply an adaptive gain-only or complete-target lower bound in degrees two or three. $\square$

## 14. The credited nonvanishing mixed upper construction

**Theorem 14.1.** For every declared $d\ge1$, the word $JM^{2m}$ gives one all-input fixed gain map in $2m+2=2d+4$ reads, with output $\operatorname{tr}(JP)\beta$.

**Proof.** Acquire one $J$ and then $2m$ separate $M$ actions, with every immediate read and the initial read. At original clock $s+1$,

$$
A_{s+1}=M^sJ,\qquad
z_{s+1}=\bigl(\alpha'\phi^s+\eta'\psi^s\bigr)g(s+1)+\delta,
$$

where $\alpha'=\operatorname{tr}(\Pi_+JP)$ and $\eta'=\operatorname{tr}(\Pi_-JP)$. Their sum is $\operatorname{tr}(JP)=P_{12}+P_{21}>0$.

For each $0\le k\le d$ choose $h_k(x)=\sum_{s=0}^{2m}b_{ks}x^s$ with

$$
h_k(1)=0,\qquad
((D+1)^jh_k)(\phi)=((D+1)^jh_k)(\psi)=\delta_{jk}
\quad(0\le j\le d).
$$

Lemma 12.2 proves existence and uniqueness for all these prescribed conditions. Equation (12.3), with the actual factor $(s+1)^j$ from $g(s+1)$, gives

$$
\sum_{s=0}^{2m}b_{ks}z_{s+1}=(\alpha'+\eta')\beta_k.
$$

Clock zero has output coefficient zero but is acquired. The scale is strictly positive, with no condition on the actual degree, sampled roots, coefficient signs, drift, or $\eta'$. Polynomial exponents specify coefficients on original clocks; they do not reindex acquisition. This is a gain construction, not a claim of complete-target recovery on this word. $\square$

Combining Sections 10–14, the fixed mixed threshold at any $m$ is $2m+1$ if (10.3) has a positive solution and $2m+2$ otherwise. Its $m=2,3,4$ nonexistence is established in Section 13, giving the sharp fixed mixed thresholds six, eight, and ten. For $m\ge5$ the criterion remains unresolved. The prior pure-$M$ threshold is already $2m+1$ at every $m$.

## 15. Complete-target protocols and the degree-one adaptive consequence

**Lemma 15.1 (prior pure-terminal bridge).** A deterministic protocol correct for the complete target on the whole domain cannot terminate on a pure word, including the empty word.

**Proof.** For $A=M$ or $J$, all powers lie in $\operatorname{span}\{I,A\}$. Write any legal source as $P=uv^{\mathsf T}$ with $u,v>0$ and $v^{\mathsf T}u=1$. If $u,Au$ are independent, perturb $u$ slightly to a nonproportional positive $u'$ and solve

$$
(v')^{\mathsf T}u'=1,\qquad
(v')^{\mathsf T}Au'=v^{\mathsf T}Au.
$$

The coefficient matrix stays invertible nearby, and the solution is continuous and positive near $v$. The new column line makes $u'(v')^{\mathsf T}\ne P$. If $Au=\lambda u$, keep $u$ and vary positive $v$ along $v^{\mathsf T}u=1$; the $A$ trace remains $\lambda$, and the source changes. In either case there is a distinct legal source with the same traces against all powers of $A$, hence identical pure reads with the same $g,\delta$. By determinism the alternative world follows the same actual choices and terminal decision. The same complete target cannot be correct for both. On the empty word, $z_0=g(0)+\delta$ is independent of $P$. $\square$

Together with Theorem 11.1 and Lemma 3.2 this gives the prior lower bound of $2d+3$ reads for complete-target recovery required also to deliver (1.3) by countable palettes.

For $d=1$, a stronger argument is available. Separate all-input obstructions for different fixed words alone do not prove an adaptive obstruction. We instead exclude the two words that admit identities on one common open source set.

**Theorem 15.2.** No deterministic protocol on the full degree-one domain can recover $(P,g,\delta)$ in at most five reads while also producing a nonzero full gain ray by a countable palette per terminal word. Thus six reads is a lower bound for this complete-target mechanism.

**Proof.** Consider the nonempty open source set in chart (2.5) given by

$$
\frac12<\theta<1,\qquad 0<c<2\theta-1,\qquad
b=\theta(1-\theta)/c.
\tag{15.1}
$$

For the critical word $J^3M$, all cumulative matrices lie in $\operatorname{span}\{I,J,MJ\}$. Its source traces are determined by $1,b+c,1+b$, independent of the allocation of the two diagonal entries. The distinct positive source

$$
\widetilde P=\begin{pmatrix}\theta&b\\c&1-\theta\end{pmatrix}
$$

has the same determinant zero, trace one, and all these traces. With the same $g,\delta$, it has exactly the same word history. A correct complete-target protocol therefore cannot terminate on $J^3M$ at any world of (15.1).

For $MJ^3$, all cumulative matrices lie in $\operatorname{span}\{I,M,JM\}$, with traces determined by $1,b+c+\theta,1+c$. Put

$$
\theta'=1+c-\theta,\qquad
b'=\theta'(1-\theta')/c,\qquad
P'=\begin{pmatrix}1-\theta'&b'\\c&\theta'\end{pmatrix}.
$$

Condition (15.1) gives $0<\theta'<\theta<1$, so $P'$ is legal and distinct. Also

$$
b+\theta=\frac{\theta(1+c-\theta)}c
=\frac{\theta\theta'}c
=b'+\theta'.
$$

Thus $P'$ has the same three traces and, with the same $g,\delta$, the same complete word history. The protocol cannot terminate on $MJ^3$ anywhere on (15.1), either. In both arguments, identical histories force the same adaptive action sequence inductively, so the source ambiguity applies to actual terminal branches.

Pure terminal words are impossible by Lemma 15.1. Every remaining mixed terminal word of at most four reads has no identity by Theorem 11.1. At five reads every remaining mixed word has no identity by the critical classification and the degree-one $JJ$ proof; the only identity-bearing words were $J^3M$ and $MJ^3$.

Restrict now to (15.1), all $\beta\ne0$, and all $\delta$. This is a nonempty open parameter domain. For each remaining word and each matrix successful somewhere, Lemma 3.1 supplies a nonzero collinearity polynomial on the full source chart. Equivalently use (2.5) and multiply denominators by $c$: a polynomial identically zero in this chart would give global collinearity and a prohibited identity. A nonzero polynomial cannot vanish on the open set (15.1). Its zero set is nowhere dense there. There are finitely many terminal words of at most five reads and countably many matrices per word. Since a correct protocol can use neither of the two ambiguous words on this set, successful processing of every world would require countable covering by these remaining nowhere dense sets, contradicting Section 3. $\square$

Theorem 15.2 is a complete-target lower bound with the gain-output contract (1.3). It is not a lower bound for unrestricted nonlinear complete recovery and not a six-read adaptive gain-only lower bound. The exact complete-target threshold, even with this mechanism, is not determined by the six-read mixed gain construction.

## 16. Complete-target upper bounds and their exact scopes

**Theorem 16.1 (prior root-aware recovery).** Every world admits deterministic complete recovery within $4d+5$ reads, with exactly $\beta$ as a fixed linear gain output for each terminal word.

**Proof.** First acquire the $2m+1$ pure-$M$ reads of Theorem 12.3, obtaining $\beta,\delta,U,W$. Choose the least index $k$ with $\beta_k\ne0$ and obtain

$$
\alpha(P)=U_k/\beta_k,\qquad
\operatorname{tr}(MP)=\phi\alpha(P)+\psi(1-\alpha(P)).
$$

This divides by a verified nonzero coefficient. The whole polynomial $g$ is now known. Let $C_0=M^{2m}$ and $B=JC_0$.

Take one $J$ action and its read, reaching $B$. At that original clock $i$, if $g(i)\ne0$, recover $\operatorname{tr}(BP)=(z_i-\delta)/g(i)$. If $g(i)=0$, take two separate $J$ actions with both immediate reads, returning to $B$, and try again. Once successful, take one $M$ and its read, reaching $MB$. Use the same rule there: a nonzero $g(i)$ gives $\operatorname{tr}(MBP)$, and on a zero two separate $J$ actions and reads return to $MB$ for another attempt.

Each failed attempt is a distinct clock that is a root of the same nonzero polynomial. If its actual degree is $s$, there are at most $s\le d$ such failures across both phases together. A nonzero polynomial has this root bound by successive division by distinct linear factors. Thus both phases terminate. Their two first attempts cost two actions and reads, and every failure adds two more. The total is

$$
(2m+1)+2+2f=2d+5+2f\le4d+5.
$$

Return reads are counted. Repeated root multiplicity and roots at unused return reads do not affect this bound, and no division by an unchecked polynomial value occurs.

The recovered traces determine $P$. Right multiplication of the basis $I,M,J,MJ$ by the invertible $C_0$ gives $C_0,MC_0,B,MB$. Right multiplication preserves $\operatorname{span}\{I,M\}$ bijectively by (2.2), so $I,M,B,MB$ are a basis. Their known trace pairings are $1,\operatorname{tr}(MP),\operatorname{tr}(BP),\operatorname{tr}(MBP)$. Nondegeneracy of the trace pairing gives a unique matrix, and the actual legal source is that solution. Together with the known $g,\delta$ this is complete recovery.

Pad the fixed gain matrix from the initial pure-$M$ segment by zero columns. For each terminal word it is one fixed matrix returning exactly $\beta$. The uniform finite bound leaves finitely many such words. Subsequent coefficient selection, polynomial-value tests, adaptive actions, and source reconstruction do not make the gain matrix data-dependent. $\square$

**Theorem 16.2 (supplied moving-trace recovery).** Let $s=\deg g$, with $0\le s\le d$. Every world admits deterministic complete-target recovery in at most

$$
2d+s+5\le3d+5
\tag{16.1}
$$

total reads, with exactly the full $\beta$ returned by one fixed matrix per terminal word.

**Proof.** First perform the pure prefix $M^{2m}$ of Theorem 12.3. Its $2m+1=2d+3$ reads give the entire $g$, $\delta$, and $\operatorname{tr}(MP)$ by the coefficient division already justified in Theorem 16.1. Put $C_0=M^{2m}$ and $B=JC_0$. Perform one $J$, then individual $M$ actions, reading after every action. The continuation matrices and original clocks are

$$
M^pB,\qquad n_p=2m+1+p,\qquad p=0,1,\ldots.
\tag{16.2}
$$

Stop as soon as two continuation reads have nonzero sampled gain. At each such read retain $(z_{n_p}-\delta)/g(n_p)=\operatorname{tr}(M^pBP)$. At a zero gain retain the mandatory read and continue with one $M$. Among $s+2$ consecutive continuation clocks at most $s$ are roots of the nonzero polynomial, so at least two are useful. The protocol need not know $s$ in advance. Repeated roots and roots at other clocks do not increase this count.

Any two distinct useful indices $p<q$ suffice. Indeed $I,M,J,MJ$ are a basis by Section 2. Right multiplication by the invertible $C_0$ preserves $\operatorname{span}\{I,M\}$ bijectively, so $I,M,B,MB$ are a basis. The matrices $M^p,M^q$ are independent: applying a putative relation $aM^p+bM^q=0$ to the two spectral eigenspaces gives $a+b\phi^{q-p}=a+b\psi^{q-p}=0$; the two powers are distinct since $\phi>1>|\psi|$. Thus their coordinate rows in the basis $I,M$ form an invertible matrix. Multiplication on the right by $B$ proves that replacing $B,MB$ by $M^pB,M^qB$ preserves the four-matrix basis. The known trace pairings with this basis are

$$
1,\quad \operatorname{tr}(MP),\quad
\operatorname{tr}(M^pBP),\quad \operatorname{tr}(M^qBP).
\tag{16.3}
$$

The nondegenerate trace pairing gives exactly the actual $P$. Every divided gain was checked nonzero. Together with the calibrated $g,\delta$, this recovers the complete target.

The prefix costs $2d+3$ reads and the continuation at most $s+2$, proving (16.1). If $q$ is the second useful index the terminal word is $M^{2m}JM^q$, and its gain matrix is the fixed prefix matrix of Theorem 12.3 padded with zero columns. It returns exactly the full declared vector $\beta$, including its zero high coefficients. The bound permits finitely many terminal words. Data-dependent root tests and source reconstruction leave these matrix entries fixed. All original clocks and root reads remain counted. $\square$

**Theorem 16.3 (supplied calibrated and prescribed-prefix sharpness).** Suppose a continuation starts at a fixed pure-$M$ state $M^T$, $T\ge0$, with the entire actual prefix history and exact $g,\delta,\operatorname{tr}(MP)$ supplied, and no further source information. On the actual-degree-$s$ subclass its optimal uniform additional-read count is $s+2$. Among protocols prescribed to start with $M^{2d+2}$ the exact total is $2d+s+5$, with worst case $3d+5$ over $s\le d$. These lower bounds permit arbitrary deterministic adaptive continuation and nonlinear answers.

**Proof.** The proof of Theorem 16.2 applies from every such $T$: use $B=JM^T$ and clocks $T+1+p$. The same all-pairs basis and root count prove the upper bound $s+2$.

For the lower bound let

$$
\nu=\frac{(1,\phi)^{\mathsf T}}{\sqrt{1+\phi^2}},\qquad
w=\frac{(-\phi,1)^{\mathsf T}}{\sqrt{1+\phi^2}},\qquad
\mathcal I=(-\phi,\phi^{-1}).
\tag{16.4}
$$

The entire legal fiber $\operatorname{tr}(MP)=\phi$ is

$$
\mathcal F=\{P_x=\nu(\nu+xw)^{\mathsf T}:x\in\mathcal I\}
\cup\{Q_y=(\nu+yw)\nu^{\mathsf T}:y\in\mathcal I\}.
\tag{16.5}
$$

To see completeness, in the orthonormal eigenbasis $\nu,w$ trace one and the specified $M$ trace force diagonal entries $1,0$. Rank one then says that the product of the two off-diagonal entries is zero, giving exactly these branches. Positivity of $\nu+xw$ is exactly $1-\phi x>0$ and $\phi+x>0$, hence $x\in\mathcal I$, and the same holds for $y$. The branches meet only at $P_* =\nu\nu^{\mathsf T}$: multiplying $x\nu w^{\mathsf T}=yw\nu^{\mathsf T}$ by $\nu$ forces $y=0$ and then $x=0$. Each source in this entire fiber has $\operatorname{tr}(M^iP)=\phi^i$ for every $i\ge0$ by the eigenvector relations and orthogonality. This is exactly the $\eta=0$ fiber of (12.2).

For every real matrix $A$, a single scalar $\operatorname{tr}(AP)$ fails to distinguish the whole fiber. With

$$
a_A=w^{\mathsf T}A\nu,\quad b_A=\nu^{\mathsf T}Aw,\quad
c_A=\operatorname{tr}(AP_*),
$$

the branch traces are $c_A+xa_A$ and $c_A+yb_A$. If either slope is zero, its branch already contains distinct equal-trace sources. If both are nonzero, choose a sufficiently small nonzero real $e$ and take $x=eb_A$, $y=ea_A$. Both lie in $\mathcal I$, both are nonzero, and the two distinct sources have the same trace. This establishes the scalar obstruction for every possible next cumulative matrix.

Fix one common gain and drift

$$
g_*(t)=c\prod_{j=1}^s(t-(T+j)),\qquad c\ne0,\qquad\delta=\delta_*.
\tag{16.6}
$$

The empty product at $s=0$ is one. All worlds with this same degree-$s$ gain, drift, and $P\in\mathcal F$ have identical pure-$M$ prefix history and identical supplied calibration data. The next $s$ reads are $\delta_*$ regardless of actions because those original clocks are roots. Induction makes their entire adaptive action history common. Correct recovery cannot stop on any such history, since it retains distinct complete targets. If a uniform protocol finished within $s+1$ added reads, its final cumulative matrix $A$ would be fixed by that common history before the last read. The scalar obstruction supplies two distinct actual sources in $\mathcal F$ with the same final read, hence identical decisions and answer. This contradicts correctness. The pair is chosen from the single already realized common-history family, so all ancestor equations remain satisfied.

This proves the lower bound $s+2$. For prescribed prefix $M^{2d+2}$ take $T=2d+2$. Supplying the calibration data only enlarges the permitted information, so the lower bound also holds for the original prescribed-prefix protocols. None can stop during the prefix on the same family, since every partial pure history still retains distinct targets. Adding its $2d+3$ reads gives $2d+s+5$; taking $s=d$ gives $3d+5$. The fixed prefix and absence of extra source information are essential hypotheses. $\square$

Write $N_d^{\mathrm{lin}}$ for the optimal uniform complete-target count under the countable fixed-linear full-gain-ray mechanism (1.3). The established scopes are:

| Task | Established conclusion |
| --- | --- |
| Fixed acquisition, with no mixed-word requirement | Exact gain threshold $2d+3$; credited Hermite result |
| Fixed mixed acquisition, $d=1,2,3$ | Exact gain thresholds six, eight, ten; arbitrary countable palettes |
| Fixed mixed acquisition, $d\ge4$ ($m\ge5$) | Either $2d+3$ or $2d+4$; the exact positive criterion (10.3) remains unresolved, with the transition-window restrictions of the companion volume |
| Complete target with this gain-output mechanism, $d=1$ | $6\le N_1^{\mathrm{lin}}\le8$; sharpness unresolved |
| Complete target with this gain-output mechanism, general $d$ | $2d+3\le N_d^{\mathrm{lin}}\le3d+5$ |
| Calibrated pure-$M$ continuation with only the specified source information | Exact additional count $s+2$ |
| Complete recovery constrained to prefix $M^{2d+2}$ | Exact actual-degree total $2d+s+5$ and worst-case total $3d+5$ |

The $4d+5$ construction of Theorem 16.1 remains a valid credited prior construction. Theorem 16.2 supplies the stronger current upper bound. Neither the prescribed-prefix lower bound nor the fixed mixed thresholds yield global complete-target sharpness. Separate fixed-word failures in degrees two or three do not combine their exceptional failure sets into a common adaptive obstruction. The mechanism-specific lower bounds do not apply to unrestricted nonlinear global recovery. The original full-domain cubic alternative of an at-most-eight-read decoder versus a lower bound of nine remains unresolved.

No result restricts $\beta$ to a known-factor subspace, excludes a gain root, makes $\eta$ generic, or omits a positive source. A fixed invertible coefficient-basis change preserves (1.3); restricting the coefficient space changes the task. The assumption $d\ge1$ is used in line preservation and the rank-one-versus-scalar arguments. No degree-zero assertion is made.

## 17. The supplied DEV cubic frontier at its literal histories

This section concerns the separate full cubic domain $0\ne g\in\mathcal P_3$, with the positive normalized sources and original-clock model of Section 1. It records the supplied results of *FIB Self-Calibrating Relation Mathematics VI* and *VII*. Their II/V dependencies below are credited interfaces; those nested texts have not been independently consulted. These local results are not premises of the critical classification or the low-degree interpolation proofs.

For any actual history $H$, let $\mathcal F(H)$ retain every action and read. For a known set $K\subseteq\mathcal F(H)$ define

$$
L_0(K,H)\Longleftrightarrow |K|\ge2,\qquad
L_{h+1}(K,H)\Longleftrightarrow |K|\ge2\ \land\
\bigwedge_{E\in\{M,J\}}\exists z:\
L_h(K\cap\mathcal F(H,E,z),(H,E,z)).
\tag{17.1}
$$

The horizon is bounded by the remaining original clocks. Negation means that one deterministic policy recovers the entire known set within that horizon, including early stopping. Every child is the actual response fiber of the same fixed worlds.

### 17.1 The MMJM correspondence and the resolved three-target bridge

The exact parent is

$$
H_3=(0,M,1,M,23/7,J,331/35),\qquad
H_4(Y)=(H_3,M,Y),\qquad Y\in\mathbb R.
\tag{17.2}
$$

Its matrices are $I,M,T,B,D$ with

$$
T=M^2=I+M,\quad B=JT=\begin{pmatrix}1&2\\1&1\end{pmatrix},\quad
D=MB=\begin{pmatrix}1&1\\2&3\end{pmatrix},\quad
Q_M=MD=B+D,\quad Q_J=JD=2B-M.
\tag{17.3}
$$

To distinguish the fifth reading from the declared coefficient dimension $m$, write $m_5(W),j_5(W)$ for VI's $m(W),j(W)$. They are the predictions $\delta+g(5)\operatorname{tr}(Q_MP)$ and $\delta+g(5)\operatorname{tr}(Q_JP)$. They are functions on the entire actual parent, not extra acquired reads. Use VI's positive chart

$$
\eta=(DP)_{22}>0,\quad R=P/\eta,\quad H=\eta g,\quad
DR=\begin{pmatrix}xy&x\\y&1\end{pmatrix},\quad
R=\begin{pmatrix}(3x-1)y&3x-1\\(1-2x)y&1-2x\end{pmatrix},\quad
1/3<x<1/2,\quad y>0.
\tag{17.4}
$$

Here the polynomial $H$ is distinct from the history symbol. With $s=x+y,p=xy$, the parent trace factors against $R$ are

$$
(3p+1-s-x,\ s-2p,\ p+1-x,\ s-p,\ p+1).
\tag{17.5}
$$

They are positive, and their products with $H(i)$ plus $\delta$ give exactly $(0,1,23/7,331/35,Y)$. The predictions are

$$
j_5=\delta+H(5)s,\quad m_5=\delta+H(5)(s+1),\quad
z_6^{MJ}=\delta+H(6)(p+y+1),\quad
z_6^{MM}=\delta+H(6)(p+s+2).
\tag{17.6}
$$

Superscripts list the chronological atoms at clocks five and six. The normalized complete target is $(R/\operatorname{tr}R,(\operatorname{tr}R)H,\delta)$. Identical $x,y,\delta$ fix that target: the source is fixed and four positive parent factors at clocks zero through three determine the whole gain by interpolation.

The exact inherited interfaces in VI, Convention 1.3, are these. II, Theorem 52.1 gives at most one target at any fixed drift with $g(6)=g(7)=0$. II, Theorem 53.1 says that a distinct two-target $L_2$ in either actual fifth child has equal drift, seventh roots, and nonzero sixth gains. II, Theorem 53.2 excludes a two-target $L_2$ after actual fifth $J$. II, Theorem 58.1 recovers the entire root-five promised class at (17.2) with the fixed $J,J,J$ continuation. V, Corollary 4.1 recovers every known set of at most three targets in one common non-diagonal joint fifth fiber, $m_5\ne j_5$, in the three remaining reads. All these interfaces retain the same arbitrary $Y$, full cubic domain, and literal parent. The common-fifth premise of the last interface is derived below for an arbitrary losing triple.

For completeness, the intervening VI, Lemma 2.1 and Theorem 2.2 have the following proofs in these quantities.

**Fixed-drift roots five and seven.** At each fixed $\delta=e$ at (17.2) there is at most one complete target with $g(5)=g(7)=0$.

**Proof.** Write $u=\operatorname{tr}(MP)>0$, $v=\operatorname{tr}(BP)>0$, $w=\operatorname{tr}(DP)>0$. Then $v=1+P_{12}+2P_{21}<1+2u$, since $1+2u-v=P_{12}+2P_{22}>0$. Factor

$$
g(t)=(t-5)(t-7)(a+bt),\qquad
a=-e/35,\quad b=(1-e)/(24u)+e/35.
\tag{17.7}
$$

The first two parent equations give these coefficients, including lower degrees and further multiplicities. Clock two gives

$$
12eu^2+(5e-57)u+35(1-e)=0.
\tag{17.8}
$$

If $0<e<1$, then $g(3)=(1-e)/u+16e/35>0$ and $eu<(57-5e)/12$. Substitution from (17.8) gives

$$
e+g(3)(1+2u)=(127-24e+20eu)/35
<(222-97e/3)/35<222/35.
$$

But clock three would require $331/35=e+g(3)v<e+g(3)(1+2u)$, a contradiction. For $e<0$ or $e>1$, the quadratic has negative root product $35(1-e)/(12e)$, so at most one positive root. For $e=0,1$ its unique positive root is respectively $35/57,13/3$. Each admitting drift thus determines at most one $u$ and the entire gain.

Its samples $g(3),g(4)$ are nonzero. An additional root three makes $g$ a nonzero multiple of $(t-3)(t-5)(t-7)$; the first three readings give $61e=333$, whereas clock three requires $e=331/35$. An additional root four gives a nonzero multiple of $(t-4)(t-5)(t-7)$; the first three readings force $e=241/31$ and $g(3)=-2e/35<0$, incompatible with $241/31<331/35$ and $v>0$. In either triple-root case $e=0$ would force the zero polynomial and is forbidden. Therefore

$$
v=(331/35-e)/g(3),\quad w=(Y-e)/g(4),\quad
P=\begin{pmatrix}-1-3u+v+w&-3-4u+v+2w\\1+2u-w&2+3u-v-w\end{pmatrix}.
\tag{17.9}
$$

The last formula is the four-trace inverse, also obtained by solving the traces against $I,M,B,D$. All divisors have been established nonzero. This proves uniqueness, without asserting existence for an empty drift class. $\square$

**Common fifth-$J$ prediction excludes a fifth-$M$ bad pair.** Two distinct targets with the same $m_5,j_5$ at (17.2) cannot form $L_2$ after that actual fifth $M$.

**Proof.** The inherited II, Theorem 53.1 supplies common drift $e$, seventh roots and nonzero sixth gains. Set $\kappa=m_5-j_5=H_i(5)$. If $\kappa=0$, the preceding fixed-drift roots-five-and-seven uniqueness makes the targets identical. If $\kappa\ne0$, both have $s=(j_5-e)/\kappa$. Put $v_i=H_i(6)\ne0$. Equal sixth predictions for each of the two possible actions give

$$
v_1(p_1+y_1+1)=v_2(p_2+y_2+1),\qquad
v_1(p_1+s+2)=v_2(p_2+s+2).
$$

The first quantity is nonzero. Their ratio is the same function at $x_1,x_2$,

$$
F_s(x)=\frac{x(s-x)+s+2}{x(s-x)+s-x+1},\qquad
F_s'(x)=\frac{x^2+2x+2}{[x(s-x)+s-x+1]^2}>0.
\tag{17.10}
$$

The legal fixed-$s$ domain $1/3<x<1/2$, $s-x>0$ is an interval with positive denominator. Thus $x_1=x_2$, then $y_1=y_2$, and common drift and the first four readings fix the same gain and target. Both signs of $v_i$ were allowed; its zero case was excluded by the stated inherited interface. $\square$

**Theorem 17.1 (DEV VI, Theorems 3.1–3.2).** For every real $Y$ and every exactly three-target known set $K\subseteq\mathcal F(H_4(Y))$,

$$
L_3(K,H_4(Y))\ \Longrightarrow\
\exists m_5\ne j_5\ \forall W\in K:\
m_5(W)=m_5,\ j_5(W)=j_5.
\tag{17.11}
$$

Every known set at this parent with at most three targets has a strategy using at most three further reads, hence eight total reads. Consequently any compatible losing family with $L_3$ there, finite or infinite, has at least four targets.

**Proof.** Unfold (17.1) at fifth $J$. The selected losing child has $L_2$ and at least two targets. The inherited II, Theorem 53.2 excludes exactly two, so that child must be all of the original triple. Its $j_5$ is constant. Unfold at fifth $M$. If its losing child had exactly two targets, they would share their actual $m_5$ and the already common $j_5$, contradicting the preceding bad-pair exclusion. This child too is all three targets, giving common $m_5$. These children are the same fixed triple with all earlier readings retained. If $m_5=j_5$, (17.6) gives $H_W(5)=0$ and thus $g_W(5)=0$ for every target. The inherited II, Theorem 58.1 gives one fixed $JJJ$ recovery policy on that whole class, contradicting $L_3$. This proves (17.11).

The inherited V, Corollary 4.1 now applies to exactly this common non-diagonal joint fiber and its whole known triple. It supplies recovery within the three remaining clocks, contradicting the assumed $L_3$. To spell out a policy on every known triple, if $j_5$ varies, take fifth $J$; each actual child has at most two targets. Stop on a singleton and separate a remaining pair within two atoms using II, Theorem 53.2. If $j_5$ is constant and $m_5$ varies, take fifth $M$ and use the proved bad-pair exclusion. On a pair choose the first word in $MM,MJ,JM,JJ$ whose sixth or seventh read differs, execute its atoms individually, and stop at the first distinction. Such a word exists by the two-target meaning of $\neg L_2$. If both fifth functions are constant and equal, use the root-five $JJJ$ policy. If constant and unequal, use V, Corollary 4.1 on the entire known triple, choosing at each retained fiber a successful next atom and stopping at a singleton.

For a known pair take fifth $J$; it either distinguishes immediately or leaves a pair excluded from $L_2$ by II, Theorem 53.2. A singleton can stop already. All policies use actual response children, clocks five through seven, and five already counted parent reads. Therefore every set of size below four is recoverable, proving the cardinality implication for an arbitrary compatible family without extracting a triple from a larger losing family. $\square$

VI, Theorem 3.3 also recovers a known $K\subseteq\mathcal F(H_4(Y))$ with constant $j_5$ if every actual fifth-$M$ child has at most two targets. Its policy takes that $M$ and separates each whole retained pair by the preceding exclusion. At $H_3$, if every actual fourth-$M$ child has at most three targets, take fourth $M$, read its $Y$, and apply Theorem 17.1 to that entire child. Both statements allow infinite known families and finish within eight total reads; they impose the cardinality conditions on every whole actual child.

### 17.2 Distinct complementary histories and their small-child promises

The all-drift pair exclusions in VI and VII have different literal ancestors. For VI, Definition 4.1, fix $D_0\in\mathbb R$, $\lambda\ne0$, $0<\varepsilon<1/6$, and set

$$
a_0=D_0-21\lambda,\quad a_2=D_0+5\lambda(1+\varepsilon),\quad
C_3=(a_0,M,D_0,J,a_2,M,D_0),\quad
C_4(Y)=(C_3,M,Y),\quad C_5(Y,z)=(C_4(Y),J,z).
\tag{17.12}
$$

This chronological $MJMMJ$ child has cumulative matrices

$$
I,M,U,MU,M^2U,Q,\quad
U=JM=\begin{pmatrix}1&1\\0&1\end{pmatrix},\quad
M^2U=\begin{pmatrix}1&2\\1&3\end{pmatrix},\quad
Q=JM^2U=\begin{pmatrix}1&3\\1&2\end{pmatrix}.
\tag{17.13}
$$

VI, Theorem 5.1 excludes two-target $L_2$ on every entire actual $C_5(Y,z)$, for arbitrary target drifts, both zero and nonzero sixth-gain strata, and all legal gains. Its proof is VI, Sections 4–5; the baseline inverse used there is explicitly V, Theorem 6.1. The parameter $D_0$ in this history is not a promise that $\delta=D_0$.

VII instead fixes $D_0,Y,z\in\mathbb R$, $\lambda\ne0$ and uses

$$
\begin{aligned}
H_J^-&=(D_0,J,D_0+24\lambda,M,D_0+48\lambda,M,D_0+312\lambda/5),\\
H_J(Y)&=(H_J^-,J,Y),\qquad H_{JM}(Y,z)=(H_J(Y),M,z).
\end{aligned}
\tag{17.14}
$$

This chronological $JMMJM$ child has matrices

$$
I,J,L,J+L,C,Q',\quad
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix},\quad
C=\begin{pmatrix}2&1\\1&1\end{pmatrix},\quad
Q'=MC=\begin{pmatrix}1&1\\3&2\end{pmatrix}.
\tag{17.15}
$$

Its reading normalization is $f=g/\lambda$, $e=(\delta-D_0)/\lambda$, $\widehat Y=(Y-D_0)/\lambda$, $\widehat z=(z-D_0)/\lambda$, yielding $(0,24,48,312/5,\widehat Y,\widehat z)$ without changing clocks or sources. VII, Theorem 4.1 excludes two-target $L_2$ on every actual $H_{JM}(Y,z)$ for arbitrary drifts and all gain samples. Its full proof is VII, Sections 1–4, including fixed-drift double-last-root uniqueness and the complete rational Bernstein certificate. Its terminal reconstruction credits V, Theorem 7.1. This history, its chart, and its certificate are distinct from (17.12)–(17.13) and from MMJM.

The consumers retain their hypotheses. By VI, Theorem 6.1, a known family at $C_4(Y)$ is recoverable within eight total reads if every entire actual fifth-$J$ child has at most two targets. At $C_3$ impose that bound on every actual fourth-$M$, fifth-$J$ joint child. By VII, Theorem 5.1, a known family at $H_J(Y)$ is recoverable within eight total reads if every entire actual fifth-$M$ child has at most two targets; at $H_J^-$ impose the bound on every actual fourth-$J$, fifth-$M$ joint child. In each case perform the specified one or two actions, retain the actual child, stop on a singleton, and use the first separating suffix in $MM,MJ,JM,JJ$ on its whole pair. The supplied pair exclusion ensures such a suffix, and every atom is immediately read. These policies allow infinitely many possible response values and mixed drifts, but require the entire actual child to have the stated size. The corresponding VI, Corollary 6.2 and VII, Corollary 5.2 force any losing child on those specified arms to contain at least three targets. Pair separation gives no policy for every larger child.

### 17.3 VII's common-response whole-class promise at MMJM

Return to (17.2)–(17.6). Let $(a_6,b_6,c_6,d_6)$ denote VII's chronological fifth/sixth response functions $(a,b,c,d_6)$, not coefficients or declared degree. With $v_6=H(6)$ they are

$$
a_6=\operatorname{read}(JJ)=\delta+v_6(p+1),\quad
b_6=\operatorname{read}(JM)=a_6+v_6x,\quad
c_6=\operatorname{read}(MJ)=a_6+v_6y,\quad
d_6=\operatorname{read}(MM)=c_6+v_6(x+1).
\tag{17.16}
$$

Fix known constants $Y,m_5,j_5,b_0,d_0$ and the entire class

$$
\mathcal C=\{W\in\mathcal F(H_4(Y)):
(m_5(W),j_5(W),b_6(W),d_6(W))=(m_5,j_5,b_0,d_0)\},\quad
\kappa=m_5-j_5,\quad \omega=d_0-b_0.
\tag{17.17}
$$

VII, Theorem 6.2 proves that if $\omega\ne0$, at least one of $a_6,c_6$ is injective on this whole class, including possible disjoint collision pairs, and a policy recovers it by clock six, seven total reads. Its exact curve correspondence is

$$
t=1/(y+1)\in(0,1),\quad \rho=\kappa/\omega,\quad
e=1-\rho,\quad K=(b_0-j_5)/\omega-\rho,\quad
v_6=\omega t,\quad
ex=K+\rho/t-t,\quad
a_6=b_0-\omega tx,\quad c_6=d_0-\omega t(x+1).
\tag{17.18}
$$

For $e\ne0$ an $a_6$ collision has parameter sum $K$ and a $c_6$ collision has sum $K+e$. Here $\rho$ is the arbitrary real response-curve ratio, distinct from the positive interpolation parameter in Section 10. The supplied proof treats $\rho>1$, $\rho=1$, $\rho<0$, and $0\le\rho<1$ separately; in the last case the containing legal parameter interval has diameter less than $e/6$, excluding two collision midpoints separated by $e/2$. The statement includes $\kappa=0$ when $\omega\ne0$. For $\omega=0$, $\kappa\ne0$, the whole class is recovered by $JJJ$ in eight total reads: $v_6=0$, $\delta=b_0$, common $s=(j_5-b_0)/\kappa>0$, and the inherited II, Lemma 71.1 makes $H(7)$ injective on that precise root-six, fixed-drift non-diagonal fiber; the last response is $b_0+sH(7)$. The diagonal $\omega=\kappa=0$ extension is not asserted.

VII, Corollary 6.3 restricts this whole-class inverse to any known subset. It also applies at $H_3$ when every actual fourth-$M$ child has supplied known constants placing that entire child in a class (17.17) satisfying one of the two conditions. The constants are candidate promises. The policy neither reads both unchosen arms nor obtains those promises from unrestricted observations. The complete proof and arm choice are VII, Section 6, using the explicitly credited II response-curve and root-six interfaces.

### 17.4 Remaining local and original-root questions

At the same MMJM parent (17.2), whether some entire $\mathcal F(H_4(Y))$ has $L_3$ remains unresolved. Such a losing family must have at least four distinct targets by Theorem 17.1. The arbitrary exactly-three-target common non-diagonal fifth bridge and every known-at-most-three-target recovery problem there have already been resolved by VI, Theorems 3.1–3.2. They are not remaining bridges. No extraction of a losing triple from a larger losing family follows.

At the distinct MJMM and JMMJ parents (17.12), (17.14), an actual designated fifth child with at least three targets could retain $L_2$ through different bad pairs for different actions. Joint realization with the opposite fifth arm, under the same entire ancestor history, is unresolved. VI and VII exclude the two-target alternatives and prove the stated small-child consumers; they do not decode arbitrary larger fibers. At MMJM the whole-known-class result (17.17) does not place an unrestricted variable-response fiber inside its promises, and its diagonal zero-layer extension remains outside the stated conclusion.

The local and original-root simultaneous-realization systems identified in DEV VI, Section 7 and VII, Section 7 have no feasibility decision supplied here. The unrestricted original alternative remains a lawful complete-target decoder in at most eight total reads on all cubic worlds versus $n_{\mathrm{det}}(3,0)\ge9$. Each initial action, actual history and early stop belongs to that problem. None of the local cardinality bounds, promised whole-class policies, fixed-linear gain obstructions, or prescribed pure-prefix sharpness resolves it. The all-degree positive $JJ$ question remains exactly (10.3), or the equivalent transition-window criterion in the companion volume. The original global and all-degree programme remains active.

## 18. Attribution and mathematical correspondence

The supplied **FIB Linear Gain-Ray Capacity and Hermite Readouts** is the prior source for the full model, universal-collinearity and countable-cover reduction, mixed obstruction through $2m$ reads, pure-$M$ Hermite obstruction, exact $2d+3$ fixed-acquisition threshold, $2d+4$ mixed construction, pure-terminal bridge, and $4d+5$ complete-target construction. Their correspondence here is:

| Prior supplied source | Present self-contained use |
| --- | --- |
| Sections 1–2 | Sections 1–3: full domain, exact output, universal reduction, and Baire covering |
| Section 3 | Sections 2, 11, and Lemma 15.1: mixed span, earlier budgets, and pure-terminal ambiguity |
| Sections 4–5 | Section 12: spectral jets, both endpoint inequalities, exact gain/drift, and fixed-acquisition sharpness |
| Section 6 | Section 14: shifted Euler jets and the strictly positive mixed scale |
| Section 7 | Theorem 16.1: shared root counting and the four-matrix source reconstruction |
| Sections 8–9 | Sections 16–18: quantifier boundaries and inherited credits |

That source attributes the cubic mixed-word and finite-palette obstruction to **FIB Self-Calibrating Relation Mathematics IV**, Theorem 10.2, and its conventions to that volume's Definitions 1.1 and 10.1. These are inherited attributions, not claims of independent consultation. The complete proofs needed here are supplied above; nested references are not treated as verified additional inputs.

The supplied **critical mixed classification**, results B–H, is the source of the critical three-span claim, the syzygy alternatives, legal-word candidates, exceptional-source obstruction strategy, positive $JJ$ condition, and degree-one mixed conclusion. Sections 4–10 and 13 give complete proofs of those claims, including the zero-numerator syzygy case, the rank-three contradiction after deleting $m-2$ nodes, precise original-clock interpolation, realization of the negative-ratio stratum, and obstruction to every countable palette on that stratum. Result A there is prior universal-reduction material already credited to the Hermite source.

The degree-one complete-target consequence is proved separately in Theorem 15.2 using one common open family and source ambiguities for both identity-bearing words. Its justification is not an inference from separate fixed-word palette failures. This common-open-domain bridge is used only at degree one. It is independent of the separate per-word palette failures and is not transferred to degrees two or three.

The supplied **JJ quadratic/cubic feasibility proofs**, lemmas Q, L, S, and C, supply the positive interpolation exclusions added to the critical classification. Their exact correspondence is:

| Supplied proof | Present self-contained result |
| --- | --- |
| Q | Lemma 13.2: quadratic reflection, recurrence contradiction, and both edge calculations |
| L | Lemma 13.3: two fourth-difference equations and every positive-parameter sign interval |
| S | Lemma 13.4: six centered original clocks and incompatible difference/sum equations |
| C | Theorem 13.5: every cubic gap, including the verified positive shifted parameter at $a=1$ |
| Capacity corollary | Corollary 13.6: sharp fixed mixed eight/ten thresholds using the classification and credited mixed upper construction |

The feasibility contribution is relative to the critical source's open $m=3,4$ cases. Its proofs and the resulting thresholds are credited supplied mathematics, not independently discovered results of this exposition. The determinant condition remains part of the exact criterion; the new exclusions disprove interpolation itself and do not claim determinant singularity. Nested source names introduce no additional mathematical premises.

Polynomial root counting, finite differences, Lagrange and Hermite interpolation, elementary projective cross ratios, linear algebra, the intermediate value property, and the Euclidean Baire principle are established tools. Reusing them and the supplied Hermite results is not counted as new mathematics. The substantive critical results are the structural reduction, exceptional-source analysis, and positive interpolation decisions at $m=3,4$. The exact feasibility question at $m\ge5$ and the unrestricted full-recovery programme remain open.

The complete supplied *FIB Moving-Trace Recovery and Sharp Calibrated Continuations*, Sections 3–6, supplies Theorems 16.2–16.3. Their full proofs above retain the all-pairs basis, every root read, the entire positive crossing fiber, the scalar obstruction, the single common root-hiding gain, and the calibrated and prescribed-prefix quantifiers. Its Section 2 calibration is the Hermite result already reproduced in Section 12. The improved upper bound does not replace the validity of the prior construction in Theorem 16.1.

The complete supplied DEV VI and VII provide Section 17's current cubic frontier. VI, Definitions 1.1–1.2, Convention 1.3, Lemma 2.1 and Theorems 2.2, 3.1–3.3 correspond to (17.1)–(17.11) and their proofs. VI, Sections 4–6 supply the separate MJMMJ pair theorem and its at-most-two-actual-child consumers. VII, Sections 1–5 supply the separate JMMJM pair theorem, its rational positivity certificate and consumers; VII, Section 6 supplies the common-$b_6,d_6$ whole-class application with its nonzero and non-diagonal zero strata. The source-contained proofs for the latter credited interfaces remain in those specified sections, with their exact II/V premises retained above. No unseen II/V argument is asserted to have been independently verified. The external identifiability and state-distinguishing references discussed in VI/VII are contextual interfaces and supply no acquisition threshold used here.

The companion *FIB Positive JJ Sign Transitions and Reciprocal Extrapolation*, Sections 3–10, supplies the all-degree transition-window refinement of the unresolved positive criterion. Its P1–P8 arguments and exact residual equations preserve the original-clock interpolation and determinant obligation. These are supplied mathematical results and current scope corrections to the two substantive volumes.

## 追加锚（本行以下为增补区）
