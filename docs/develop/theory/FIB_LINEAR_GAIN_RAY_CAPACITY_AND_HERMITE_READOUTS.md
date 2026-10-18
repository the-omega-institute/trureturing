# FIB Linear Gain-Ray Capacity and Hermite Readouts

## 1. The acquisition model and the two targets

**Definition 1.1 (complete domain).** Fix a declared maximum degree $d\ge1$ and put $m=d+1$. Let $\mathcal W_d$ consist of triples $(P,g,\delta)$, where $P$ is a strictly entrywise positive real $2\times2$ matrix of rank one and trace one,

$$
g(t)=\sum_{k=0}^d\beta_k t^k,\qquad \beta\in\mathbb R^m\setminus\{0\},\qquad \delta\in\mathbb R.
$$

The actual degree may be smaller than $d$, including zero. There are no restrictions on coefficient signs, sampled roots, repeated roots, or the constant drift.

Set

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
A_0=I,\quad A_i=E_iA_{i-1},\quad
z_i=g(i)\operatorname{tr}(A_iP)+\delta,
\tag{1.1}
$$

where each chronological action $E_i$ is exactly one $M$ or one $J$, immediately followed by its read. The initial read counts, so $N$ reads have original clocks $0,\ldots,N-1$. All constructions use one trajectory, without resets, copies, skipped reads, unread compound actions, empty-action reads, clock renumbering, or another sensor. A deterministic protocol may choose actions, stopping, and its answer from the entire actual history. No regularity of these choices is assumed.

An unnormalized positive rank-one pair $(R,G)$ represents the normalized target

$$
P=R/\operatorname{tr}R,\qquad g=(\operatorname{tr}R)G.
\tag{1.2}
$$

Indeed $g(i)\operatorname{tr}(A_iP)=G(i)\operatorname{tr}(A_iR)$. The equivalence is $(R,G)\sim(cR,G/c)$ for $c>0$; the drift is a separate coordinate.

**Definition 1.2 (fixed linear gain-ray output).** For a fixed terminal word $w$ with $N-1$ actions, write $Z_w=(z_0,\ldots,z_{N-1})^{\mathsf T}$. A fixed real matrix $C\in\mathbb R^{m\times N}$ succeeds at a world if

$$
CZ_w=s\beta\qquad\text{for some }s\in\mathbb R\setminus\{0\}.
\tag{1.3}
$$

Either sign of $s$ is allowed. A countable palette assigns at most countably many fixed matrices to each terminal word; the selector can be any function of actual history. Matrix entries chosen from the observed data are outside this definition. Complete-target recovery returns $(P,g,\delta)$; gain-only recovery returns the ray in (1.3). These are different tasks.

Fixed acquisition means that the action word is preassigned independently of data. An early output along such a word can be retained while finishing the word, with zero columns appended to its matrix. Consequently early stopping does not improve the lower bound for fixed acquisition proved below. Adaptively chosen words are treated separately.

## 2. Universal identities and countable palettes

**Lemma 2.1 (evaluation rank and source span).** Let $V_{ik}=i^k$ for $0\le i<N$ and $0\le k<m$, with $0^0=1$, and put $a_i(S)=\operatorname{tr}(A_iS)$. Evaluation at any $r$ distinct clocks has rank $\min(r,m)$. The legal normalized sources span $\operatorname{Mat}_2(\mathbb R)$.

**Proof.** A polynomial of degree at most $m-1$ with $m$ distinct zeros vanishes. For $r\le m$, the usual Lagrange polynomials at those $r$ nodes give every value vector; for $r\ge m$, the preceding zero count gives injectivity. For the source claim, take two independent strictly positive columns and two independent strictly positive rows. Their four outer products form a basis of the matrix space. Each is positive rank one with positive trace; dividing each by its trace preserves independence and makes it legal. $\square$

**Lemma 2.2 (universal collinearity).** Suppose that, for a fixed word and matrix $C$, $CZ_w$ is collinear with $\beta$ for every world, permitting the zero vector in this hypothesis. Then

$$
C\mathbf1=0,\qquad
C\operatorname{diag}(a(S))V=\ell(S)I_m
\quad\text{for all }S\in\operatorname{Mat}_2(\mathbb R),
\tag{2.1}
$$

for a linear functional $\ell$. If $C$ succeeds at even one world, then $\ell\ne0$.

**Proof.** Vary $\delta$ while fixing a nonzero $\beta$. The difference of the two outputs shows that $C\mathbf1$ belongs to $\operatorname{span}\{\beta\}$. As $m\ge2$, the intersection of these lines over all nonzero $\beta$ is zero. For fixed $P$, the linear map $C\operatorname{diag}(a(P))V$ sends every vector into its own line. Its action on basis vectors is diagonal, and its action on each sum of two basis vectors makes every diagonal entry equal. Thus it is a scalar matrix. One of its diagonal entries defines a linear functional $\ell(S)$ on all matrices. The identity on legal $P$ extends to every auxiliary $S$ by Lemma 2.1. Auxiliary matrices used in this linear extension need not be physical sources. At a successful world the scalar $\ell(P)$ is nonzero. $\square$

**Lemma 2.3 (countable covering obstruction).** Consider any collection of admissible terminal words at a finite read budget. If none admits (2.1) with $\ell\ne0$, then no countable palette supported on these words succeeds on the whole domain, regardless of action, stopping, and selector regularity.

**Proof.** Every legal source has the unique chart

$$
P(x,r)=\frac1{1+xr}\begin{pmatrix}1&r\\x&xr\end{pmatrix},\qquad x,r>0.
\tag{2.2}
$$

To check surjectivity, write a legal source as $\left(\begin{smallmatrix}a&b\\c&e\end{smallmatrix}\right)$, set $x=c/a,r=b/a$, and use $ae=bc$ and $a+e=1$. The full parameter domain

$$
\Omega_d=(0,\infty)^2\times(\mathbb R^m\setminus\{0\})\times\mathbb R
\tag{2.3}
$$

is nonempty and open. For each word-map pair, collinearity is expressed by

$$
\beta_j(CZ_w)_k-\beta_k(CZ_w)_j=0\qquad(0\le j<k<m).
\tag{2.4}
$$

Multiplying by $1+xr$ makes each expression a polynomial in $(x,r,\beta,\delta)$. For a pair successful anywhere, these polynomials cannot all be identically zero: otherwise Lemma 2.2 would give a forbidden nonzero universal identity. Choose one nonzero polynomial for each such pair.

The zero set of a nonzero real polynomial is closed and has empty interior. The latter assertion follows by induction on the number of variables: vanishing on a product of intervals makes each univariate coefficient polynomial vanish on a product of intervals of smaller dimension, and a univariate polynomial vanishing on an interval is zero. Thus each chosen zero set is nowhere dense relative to $\Omega_d$.

There are finitely many words at the budget and countably many matrices per word. These zero sets cannot cover $\Omega_d$, by the Baire category theorem. One can see the needed form directly: choose a closed ball of positive radius inside $\Omega_d$, and successively choose nested positive-radius closed subballs avoiding the first, second, and subsequent zero sets, with diameters tending to zero. The common point, supplied by completeness of Euclidean space, stays in the initial ball and avoids every zero set. Every successfully processed world would have to lie in the zero set assigned to its selected pair, a contradiction. No topological assumption on the actual selection sets or terminal branches has entered. $\square$

## 3. Mixed words and complete-target protocols

**Theorem 3.1 (mixed-word obstruction through $2d+2$ reads).** For $N\le2m$, a word containing both $M$ and $J$ admits no fixed $C$ satisfying (2.1) with $\ell\ne0$.

**Proof.** Such an identity would imply $\operatorname{rank}C=m$, by choosing $S$ with $\ell(S)\ne0$. If $N<m$ this already fails. Write $\ell(S)=\operatorname{tr}(LS)$ for a nonzero matrix $L$, using nondegeneracy of the trace pairing, and set $E=\ker\ell$. Put

$$
Q=\{i:A_i\text{ is proportional to }L\},\qquad q=|Q|.
$$

For $i\notin Q$, $a_i$ restricts to a nonzero functional on $E$: a functional vanishing on $\ker\ell$ would be proportional to $\ell$. Choose $S\in E$ outside the finitely many resulting proper hyperplanes. Such a choice exists, for instance because a product of their nonzero defining linear polynomials cannot vanish on all of $E$. Then $a_i(S)\ne0$ exactly at indices outside $Q$. The nuisance image $\operatorname{diag}(a(S))\operatorname{range}V$ lies in $\ker C$ and has dimension $\min(N-q,m)$ by Lemma 2.1.

If $q>0$, this image vanishes at all indices of $Q$, whereas $\mathbf1$ does not. Since $\mathbf1\in\ker C$, we get

$$
N-m\ge\min(N-q,m)+1.
\tag{3.1}
$$

When $N-q\ge m$, this forces $N\ge2m+1$. Otherwise it forces $q\ge m+1$. Neither can occur: adjacent cumulative matrices cannot be proportional, since $A_{i+1}=cA_i$ and invertibility of $A_i$ would give $E_{i+1}=cI$. Hence a proportionality class occupies at most $\lceil N/2\rceil\le m$ indices.

If $q=0$, the nuisance image has dimension $m$, so $N-m\ge m$ and therefore $N=2m$. Equality of dimensions gives

$$
\ker C=\operatorname{diag}(a(S))\operatorname{range}V.
\tag{3.2}
$$

For every $T\in E$, the diagonal matrix with entries $a_i(T)/a_i(S)$ consequently preserves $\operatorname{range}V$. Every diagonal matrix preserving degree-at-most-$m-1$ evaluation vectors at $2m$ distinct nodes is scalar. To prove this, take the polynomial with any chosen $m-1$ nodes as its simple roots. Its diagonal image is the evaluation of a polynomial of degree at most $m-1$ vanishing at those roots, hence a scalar multiple of the original polynomial. All diagonal entries outside those roots are equal. Given any two indices, choose the roots among the other $2m-2$ nodes to obtain equality of those two entries. This also covers zero diagonal entries.

It follows that the restrictions $a_i|_E$ span at most one dimension: for each $T\in E$, all ratios $a_i(T)/a_i(S)$ coincide. Restriction from the full dual matrix space to $E$ has kernel $\operatorname{span}\{\ell\}$. Thus the unrestricted $a_i$, and equivalently the matrices $A_i$, span at most two dimensions.

A mixed word has cumulative span at least three. If it starts with $M^k$ before its first $J$, $k\ge1$, it contains $I,M,JM^k$. The first two are symmetric. From $M^2=M+I$, induction gives

$$
M^k=\begin{pmatrix}F_{k-1}&F_k\\F_k&F_{k+1}\end{pmatrix},\qquad
F_0=0,\ F_1=1,\ F_{k+1}=F_k+F_{k-1}.
$$

The off-diagonal entries of $JM^k$ differ by $F_k>0$, so it is outside their span. If the word starts with $J^k$ before its first $M$, its cumulative matrices include $I,J$ and $M$ or $MJ$, according to the parity of $k$. Neither lies in $\operatorname{span}\{I,J\}$: $M$ has unequal diagonal entries, and $MJ=\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$ has unequal off-diagonal entries. This contradicts the two-dimensional bound. $\square$

**Lemma 3.2 (pure terminal histories cannot recover the complete target).** A correct deterministic complete-target protocol on all of $\mathcal W_d$ cannot terminate on a word containing just one atom type, including the empty word.

**Proof.** Fix $A=M$ or $J$. Its powers lie in $\operatorname{span}\{I,A\}$, by $M^2=M+I$ and $J^2=I$. For every legal $P=uv^{\mathsf T}$ with $u,v>0$ and $v^{\mathsf T}u=1$, there is a distinct legal $P'$ with $\operatorname{tr}(AP')=\operatorname{tr}(AP)$. If $u,Au$ are independent, perturb $u$ slightly to a nonproportional positive $u'$ and solve

$$
(v')^{\mathsf T}u'=1,\qquad (v')^{\mathsf T}Au'=v^{\mathsf T}Au.
$$

The coefficient matrix remains invertible near $u$; its solution is continuous and stays positive near $v$. Different column lines ensure $u'(v')^{\mathsf T}\ne P$. If $Au=\lambda u$, keep $u$ and vary $v$ within the positive part of the line $v^{\mathsf T}u=1$. The $A$ trace stays $\lambda$ and the source changes. With the same $g,\delta$, the two worlds share every pure-$A$ read. Determinism forces the same decisions along this actual history, including the terminal decision, so both cannot receive a correct common target. With no actions, $z_0=g(0)+\delta$ is independent of $P$ and the same conclusion holds. $\square$

**Theorem 3.3 (countable-palette complete-protocol lower bound).** No correct complete-target protocol using at most $2d+2$ reads can obtain a successful countable-palette gain-ray output on every world.

**Proof.** Lemma 3.2 makes every actual terminal word mixed. Theorem 3.1 and Lemma 2.3 exclude successful coverage by their countable palettes. This applies to arbitrary action, stopping, and selection functions. It does not assert that a gain-only protocol has mixed terminal words. $\square$

For $d=3$, the fixed mixed-word argument and the finite-palette complete-protocol obstruction are the credited results of *FIB Self-Calibrating Relation Mathematics IV*, Theorem 10.2. The countable extension uses Lemma 2.3 instead of a finite product of polynomials.

## 4. The pure-$M$ endpoint obstruction

**Lemma 4.1 (spectral coordinates).** Define

$$
\phi=\frac{1+\sqrt5}{2},\quad \psi=\frac{1-\sqrt5}{2}=-\phi^{-1},\quad
\Pi_+=\frac{M-\psi I}{\phi-\psi},\quad
\Pi_-=\frac{\phi I-M}{\phi-\psi}.
\tag{4.1}
$$

Then $\Pi_\pm$ are complementary rank-one spectral projectors and

$$
M^i=\phi^i\Pi_++\psi^i\Pi_-,\quad
\alpha(S)=\operatorname{tr}(\Pi_+S),\quad
\eta(S)=\operatorname{tr}(\Pi_-S).
\tag{4.2}
$$

For legal $P$, $\alpha(P)>0$ and $\alpha(P)+\eta(P)=1$. The value $\eta(P)$ may be zero or negative.

**Proof.** The characteristic identity $(M-\phi I)(M-\psi I)=0$ and $\phi\ne\psi$ give $\Pi_++\Pi_-=I$, $\Pi_+\Pi_-=0$, and $M\Pi_\pm=\phi\Pi_+$ or $\psi\Pi_-$, respectively. These prove (4.2), including $i=0$. Each projector has trace one and is nonzero, hence has rank one. The entries of $\Pi_+$ are $(-\psi,1,1,1-\psi)/(\phi-\psi)$, all strictly positive. Thus its trace pairing with positive $P$ is positive. The sum identity gives $\alpha(P)+\eta(P)=\operatorname{tr}P=1$. $\square$

**Lemma 4.2 (readout polynomials and jets).** For $f(x)=\sum_i c_i x^i$ and $D=x\,d/dx$,

$$
(D^j f)(\lambda)=\sum_i c_i i^j\lambda^i,\qquad
((D+1)^j f)(\lambda)=\sum_i c_i(i+1)^j\lambda^i.
\tag{4.3}
$$

At a nonzero node $\lambda$, either list of jets through order $d$ is an invertible triangular transform of the ordinary derivative jets through that order.

**Proof.** The monomial $x^i$ is an eigenvector of $D$ with eigenvalue $i$ and of $D+1$ with eigenvalue $i+1$, proving (4.3). Induction on $j$ shows that the leading derivative term of either operator power is $x^j f^{(j)}$, with all other terms involving smaller derivative orders. The diagonal entries of the jet transform are $1,\lambda,\ldots,\lambda^d$, all nonzero. In particular, vanishing of all these jets is equivalent to a root of multiplicity at least $m$. These operators specify fixed polynomial coefficients for readout maps; they do not change acquired clocks. $\square$

**Theorem 4.3 (pure-$M$ lower bound).** A pure-$M$ word with at most $2m$ reads admits no identity (2.1) with $\ell\ne0$.

**Proof.** Append $M$ actions and pad $C$ with zero columns if necessary, so $N=2m$. On auxiliary matrices the trace sequence is $a_i(S)=\alpha(S)\phi^i+\eta(S)\psi^i$. Therefore (2.1) makes $\ell$ vanish on $\ker\alpha\cap\ker\eta$. The functionals $\alpha,\eta$ are independent, as evaluation on the two projectors gives $(1,0)$ and $(0,1)$. Hence $\ell=u\alpha+v\eta$ with $(u,v)\ne(0,0)$.

For row $k$ of $C$ define $f_k(x)=\sum_{i=0}^{2m-1}C_{ki}x^i$. The drift and coefficient identities imply

$$
f_k(1)=0,\qquad
(D^j f_k)(\phi)=u\delta_{jk},\qquad
(D^j f_k)(\psi)=v\delta_{jk}
\quad(0\le j,k\le d),
\tag{4.4}
$$

where $\delta_{jk}$ denotes the Kronecker symbol, not the drift.

Let $H_\phi$ be the polynomial of degree at most $2d+1$ with value one at $\phi$, value zero at $\psi$, and ordinary derivatives of orders $1,\ldots,d$ zero at both nodes. It exists uniquely: the homogeneous square Hermite system has roots of multiplicity $m$ at both nodes, impossible in degree at most $2m-1$ unless zero. Let $H_\psi=1-H_\phi$. Lemma 4.2 gives

$$
f_0=uH_\phi+vH_\psi.
\tag{4.5}
$$

The derivative of $H_\phi$ has degree at most $2d$, zeros of multiplicity at least $d$ at both endpoints, and integral one from $\psi$ to $\phi$. Consequently

$$
H_\phi'(x)=c(x-\psi)^d(\phi-x)^d,\qquad c>0
\quad(\psi<x<\phi).
\tag{4.6}
$$

The density is symmetric about $(\phi+\psi)/2=1/2$ and strictly positive in the interval. Since $\psi<1<\phi$ and $1>1/2$,

$$
\frac12<H_\phi(1)<1,\qquad 0<H_\psi(1)<\frac12.
$$

The condition $f_0(1)=0$ forces $u\ne0$ and

$$
\frac vu=-\frac{H_\phi(1)}{H_\psi(1)}<-1.
\tag{4.7}
$$

On the other hand, the jets of $f_d$ below order $d$ vanish at both nodes. Its degree bound gives

$$
f_d(x)=(x-\phi)^d(x-\psi)^d(ax+b).
$$

Because $1$ is neither spectral node, $f_d(1)=0$ gives $b=-a$. Taking the order-$d$ Euler jets yields

$$
u=d!\phi^d(\phi-\psi)^d a(\phi-1),\qquad
v=d!\psi^d(\psi-\phi)^d a(\psi-1).
$$

Here $u\ne0$ implies $a\ne0$. As $\phi-1=\phi^{-1}$ and $\psi-1=-\phi$,

$$
\frac vu=\left(\frac{-\psi}{\phi}\right)^d\frac{\psi-1}{\phi-1}
=-\phi^{2-2d}\in[-1,0)
\quad(d\ge1),
\tag{4.8}
$$

contradicting (4.7). This proves the claim, including $d=1$. $\square$

## 5. Exact Hermite gain and drift readouts

**Lemma 5.1 (the square interpolation system).** For any prescribed Euler jets through order $d$ at each of $\phi,\psi$, and any prescribed value at $1$, there is exactly one polynomial of degree at most $2m$ satisfying them. The same assertion holds with $D+1$ in place of $D$.

**Proof.** The polynomial space has dimension $2m+1$, equal to the number of conditions. In the homogeneous system, Lemma 4.2 gives roots of multiplicity at least $m$ at $\phi,\psi$, together with a root at the distinct node $1$. A nonzero polynomial would have degree at least $2m+1$, which is forbidden. Thus the linear map from coefficients to conditions is injective between equal finite dimensions, hence bijective. This proves both existence and uniqueness for arbitrary prescribed conditions. $\square$

**Theorem 5.2 (exact all-input readouts at $2d+3$ reads).** The pure word $M^{2m}$, comprising $2m$ separate actions and $2m+1$ reads, has fixed linear maps recovering the entire normalized coefficient vector $\beta$ and the drift $\delta$ exactly.

**Proof and construction.** For each $0\le k\le d$, let $f_k^+,f_k^-$ be the unique degree-at-most-$2m$ polynomials given by Lemma 5.1 with

$$
\begin{aligned}
f_k^+(1)&=0,& (D^j f_k^+)(\phi)&=\delta_{jk},& (D^j f_k^+)(\psi)&=0,\\
f_k^-(1)&=0,& (D^j f_k^-)(\phi)&=0,& (D^j f_k^-)(\psi)&=\delta_{jk}
\end{aligned}
\quad(0\le j\le d).
\tag{5.1}
$$

Write $f_k^\pm(x)=\sum_{i=0}^{2m}c_{ki}^\pm x^i$ and use the actual reads to form

$$
U_k=\sum_{i=0}^{2m}c_{ki}^+z_i,\qquad
V_k=\sum_{i=0}^{2m}c_{ki}^-z_i.
\tag{5.2}
$$

The coefficients depend only on the declared degree and the fixed atoms. Along this word,

$$
z_i=\sum_{j=0}^d\beta_j i^j
\bigl(\alpha(P)\phi^i+\eta(P)\psi^i\bigr)+\delta.
$$

Substitute this expression into (5.2) and apply (4.3) and (5.1). Every unwanted jet and the drift vanish, giving

$$
U_k=\alpha(P)\beta_k,\qquad
V_k=\eta(P)\beta_k,\qquad U+V=\beta.
\tag{5.3}
$$

For the drift put $Q(x)=x^2-x-1$ and

$$
f_\delta(x)=(-1)^m Q(x)^m,\qquad
\delta_{\rm out}=\sum_{i=0}^{2m}[x^i]f_\delta(x)\,z_i.
\tag{5.4}
$$

The polynomial $f_\delta$ has zeros of multiplicity $m$ at both spectral nodes and $f_\delta(1)=(-1)^m(-1)^m=1$. Its Euler jets through order $d$ therefore vanish at both nodes. The same substitution proves $\delta_{\rm out}=\delta$.

The output $\beta$ is nonzero on every legal world. No division, root exclusion, sign condition, or nonvanishing assumption on $\eta(P)$ is used. The identity $\alpha+\eta=1$ is the trace-one normalization; without normalization the sum would be $(\operatorname{tr}R)G$ in the notation of (1.2). All clocks are exactly $0,\ldots,2m$, and every intermediate action is read. $\square$

**Theorem 5.3 (sharp fixed-acquisition threshold).** For every declared $d\ge1$, the optimal read count for full-domain gain-ray extraction on a preassigned acquisition word is exactly $2d+3$, even with arbitrary countable-palette selection.

**Proof.** Theorem 5.2 gives the upper bound. At $N\le2m$, mixed words are excluded by Theorem 3.1 and Lemma 2.3; pure-$M$ words are excluded by Theorem 4.3 and Lemma 2.3. For pure-$J$ words, use the same legal source

$$
P_*=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix}
$$

in the two worlds $(P_*,t,0)$ and $(P_*,t+1,-1)$. Since $JP_*=P_*$, both produce $z_i=i$ at every original clock, for arbitrarily long pure-$J$ acquisition. The full coefficient vectors of $t$ and $t+1$ are noncollinear for every $d\ge1$. Identical histories therefore rule out any gain-ray selector, even unrestricted nonlinear selection. The same pair covers the no-action case. These cases exhaust all preassigned words. Padding early outputs as in Definition 1.2 covers early stopping on a preassigned word. $\square$

Even infinitely many pure-$M$ reads cannot recover the whole source $P$: Lemma 3.2 supplies a distinct source with the same pure-$M$ trace sequence and the same $g,\delta$. Exact gain-and-drift recovery is thus strictly weaker than complete-target recovery.

## 6. A nonvanishing mixed-word realization

**Theorem 6.1 (mixed gain output at $2d+4$ reads).** The mixed chronological word $JM^{2m}$ admits one fixed linear gain-ray map with output

$$
\operatorname{tr}(JP)\beta,
\tag{6.1}
$$

which is nonzero for every world.

**Proof and construction.** Execute one $J$ and then $2m$ individual $M$ actions, reading after each and including $z_0$. The actual clocks are $0,\ldots,2m+1$. For $i\ge1$,

$$
A_i=M^{i-1}J,\qquad
z_i=\bigl(\alpha'\phi^{i-1}+\eta'\psi^{i-1}\bigr)g(i)+\delta,
$$

where $\alpha'=\operatorname{tr}(\Pi_+JP)$ and $\eta'=\operatorname{tr}(\Pi_-JP)$. Their sum is $\operatorname{tr}(JP)=P_{12}+P_{21}>0$.

For each $k$, let $h_k$ be the unique degree-at-most-$2m$ polynomial satisfying

$$
h_k(1)=0,\qquad
((D+1)^j h_k)(\phi)=((D+1)^j h_k)(\psi)=\delta_{jk}
\quad(0\le j\le d).
\tag{6.2}
$$

Existence and uniqueness follow from the complete square-system argument of Lemma 5.1, including its root-multiplicity proof. Write $h_k(x)=\sum_{r=0}^{2m}b_{kr}x^r$ and define

$$
Y_k=\sum_{r=0}^{2m}b_{kr}z_{r+1}.
\tag{6.3}
$$

This is a fixed matrix on the entire acquired data vector, with coefficient zero on $z_0$. Equation (4.3) gives

$$
Y_k=\sum_{j=0}^d\beta_j
\left(\alpha'((D+1)^j h_k)(\phi)+
\eta'((D+1)^j h_k)(\psi)\right)
=(\alpha'+\eta')\beta_k.
$$

Thus (6.1) holds with a strictly positive scale, regardless of sampled roots, actual degree, signs, or drift. The polynomial exponent $r$ only specifies the coefficient of the read acquired at original clock $r+1$; it does not renumber the acquisition. The construction takes exactly $2m+2=2d+4$ reads. It asserts a mixed gain-ray realization, without claiming complete-target recovery on this word. $\square$

## 7. A root-aware complete-target realization

**Theorem 7.1 (complete recovery within $4d+5$ reads).** There is a deterministic protocol on all of $\mathcal W_d$ recovering $(P,g,\delta)$ within $4d+5$ total reads. Its gain output is exactly $\beta$ by a fixed linear map for each terminal word; one matrix per word suffices.

**Proof and construction.** First execute the $2m$ individual $M$ actions of Theorem 5.2. After $2m+1$ reads, $\beta,\delta,U,V$ are known. Choose the least index $k$ with $\beta_k\ne0$ and set

$$
\alpha(P)=U_k/\beta_k,\qquad
\operatorname{tr}(MP)=\phi\alpha(P)+\psi(1-\alpha(P)).
\tag{7.1}
$$

This division is by a coefficient known to be nonzero. The entire polynomial $g$ is now known. Put $C_0=M^{2m}$ and $B=JC_0$.

For the first source measurement, execute $J$ and read, reaching cumulative matrix $B$. At its actual clock $i$, test the already known value $g(i)$. If it is nonzero, obtain

$$
\operatorname{tr}(BP)=(z_i-\delta)/g(i).
\tag{7.2}
$$

If it is zero, execute $J$, read, then execute another $J$, read, returning to $B$ for the next attempt. Repeat until (7.2) is available. Each return action and its read is part of the trajectory. The first of these two actions returns to $C_0$; the second returns to $B$, since $J^2=I$.

At that successful clock the cumulative matrix is $B$. Execute one $M$ and read, reaching $MB$. Test $g$ at this new actual clock. A nonzero value gives

$$
\operatorname{tr}(MBP)=(z_i-\delta)/g(i).
\tag{7.3}
$$

On a zero, execute two separate $J$ actions with their immediate reads. The second returns to $MB$ for the next attempt. Continue until (7.3) is available. Unused intermediate return reads remain counted.

Each failed attempt in either phase is at a distinct original clock and is a root of the same nonzero polynomial $g$. A nonzero polynomial of actual degree $s$ has at most $s$ distinct real roots, by successive division by its distinct linear factors. Thus the total number $f$ of failed attempts across both phases is at most $s\le d$. In particular both phases terminate. Their two first attempts cost two actions and reads, and each failure adds exactly two more. The total number of reads is

$$
(2m+1)+(2+2f)=2d+5+2f\le4d+5.
\tag{7.4}
$$

No division by an unchecked sampled value occurs. A sampled root of any multiplicity counts as one failed clock; repeated roots and roots encountered during unused return reads cannot invalidate the bound.

It remains to prove that the recovered traces determine the actual source. First $I,M,J,MJ$ are a basis of $\operatorname{Mat}_2(\mathbb R)$. Indeed a zero combination $aI+bM+cJ+eMJ$ has entries

$$
\begin{pmatrix}a+e&b+c\\b+c+e&a+b+e\end{pmatrix}=0.
$$

The off-diagonal difference gives $e=0$, the first diagonal then gives $a=0$, the second gives $b=0$, and finally $c=0$. Right multiplication by the invertible $C_0$ sends this basis to $C_0,MC_0,B,MB$. The algebra $\operatorname{span}\{I,M\}$ is preserved bijectively by that multiplication: $M^2=M+I$ and $M^{-1}=M-I$ put both $C_0$ and its inverse in this algebra. Therefore $C_0,MC_0$ span the same space as $I,M$. It follows that

$$
I,M,B,MB\quad\text{are a basis}.
\tag{7.5}
$$

The four known traces against this basis are $1,\operatorname{tr}(MP),\operatorname{tr}(BP),\operatorname{tr}(MBP)$. Nondegeneracy of the trace pairing makes their linear system uniquely determine all four entries of $P$. More explicitly, equality of these traces for two candidate matrices gives zero trace pairing of their difference with every matrix, hence with every matrix unit, forcing every entry of the difference to be zero. The actual world supplies a solution, so the uniquely recovered matrix is its positive rank-one trace-one source. Together with $g,\delta$ this recovers the complete target.

Finally pad the gain matrix of Theorem 5.2 by zero columns after its first $2m+1$ columns. For each possible terminal word this is one fixed matrix returning exactly $\beta$. The uniform finite read bound leaves only finitely many terminal words. The coefficient selection in (7.1), root tests, actions, stopping, and source reconstruction are permitted subsequent processing; they do not make the gain-readout entries depend on data. $\square$

## 8. Quantifiers and unresolved boundaries

**Corollary 8.1 (the established bounds).** The following statements hold for every declared $d\ge1$.

| Task or identity | Established read count |
| --- | --- |
| Nonzero universal scalar-linear gain identity on a mixed word | Impossible through $2d+2$ |
| Complete-target protocol with an everywhere successful countable-palette gain output | At least $2d+3$, and at most $4d+5$ |
| Gain-only extraction on a preassigned word, with countable fixed-matrix selection | Exactly $2d+3$ |
| One all-input mixed-word gain map | A realization at $2d+4$ |

**Proof.** The rows follow respectively from Theorems 3.1, 3.3 and 7.1, 5.3, and 6.1. $\square$

At $d=3$, these give the exact fixed-acquisition gain threshold of nine reads, a ten-read mixed gain construction $JM^8$, and the bounds nine through seventeen for complete recovery equipped with this gain-output mechanism. The seventeen-read bound is an upper bound for the particular root-aware construction, with no optimality claim or comparison theorem for unrestricted protocols.

A universal fixed-map identity concerns every legal world. A map may succeed only on a restricted actual branch. Lemma 2.3 connects these notions only through its explicit countable-cover hypotheses; it does not make a branch universal. Nor does a countable palette include matrices with data-dependent entries.

The exact adaptive gain-only threshold is unresolved here. Lemma 3.2 excludes pure terminal words only for correct complete-target protocols; it cannot be used to forbid pure terminal words of gain-only protocols. Thus Theorem 5.3 is not an adaptive gain-only lower bound. Likewise the mixed construction does not classify mixed identities at $2d+3$ reads or prove impossibility for all selectors at that budget. A universal identity allowed by dimension counting would still require an everywhere nonzero output, including exceptional source loci, to become a full-domain algorithm.

Unrestricted nonlinear complete recovery has no imposed gain-output mechanism. Theorems 3.3 and 8.1 do not settle whether the full cubic domain admits eight total reads, and do not prove the unrestricted bound $n_{\rm det}(3,0)\ge9$. The earlier bound $n_{\rm det}(3,0)\ge8$ is recorded in the supplied IV source with its original scope; no proof of that external earlier result is needed or imported here.

The other open questions recorded in IV also remain open: feasibility of its exceptional-pair system (6.1)–(6.4); a simultaneous third target in the same literal joint fifth-response fiber satisfying its sparse relations and all losing-child conditions; the bridge from arbitrary three-target losing families to the common-fifth hypotheses; the unrestricted local 127-coordinate system at the specified $MMJM$ parent; and the unrestricted original-root 2046-coordinate system. The complementary $JMMJ$ and $MJMM$ subtrees at their own preceding histories, and the fifth-$M$ alternative at the specified $JMJM$ parent, are separate unresolved branches. None is identified with another parent by the present arguments. Finite-tree encodings and algebraic decidability alone supply no feasibility decision. These questions are not prerequisites for the self-contained gain identities and realization in this volume.

The full coefficient space, rather than a known-factor subspace such as $g=(1+t^2)(a+bt)$, is essential in Lemmas 2.2–2.3. No conclusion here changes the validity or scope of the known-factor recovery results cited in IV. Invertible fixed changes of coefficient basis can be absorbed into the output matrix and do not change the capacity conclusions. The restriction $d\ge1$ is essential to the collinearity argument and the pure-$J$ pair; no $d=0$ assertion is made by those proofs.

No statement about empirical performance, general learning models, stability, bit or time complexity, physical acquisition cost, external originality, or literature completeness follows from these exact mathematical read counts.

## 9. Attribution and supplied-result correspondence

The normalized source and original-clock conventions agree with *FIB Self-Calibrating Relation Mathematics IV*, Definition 1.1 and Definition 10.1. Its Theorem 10.2 supplies the credited cubic mixed-word and finite-palette obstruction. The argument here proves its general-degree form directly and uses Baire category for countable palettes; the cubic finite result is not presented as new.

The supplied *Linear Gain-Ray Threshold* manuscript proposes results A–F. Their complete mathematical correspondence is:

| Supplied result | Result proved in this volume |
| --- | --- |
| A: universal collinearity and countable covering | Lemmas 2.1–2.3, on the full open parameter domain and without selector regularity |
| B: mixed obstruction and complete-protocol lower bound | Theorem 3.1, Lemma 3.2, and Theorem 3.3 |
| C: pure-$M$ obstruction | Lemmas 4.1–4.2 and Theorem 4.3, including both endpoint sign constraints |
| D: sharp fixed-acquisition threshold and exact gain/drift | Lemma 5.1 and Theorems 5.2–5.3, using trace normalization and a same-source pure-$J$ collision |
| E: mixed realization | Theorem 6.1, with original-clock $(D+1)$ jets and strictly positive output scale |
| F: complete-target realization | Theorem 7.1, with shared root counting across both phases and the four-matrix basis proof |

These proofs retain the stated outcomes of A–F without adding an adaptive sharpness claim. Spectral decomposition, polynomial root counting, Lagrange and Hermite interpolation, elementary linear algebra, and Baire category are established mathematical tools. The substantive applications here are the readout obstruction, exact threshold, and legal constructions in the specified acquisition model. Nested references and outside literature listed in IV are not additional hypotheses or externally verified inputs to these self-contained proofs.

## 追加锚（本行以下为增补区）
