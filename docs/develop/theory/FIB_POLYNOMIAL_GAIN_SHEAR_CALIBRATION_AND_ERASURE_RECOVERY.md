# Common polynomial-gain shear calibration and erasure recovery

This volume treats one strictly positive rank-one source with a common nonzero polynomial gain and a common polynomial additive drift. A predetermined forward history recovers the complete trace-normalized target in $\max(k,d)+2k+4$ scalar reads. After its specified baseline and shear prefix, exactly $k+2$ further reads are necessary and sufficient in the worst case over the declared model. The latter optimum concerns this fixed prefix, not all possible acquisition histories.

## 1. Common source, operations, clock, and target

**Definition 1.1 (original model).** Fix known integers $k,d\ge0$ and known matrices

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
U=JM=\begin{pmatrix}1&1\\0&1\end{pmatrix}.
$$

The initial relation $R=c\ell$ has four strictly positive real entries and determinant zero. The object $c$ is a strictly positive column and the instrument $\ell$ a strictly positive row, fixed within its run. Let $G$ be any nonzero real polynomial of degree at most $k$, and let $D$ be any real polynomial of degree at most $d$, including the zero polynomial. The exact reading at cumulative matrix $A_i$ is

$$
z_i=G(i)\operatorname{tr}(A_iR)+D(i).
$$

Every recorded read advances the consecutive index $i=0,1,\ldots$ once, including a repeat after an empty word. Unread operations do not advance this clock. Between reads one may execute any finite word in $M,J$, including the empty word, along the same object history. The initial matrix is $I$, its read is counted, and the subsequent word list and final read count are predetermined from $k,d$. An atom $E$ changes the cumulative matrix $A$ to $EA$. Thus the chronological atom list $(E_1,\ldots,E_n)$ has multiplier $E_n\cdots E_1$; in particular $(M,J)$ has multiplier $JM=U$.

The contract permits no reset, copy, inverse acquisition, second source, independent instrument change, extra clock, free counter, or data-dependent acquisition. Selecting two decoding positions after acquisition is an operation on the recorded data, not a change in the acquisition history. Different candidate runs may have different fixed instruments, as the source domain permits.

Put

$$
a_R=\operatorname{tr}R>0,\qquad
R_0=\frac{R}{a_R},\qquad H=a_RG.
$$

The complete recovery target is $(R_0,H,D)$, where $\operatorname{tr}R_0=1$. There is no sign restriction on $G$ and no nonzero-value assumption at any specified index, including index zero. Actual degrees may be below their announced bounds; roots may be repeated or occur anywhere on the real line.

**Lemma 1.2 (trace and legal-word interfaces).** For a matrix $C=(\begin{smallmatrix}\alpha&\beta\\\gamma&\delta\end{smallmatrix})$ and $R=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})$,

$$
\operatorname{tr}(CR)=\alpha p+\beta r+\gamma q+\delta s.
$$

For $R=c\ell$ this equals $\ell Cc$. Every cumulative legal-word matrix has nonnegative integer entries and determinant $1$ or $-1$. A strictly positive initial factorization stays positive at all read and unread states with the same fixed row.

Proof. Expanding the diagonal of $CR$ gives the trace formula. Expanding $Cc\ell$ gives $\operatorname{tr}(Cc\ell)=\ell Cc$. Both $M$ and $J$ have nonnegative integer entries and determinant $-1$; multiplication preserves nonnegative integer entries and multiplies determinants. The empty word is $I$. Finally,

$$
M\begin{pmatrix}c_1\\c_2\end{pmatrix}
=\begin{pmatrix}c_2\\c_1+c_2\end{pmatrix},\qquad
J\begin{pmatrix}c_1\\c_2\end{pmatrix}
=\begin{pmatrix}c_2\\c_1\end{pmatrix}
$$

are strictly positive when $c_1,c_2>0$. Only the column is acted on. Conversely, every strictly positive matrix $R=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})$ of determinant zero has the positive factorization

$$
c=\begin{pmatrix}p\\r\end{pmatrix},\qquad
\ell=(1,q/p),
$$

because $rq/p=s$. Thus the matrix source domain and the stated positive-factor domain agree. ∎

## 2. Elementary polynomial interfaces

**Lemma 2.1 (roots and interpolation).** A nonzero real polynomial of degree at most $n\ge0$ has at most $n$ distinct real roots. At distinct real nodes $x_0,\ldots,x_n$, arbitrary real values $y_0,\ldots,y_n$ have the unique degree-at-most-$n$ interpolant

$$
F(t)=\sum_{h=0}^{n}y_h
\prod_{\substack{0\le b\le n\\b\ne h}}
\frac{t-x_b}{x_h-x_b}.
$$

Proof. If $F(x)=0$, polynomial division by $t-x$ has remainder $F(x)=0$, so $F=(t-x)Q$. At a distinct root $y$, the equality $(y-x)Q(y)=0$ forces $Q(y)=0$. Iterating at distinct roots would force a nonzero polynomial with $n+1$ roots to have degree at least $n+1$, proving the root bound. Each displayed basis product has degree at most $n$, equals one at its own node, and vanishes at all the others. The sum therefore interpolates. Two such interpolants differ by a degree-at-most-$n$ polynomial with $n+1$ distinct roots, so the difference is zero. The denominators are nonzero node differences. For $n=0$ the product is empty and equals one. The proof includes zero interpolants and lower actual degrees and places no restriction on root signs or multiplicities. ∎

## 3. The fixed baseline, shear, and terminal history

**Definition 3.1 (one cumulative history).** Set

$$
B=\max(k,d)+1,\qquad \nu=k+2,\qquad
T=B+k+1,\qquad L=T+k+2=B+2k+3.
$$

The cumulative matrices at recorded positions are

$$
A_i=I\qquad(0\le i<B),
$$

$$
c_\ell=B+\ell-1,\qquad
A_{c_\ell}=U^\ell=\begin{pmatrix}1&\ell\\0&1\end{pmatrix}
\qquad(1\le\ell\le k+1),
$$

and

$$
A_{T+j}=U^jMU^{k+1}
=\begin{pmatrix}j&1+\nu j\\1&\nu\end{pmatrix}
\qquad(0\le j\le k+1).
$$

The complete chronological acquisition is as follows.

1. Read at $I$ with index zero, then repeat $B-1$ times: execute the empty word and read again at $I$.
2. For $\ell=1,\ldots,k+1$, execute $M$ then $J$, with no intermediate read, and read the endpoint at index $c_\ell$.
3. Execute one $M$ and read at index $T$.
4. For $j=1,\ldots,k+1$, execute $M$ then $J$, with no intermediate read, and read at index $T+j$; stop at index $L-1$.

The fixed prefix comprises steps 1 and 2. It has $T$ reads, ends at index $T-1=B+k$ and cumulative matrix $U^{k+1}$, and is the prefix used in the continuation optimum below.

**Lemma 3.2 (cumulative realization and counts).** Definition 3.1 is a legal single forward history with exactly

$$
L=\max(k,d)+2k+4
$$

reads and exactly $4k+5$ atomic operations. Its prefix uses $2(k+1)$ atoms, and its terminal continuation uses $2k+3$ atoms.

Proof. Direct multiplication gives $JM=U$. Induction on $\ell$ by left multiplication by $U$ gives $U^\ell=(\begin{smallmatrix}1&\ell\\0&1\end{smallmatrix})$, starting with $U^0=I$. After the last calibration read the matrix is $U^{k+1}$. One $M$ then gives

$$
MU^{k+1}=\begin{pmatrix}0&1\\1&k+2\end{pmatrix}.
$$

Multiplying this on the left by $U^j$ gives the claimed terminal matrix, and the next terminal matrix is obtained by one further $U$. Each such $U$ is the chronological pair $(M,J)$. Thus the displayed atom list realizes exactly every stated cumulative matrix and no additional reads. Lemma 1.2 supplies the same positive column history and fixed instrument at all intermediate states.

The three blocks have respectively $B$, $k+1$, and $k+2$ reads. Their sum is $B+2k+3$, and the last index is $T+k+1=L-1$. Initial repeats cost no atoms. The calibration costs $2(k+1)$ atoms; the terminal block costs $1+2(k+1)=2k+3$. Their sum is $4k+5$. These counts use the recorded-reading clock throughout, including the empty repeats. ∎

## 4. Complete polynomial calibration and any-two terminal inverse

**Theorem 4.1 (uniform recovery on the full original model).** The $L$ readings in Definition 3.1 uniquely recover the full target $(R_0,H,D)$ of Definition 1.1 for every allowed source and gain polynomial, including initial gain zero and all degree and root degeneracies.

Proof. Use coordinates of the single original source

$$
r=R_{21}>0,\qquad
S=\frac Rr=\begin{pmatrix}p&q\\1&s\end{pmatrix},\qquad
K=rG,\qquad a=p+s.
$$

Strict positivity gives $p,q,s>0$, and determinant zero gives $q=ps$. The polynomial $K$ is nonzero and has degree at most $k$. Define

$$
P=D+aK,\qquad \deg P\le\max(k,d)=B-1.
$$

Here and below a degree upper bound includes the zero polynomial. The normalized target in these coordinates is

$$
R_0=S/a,\qquad H=aK,\qquad D=P-aK.
$$

At every initial repeat $\operatorname{tr}S=a$, so $z_i=P(i)$ for $0\le i<B$. Lemma 2.1 therefore recovers exactly the entire polynomial

$$
P(t)=\sum_{h=0}^{B-1}z_h
\prod_{\substack{0\le b<B\\b\ne h}}\frac{t-b}{h-b}.
$$

No assumption that $P$ is nonzero is needed. At the calibration endpoint $U^\ell$, the trace is $a+\ell$. Consequently

$$
e_\ell=\frac{z_{c_\ell}-P(c_\ell)}{\ell}=K(c_\ell)
\qquad(1\le\ell\le k+1).
$$

The $k+1$ distinct indices $c_\ell$ determine exactly

$$
K(t)=\sum_{\ell=1}^{k+1}e_\ell
\prod_{\substack{1\le b\le k+1\\b\ne\ell}}
\frac{t-c_b}{c_\ell-c_b}.
$$

This division uses $\ell>0$, not a gain value. In particular a calibration value may be zero. The values cannot all be zero for an actual source, since the nonzero degree-at-most-$k$ polynomial $K$ cannot have $k+1$ distinct roots.

The $k+2$ terminal clock values are distinct, so at least two of their gains $K(T+j)$ are nonzero by Lemma 2.1. Choose any two surviving local indices $u<v$, after the fixed acquisition. At every surviving index define

$$
V_j=\frac{z_{T+j}-P(T+j)}{K(T+j)},\qquad
W_j=V_j-1-\nu j.
$$

The terminal trace formula of Lemma 1.2 is

$$
\operatorname{tr}(A_{T+j}S)
=jp+1+\nu j+q+\nu s.
$$

Since $P=D+aK$, subtracting $P$ rather than $D$ gives $V_j=\operatorname{tr}(A_{T+j}S)-a$. It follows that

$$
\begin{aligned}
W_j&=(j-1)p+q+(k+1)s\\
&=(j-1)p+s(p+k+1).
\end{aligned}
$$

Thus any two surviving positions have the global inverse

$$
p=\frac{W_v-W_u}{v-u},\qquad
s=\frac{W_u-(u-1)p}{p+k+1},\qquad
q=ps.
$$

The first formula returns the true $p>0$ because $W_v-W_u=(v-u)p$. The numerator of the second is the true $s(p+k+1)$, and its denominator is positive because $p>0,k\ge0$. Hence it returns the true $s>0$. Conversely, two positive matrices $(\begin{smallmatrix}p&ps\\1&s\end{smallmatrix})$ producing the same $W_u,W_v$ must have equal $p$ by subtraction and then equal $s$ by division by $p+k+1$. This proves injectivity for every pair on the whole positive source domain. The values $W_j$ themselves need not be positive. Every available pair returns the same source, and an additional surviving terminal sample remains an equation on that same source.

Recover $a=p+s>0$ and output $S/a,aK,P-aK$. For the original realization,

$$
\frac Sa=\frac{R/r}{a_R/r}=\frac R{a_R},\qquad
aK=\frac{a_R}{r}\,rG=a_RG.
$$

The recovered $P-aK$ is exactly the original polynomial $D$, not only its values at the sampled indices. This includes cancellations of all coefficients above degree $d$ when $d<k$.

For global target injectivity, two actual realizations with the same $L$ data first have the same $P$ by baseline interpolation and the same nonzero $K$ by calibration interpolation. Their terminal zero sets are identical, so the same surviving pair can be used for both. The positive pair inverse gives the same $p,s,S,a$, and then the same entire $R_0,H,D$. Every step used coordinates of one common source, gain, and drift; no independently lifted relations are fitted. ∎

**Corollary 4.2 (division domains and endpoints).** Every denominator in Theorem 4.1 is justified on the full model. Its bound includes $k=0$, $d=0$, lower actual degrees, vanishing leading coefficients, arbitrary repeated roots, and gain zeros at baseline, calibration, or terminal positions.

Proof. The baseline denominators $h-b$ are nonzero integers. The calibration denominators are $\ell>0$ and $c_\ell-c_b=\ell-b\ne0$. Terminal gain division is performed only at indices already determined to have $K(T+j)\ne0$, with either sign permitted. The pair divisor $v-u$ is a positive integer, the source divisor $p+k+1$ is strictly positive, and the final divisor $a=p+s$ is strictly positive. The derivational normalizations use only $r>0$ and $a_R>0$. No leading coefficient, gain coefficient, prescribed gain sample, baseline gain, or calibration gain is a divisor.

If $k=0$, then $B=d+1$, the one calibration read determines the nonzero constant $K$, and both terminal readings survive. There are $d+4$ reads and five atoms. In particular $k=d=0$ gives the four endpoints $I,U,MU,UMU$, indexed $0,1,2,3$, and the same inverse with denominator $p+1>0$. If $d=0$ and $k$ is arbitrary, the count is $3k+4$, and $P-aK$ is the original constant drift.

For any $k,d$, interpolation uses degree upper bounds alone, so no highest coefficient is required to be nonzero and $P$ may be identically zero. If $G(0)=0$, the initial reading is simply $z_0=D(0)$, and the same baseline interpolation applies. Calibration gain zeros give $e_\ell=0$ without a zero denominator. Terminal gain zeros are omitted only from the division; their observation equations remain part of the model. The root proof counts distinct roots, regardless of signs, multiplicities, or noninteger locations. Thus none of these cases changes the argument. ∎

## 5. Necessary and sufficient finite-data compatibility

**Proposition 5.1 (one common-source existence criterion).** For arbitrary real data $z_0,\ldots,z_{L-1}$ on Definition 3.1's path and clock, the following sequential criterion is necessary and sufficient for a realization in Definition 1.1.

1. Interpolate $P$ and $K$ by Theorem 4.1's formulas. Require $K\not\equiv0$.
2. Choose the two smallest terminal local indices $u<v$ for which $K(T+j)\ne0$. Compute $W_u,W_v$ and $p$ by the stated inverse. Require $p>0$, then compute $s$ using $p+k+1>0$ and require $s>0$.
3. Set $q=ps$, $S=(\begin{smallmatrix}p&q\\1&s\end{smallmatrix})$, $a=p+s$, $R_0=S/a$, $H=aK$, and $D=P-aK$. Require $\deg D\le d$, meaning that every coefficient above degree $d$ vanishes.
4. Require every original observation equation, at all recorded indices:

$$
z_i=K(i)\operatorname{tr}(A_iS)+D(i)
=H(i)\operatorname{tr}(A_iR_0)+D(i)
\qquad(0\le i<L).
$$

At any zero of $K$ this is precisely $z_i=D(i)$. It includes all baseline and calibration positions, all unused terminal survivors, and every zero-gain position.

Proof. Interpolation is always defined, even for arbitrary data. Once $K\not\equiv0$, its degree is at most $k$ by construction, so at least two terminal positions survive. Hence the two gain quotients and $v-u$ division are defined. Requiring $p>0$ before the $s$ formula ensures its positive denominator, and requiring $s>0$ ensures $a>0$. Thus the criterion does not use an undefined later construction at an earlier rejected input.

For actual data Theorem 4.1 returns the true $S,K,P$ and hence the true positive $p,s$, complete drift $D$, and normalized target. All degree conditions and every recorded equation are then necessary, including the equations at gain roots.

Conversely suppose all conditions hold. The constructed $S$ has strictly positive entries and determinant $ps-q=0$. Therefore $R_0=S/a$ is strictly positive, rank one, and of trace one. The polynomial $H=aK$ is nonzero and of degree at most $k$; the explicitly checked $D$ has degree at most $d$. Choose the original realization

$$
R=R_0,\qquad G=H,\qquad
c=\begin{pmatrix}p\\1\end{pmatrix},\qquad
\ell=(1/a,s/a).
$$

These positive factors satisfy

$$
c\ell=\frac1a\begin{pmatrix}p&ps\\1&s\end{pmatrix}=R_0.
$$

Execute the chronological word list of Definition 3.1 on this one column with this fixed row and these single polynomials. Lemma 3.2 gives every cumulative endpoint, and condition 4 gives every proposed reading at its actual clock index. This is one common-source realization of the full finite data. Its target is unique by Theorem 4.1. The degree test in condition 3 is essential when $d<k$; otherwise the construction could supply an impermissible drift. ∎

## 6. Exact scale and forward-reading fibres

**Theorem 6.1 (complete positive-scale fibre).** For compatible data, all original-model realizations are exactly

$$
R=tR_0,\qquad G=H/t,\qquad D\text{ fixed},\qquad t>0.
$$

Equivalently, in Theorem 4.1's coordinates they are $R=\rho S$, $G=K/\rho$, $\rho>0$. Two original realizations have the same specified finite data if and only if

$$
R'=\lambda R,\qquad G'=G/\lambda,\qquad D'=D
\quad\text{for some }\lambda>0.
$$

All members give identical readings along any common future known $M/J$ history at the same recorded indices. The positive factorization of each $R$ has the additional internal freedom $c'=\mu c$, $\ell'=\ell/\mu$, $\mu>0$, and no other positive-factor freedom.

Proof. Every realization has the recovered target by Theorem 4.1. Taking $t=\operatorname{tr}R>0$ in $R/\operatorname{tr}R=R_0$ and $(\operatorname{tr}R)G=H$ proves necessity of the first parameterization and fixes $D$. Conversely every $t>0$ preserves positivity, rank one, nonzero gain, and both degree bounds. For every known cumulative matrix $C$ and recorded index $n$,

$$
\frac{H(n)}t\operatorname{tr}(C\,tR_0)+D(n)
=H(n)\operatorname{tr}(CR_0)+D(n).
$$

This proves finite-data sufficiency and future agreement. Any extension containing the finite history can have no additional normalized ambiguity, since its identical data include the finite identifying data. As $R_0=S/a$, the alternate parameter is $\rho=t/a>0$. Comparing two positive traces gives $\lambda=t'/t$, proving the equivalence for two realizations.

Finally suppose $c\ell=c'\ell'$ with all vector components positive. Equality of first columns gives $c'=(\ell_1/\ell'_1)c=\mu c$ with $\mu>0$. Equality of each remaining column and a positive component of $c$ then forces $\ell'=\ell/\mu$. Conversely those changes preserve the outer product. This internal scale does not change $R$ and is separate from relation/gain rescaling. ∎

## 7. An arbitrary-endpoint positive-source collision

**Lemma 7.1 (same-prefix collision at every legal endpoint).** For every finite cumulative $M/J$ word matrix $C$, there are an $x>0$ and distinct $u_-,u_+\in(0,x)$ such that the strictly positive rank-one sources

$$
R_x(u)=\begin{pmatrix}x-u&u(x-u)\\1&u\end{pmatrix}
=\begin{pmatrix}x-u\\1\end{pmatrix}(1,u)
$$

have equal signals at $I$, at every $U^\ell$ for $\ell\ge0$, and at $C$. They have equal trace $x$ but different normalized matrices $R_x(u)/x$.

Proof. For $0<u<x$ all displayed entries and factors are strictly positive, the determinant is $(x-u)u-u(x-u)=0$, and the trace is $x$. Lemma 1.2 gives

$$
\operatorname{tr}(U^\ell R_x(u))=x+\ell,
$$

independently of $u$. Write $C=(\begin{smallmatrix}\alpha&\beta\\\gamma&\delta\end{smallmatrix})$. Its signal is

$$
f_C(u)=\alpha x+\beta+(\delta-\alpha)u+\gamma u(x-u).
$$

If $\gamma=0$, Lemma 1.2 gives $\det C=\alpha\delta\in\{1,-1\}$. Nonnegativity excludes $-1$, and nonnegative integer factors with product one force $\alpha=\delta=1$. Thus $f_C(u)=x+\beta$ is constant. Choose $x=2$, $u_-=2/3$, $u_+=4/3$.

If $\gamma>0$, put

$$
\Delta=\delta-\alpha,\qquad
x=1+\frac{|\Delta|}{\gamma},\qquad
u_* =\frac{x+\Delta/\gamma}{2}.
$$

The strict inequality $x>|\Delta|/\gamma$ gives $0<u_*<x$. Define

$$
\varepsilon=\frac12\min(u_*,x-u_*)>0,\qquad
u_-=u_*-\varepsilon,\qquad u_+=u_*+\varepsilon.
$$

These are distinct points of $(0,x)$. Direct subtraction gives, for any $u,v$,

$$
f_C(v)-f_C(u)
=(v-u)\bigl[\Delta+\gamma(x-u-v)\bigr].
$$

At the chosen pair $u_-+u_+=x+\Delta/\gamma$, so the bracket is zero. The endpoint signals therefore agree. Both cases cover every legal $C$, including triangular matrices, repeated endpoints, and arbitrarily long finite words.

The sources differ in their lower-right entries while both traces equal $x>0$, so their trace-normalized matrices differ. Their explicit factorizations give one fixed positive row per run, and Lemma 1.2 preserves positivity throughout every intervening word. ∎

## 8. Exact continuation optimum after the fixed prefix

**Theorem 8.1 (exactly $k+2$ further reads).** Fix the entire prefix of Definition 3.1: $B$ reads at $I$ and then the $k+1$ reads at $U,\ldots,U^{k+1}$ on the same recorded-reading clock. For every predetermined legal continuation with at most $k+1$ further reads, two original-model realizations have identical full data but different complete normalized targets. The smallest uniform further-read bound over predetermined legal continuations of this prefix is therefore exactly $k+2$, and the corresponding total-read optimum is

$$
T+k+2=B+2k+3=\max(k,d)+2k+4.
$$

Proof. Consider an arbitrary continuation with $m\le k+1$ reads. Let its predetermined finite word multipliers be $W_0,\ldots,W_{m-1}$, each possibly $I$. Its cumulative matrices and exact read indices are

$$
C_h=W_h\cdots W_0U^{k+1},\qquad i=T+h
\qquad(0\le h<m).
$$

Each $C_h$ is a legal cumulative word matrix by Lemma 1.2. No bound on the word lengths or additional condition on the endpoints is imposed.

First suppose $m\le k$. Set $x=2$, $u_-=2/3$, $u_+=4/3$, and use sources $R_-=R_x(u_-)$ and $R_+=R_x(u_+)$. In both runs choose the same polynomials

$$
G(t)=\prod_{h=0}^{m-1}(t-(T+h)),\qquad D(t)=0.
$$

For $m=0$ the product is one. In every case $G$ is monic, nonzero, and of degree $m\le k$; $D=0$ satisfies every $d\ge0$. The sources have equal signals $x$ at every baseline read and $x+\ell$ at the calibration read at $U^\ell$. Multiplication by the same $G$ at the same prefix indices gives identical complete prefix data. At each continuation read $T+h$, the gain is zero, so both observed values are zero independently of $C_h$. This constructs a collision for every such shorter continuation, including no continuation.

Now suppose $m=k+1$. Apply Lemma 7.1 to the actual last cumulative matrix $C=C_k$, obtaining $x,u_-,u_+$ and sources $R_-,R_+$. Use in both runs

$$
G(t)=\prod_{h=0}^{k-1}(t-(T+h)),\qquad D(t)=0.
$$

For $k=0$ this is the constant one; otherwise it is a monic degree-$k$ polynomial. The first $k$ continuation readings vanish for both sources. At the last index,

$$
G(T+k)=\prod_{h=0}^{k-1}(k-h)>0,
$$

including the empty product one. Their last unweighted signals are equal by Lemma 7.1, so multiplying by this same nonzero gain yields equal last readings. The entire prefix agrees for the same reason as before: the sources have common trace $x$ and lower-left entry one and thus common signals at all its cumulative matrices. All observations occur at the original consecutive indices with no change of clock, source, gain, or drift.

In either case the actual original sources are the displayed $R_-,R_+$, each with its explicit positive column and fixed positive row, and the single chosen $G,D$ are used throughout its run. Lemma 1.2 supplies positive read and unread states for every prescribed atom. Their complete targets are

$$
\left(R_-/x,xG,0\right),\qquad
\left(R_+/x,xG,0\right).
$$

The normalized lower-right entries $u_-/x$ and $u_+/x$ differ. If $R_+=\lambda R_-$ for $\lambda>0$, taking traces would give $x=\lambda x$, hence $\lambda=1$, contradicting their different lower-right entries. Thus the collision is a genuine normalized-target distinction, not the positive-scale fibre. It occurs between actual common-source realizations, not separately fitted sample relations.

The words are predetermined, so the two runs also have the same operation history. Any output based on the identical data and history is the same for both and cannot equal both targets. If a predetermined finite word list permits data-dependent early stopping, the collision for its full list also gives identical histories up to each earlier stopping decision. Both runs therefore stop together with the same output; early stopping does not remove this obstruction.

This proves failure of every continuation with at most $k+1$ further reads. The terminal family of Definition 3.1 succeeds uniformly with $k+2$ further reads by Theorem 4.1. The lower and upper bounds match, proving the stated exact optimum for this prefix. Root counting supplies the upper survivor count; the arbitrary-endpoint positive-source collision supplies the separate necessity argument. ∎

**Corollary 8.2 (endpoint scope of necessity).** The continuation optimum includes all $k,d\ge0$, but its necessity is a worst-case statement over the announced model, not a statement for every fixed gain polynomial or prescribed root pattern.

Proof. When $k=0$, $m=0$ falls in the first case with constant gain one, and $m=1$ falls in the second case with the same constant gain and Lemma 7.1's arbitrary-endpoint collision. Thus one further read fails and the two surviving upper-family reads suffice. Here $B=d+1$, giving $d+4$ total reads; for $k=d=0$ these are exactly $I,U,MU,UMU$. For every $d$, the lower examples use legal zero drift, so they remain in the degree-$d$ model, including $d=0$. For every relative size of $k,d$, the gain degrees in the lower examples are at most $k$ and their targets remain distinct as proved. These examples establish a uniform worst-case lower bound without requiring that each allowed gain have $k$ actual roots. The upper theorem, separately, applies to every allowed gain, including lower actual degree and initial zero. ∎

## 9. Comparison, credits, and mathematical boundaries

**Proposition 9.1 (strict read improvement and separate atom accounting).** Section 39 of [FIB self-calibrating relation mathematics](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md) gives $3k+d+5$ reads for the same complete target and full polynomial-gain domain. The present fixed history saves exactly $\min(k,d)+1>0$ reads. Its literal atom count minus that source history's literal atom count is $k+1-d$.

Proof. In Section 39 put $N=2k+d+3$. Its history has cumulative matrices $M^i$ for $0\le i<N$, then $M^jJM^{N-1}$ for $0\le j\le k+1$. It has $N+k+2=3k+d+5$ reads. The $N-1$ initial moves use one $M$ each, the switch uses one $J$, and the remaining $k+1$ moves use one $M$ each, so it has $N-1+1+(k+1)=3k+d+4$ atoms. Lemma 3.2 gives the present counts. Subtraction gives

$$
\begin{aligned}
(3k+d+5)-(\max(k,d)+2k+4)
&=k+d+1-\max(k,d)\\
&=\min(k,d)+1>0,
\end{aligned}
$$

and

$$
(4k+5)-(3k+d+4)=k+1-d.
$$

Thus the present literal construction uses fewer atoms when $d>k+1$, the same number when $d=k+1$, and more when $d<k+1$. A read improvement alone supplies no atom improvement. The comparison is of sufficient constructions, not a minimal-atom assertion. ∎

The common positive rank-one model, trace convention, counted initial read, finite-composite-word and empty-word contract are those of Definitions 10.1–10.3 of the self-calibration source. Its Definition 39.1 supplies exactly the normalized target used here, without initial-gain or root restrictions. Its Section 39 supplies the older full-model upper bound and the common-source compatibility and positive-scale perspective. Its four-trace inverse, Fibonacci closure, and polynomial-drift and lifted-gain tools are background results; no independent lifted matrices or confluent evaluation inverse are needed by the present proof.

The repeated-initial-baseline and shear-calibration ideas are from the companion *Shared affine gain and zero-crossing recovery*, particularly its Theorem 2.1. Its Theorem 4.1 supplies the affine single-endpoint collision mechanism: keep the trace and lower-left entry fixed, use the quadratic endpoint signal, and erase another read with a gain root. Both volumes use $U=JM$, with chronological atoms $M$ then $J$.

The additional full-model upper construction interpolates the one polynomial $K=rG$ from $k+1$ shear samples after $B=\max(k,d)+1$ baseline reads. Its terminal family $U^jMU^{k+1}$ has the all-pairs identity $W_j=(j-1)p+s(p+k+1)$, giving a global positive inverse from any two surviving gain positions. This supplies the strictly smaller bound for the entire original model. The continuation theorem extends the credited affine collision mechanism by a degree-at-most-$k$ gain that erases all but at most one read, then collides at the arbitrary surviving cumulative endpoint. These statements make no claim of literature priority.

The fixed-prefix optimum does not settle the minimum over different prefixes or all predetermined histories, the original all-fixed-path sharp affine question, a global polynomial-gain optimum, or adaptive acquisition. For the positive-initial-intercept affine submodel, the target correspondence is

$$
S_{\mathrm{aff}}=\alpha R,\quad \kappa=\beta/\alpha,\quad
R_0=\frac{S_{\mathrm{aff}}}{\operatorname{tr}S_{\mathrm{aff}}},\quad
H(t)=(\operatorname{tr}S_{\mathrm{aff}})(1+\kappa t),\qquad \alpha>0.
$$

Conversely $H(0)>0$ gives $S_{\mathrm{aff}}=H(0)R_0$ and $\kappa=H'(0)/H(0)$. At $k=1$ the present full-model bound is $\max(d+6,7)$; its validity also at $G(0)=0$ does not supply a global sharpness theorem for that affine programme.

The optimized resource is the number of exact scalar reads after the specified prefix. The $4k+5$ atom count is a construction upper count. The finite-composite-word and empty-word contract is essential to the stated history; it differs from a requirement to read after every atom. Strict positivity, rank one, the known $M,J$, one common nonzero bounded-degree gain, one common bounded-degree drift, exact real arithmetic, and the recorded-reading clock remain assumptions. The recovered relation does not separately determine an absolute object and instrument or an original ordered tree.

Zero relation and zero-trace sources are outside this domain, where trace normalization would fail. Identically zero gain is excluded: with $G\equiv0$ every relation gives only $D(i)$, so the relation is unidentifiable. Finite compatibility proves existence within the declared degree-bounded model. It does not establish an undeclared functional bound: adding a nonzero multiple of $\prod_{i=0}^{L-1}(t-i)$ to an otherwise unrestricted drift leaves these finite data unchanged and changes later values. Nor does it identify an external time origin in a translation-closed polynomial family: replacing an origin $\tau$ by $\tau+h$ and functions $G(t),D(t)$ by $G(t-h),D(t-h)$ preserves their values at $i+\tau$. These are algebraic limits of the recovery target and assumptions.

## 追加锚（本行以下为增补区）
