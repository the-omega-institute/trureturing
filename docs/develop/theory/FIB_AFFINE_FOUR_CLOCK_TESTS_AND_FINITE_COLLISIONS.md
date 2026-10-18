# Four recorded-clock tests, exhaustive constant-diagonal classification, and finite collisions with affine gain

Two additional necessary determinant equalities strengthen the two credited off-diagonal tests for five-read constant-drift recovery in a specified diagonal endpoint stratum. An infinite family passes both earlier tests and every noninitial erasure-span test but fails the added conditions. The complete regular class satisfying all four equalities is then classified: its endpoints are forced to be the single history $H_3$, whose finite positive-source collision therefore excludes the whole class. The mirrored upper-left stratum has the same classification. The unrestricted constant-drift optimum remains $5\le C_{\mathrm{fix}}(0)\le6$.

## 1. The original model and its representation fibres

Set

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
U=JM=\begin{pmatrix}1&1\\0&1\end{pmatrix},\quad
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix}.
$$

A predetermined history has $A_0=I$ and $A_{i+1}=W_iA_i$, where each $W_i$ is a finite word in $M,J$, possibly empty. Products act on the left and execute from right to left. Chronological $(M,J)$ implements $U$, and $(J,M)$ implements $L$. Every scalar read advances the recorded index by one; an unread atom does not. In the five-read problem the indices are exactly $0,1,2,3,4$.

The original all-degree programme has effective target $(S,k,D)$ and readings

$$
S=\begin{pmatrix}p&q\\r&s\end{pmatrix},\qquad
p,q,r,s>0,\quad ps=qr,\qquad
z_i=(1+ki)\operatorname{tr}(A_iS)+D(i),
\tag{1.1}
$$

where $k\in\mathbb R$ is arbitrary and $D\in\mathbb R[\tau]$ has degree at most a known $d\ge0$. The zero polynomial and smaller actual degrees are included. The new obstructions concern $d=0$, so each run has one entire constant polynomial $D(\tau)=\delta$. Neither the gain domain nor the target is reduced: sampled gain zeros and negative gains remain allowed.

In original parameters, $S=\alpha R$, $k=\beta/\alpha$, with $\alpha>0$, arbitrary real $\beta$, and a single strictly positive rank-one relation $R$. Every source in (1.1) has the actual realization

$$
\alpha=1,\quad\beta=k,\quad R=S,\qquad
c=\binom p r,\quad \ell=(1,q/p),\quad c\ell=S.
\tag{1.2}
$$

The last equality follows from $s=qr/p$. For $A=(\begin{smallmatrix}a&b\\c_1&e\end{smallmatrix})$,

$$
\ell A c=\operatorname{tr}(AS)=ap+b r+c_1q+es.
\tag{1.3}
$$

The row $\ell$ stays fixed throughout its run. Both $M(x,y)^{\mathsf T}=(y,x+y)^{\mathsf T}$ and $J(x,y)^{\mathsf T}=(y,x)^{\mathsf T}$ preserve strictly positive columns. Thus (1.2) realizes every recorded and unread state on every history used below. Candidate runs may have different fixed rows. No reset, source copy, inverse acquisition, independent lifted source, alternative unexecuted history, or additional acquisition clock is used.

For a fixed effective target, its exact original relation/gain fibre is

$$
R=S/b,\qquad\alpha=b>0,\qquad\beta=bk,\qquad D\text{ fixed}.
\tag{1.4}
$$

Necessity follows from the definitions, and substitution proves sufficiency at every index on any common history. For a fixed $R=c\ell$, all positive factorizations are exactly $c'=\mu c$, $\ell'=\ell/\mu$, $\mu>0$: equality of first columns fixes this scalar and equality of second columns fixes the other row component. These are representation freedoms for a fixed target. A history with collisions can have several different effective targets, each with its own representation fibre. Every collision below changes the effective target itself.

## 2. Two credited bridges, with proofs on actual sources

Every cumulative word matrix is nonnegative integral and has determinant $\pm1$.

**Lemma 2.1 (noninitial erasure-span obstruction).** If deleting some $j\in\{1,2,3,4\}$ leaves matrices with span of dimension at most three, the five-read history has a finite collision between distinct positive rank-one sources at common slope $k=-1/j$ and common drift zero. Hence uniform recovery requires four independent survivors after every noninitial deletion.

**Proof.** The survivors include $I$. Choose $A,B$ so that $I,A,B$ span them, repeating $I$ if necessary. Two homogeneous equations in three unknowns give a nonzero trace-zero matrix

$$
X=\begin{pmatrix}a&b\\c_1&-a\end{pmatrix}
$$

annihilating $A,B$ under the trace pairing. For $A=(\begin{smallmatrix}u&v\\w&e\end{smallmatrix})$ its equation is $(u-e)a+wb+vc_1=0$.

If $a\ne0$ or $bc_1<0$, the coefficients $a,-b,-c_1,-a$ have both strict signs. Otherwise orient $X$ so that $b,c_1\ge0$, not both zero. Nonnegativity then forces the corresponding off-diagonal entry of each selected matrix to vanish. Such a triangular nonnegative integral unimodular matrix has diagonal entries both one. Consequently $\operatorname{diag}(1,-1)$ annihilates $I,A,B$ as well. Replace $X$ by it. In either case we have a nonzero annihilator $X=(\begin{smallmatrix}a&b\\c_1&e\end{smallmatrix})$ for which $a,-b,-c_1,e$ contain both strict signs.

Put

$$
E(x,y)=\begin{pmatrix}xy&x\\y&1\end{pmatrix},\qquad
f(x,y)=exy+a-c_1x-by\quad(x,y>0).
$$

This function takes both signs. Indeed its values at $(\epsilon,\epsilon)$ tend to $a$, while its values divided by $T^2$ at $(T,T)$, and divided by $T$ at $(T,T^{-2})$ and $(T^{-2},T)$, tend respectively to $e,-c_1,-b$. Each strictly signed coefficient supplies a positive point of that sign. Join two such points by a positive straight segment with endpoint values $f_-<0<f_+$. On this compact segment every entry of $E$ is at least some $m>0$.

Write $\Delta=\det X$ and choose

$$
\lambda>\max\left\{\frac{\max_{a,b}|X_{ab}|}{m},
\frac{|\Delta|}{\min(-f_-,f_+)}\right\}.
$$

The intermediate value theorem supplies a segment point with $f=-\Delta/\lambda$. At that point $S_0=\lambda E$ and $S_1=S_0+X$ are strictly positive, distinct, and have zero determinant, since $\det S_1=\lambda f+\Delta=0$. They are therefore rank one. Their surviving traces agree. The only remaining index has gain zero at $k=-1/j$, so all five observations agree with drift zero. Equation (1.2) and positivity under each atom realize these sources on the original words with one fixed row per run. ∎

For the second bridge define auxiliary full-matrix maps

$$
\mathcal L(X)_i=\operatorname{tr}(A_iX),\qquad
\mathcal Qv=(v_i-v_0)_{i=1}^4,\qquad
(\mathcal Iv)_i=iv_i,
$$

$$
\mathsf B=\mathcal Q\mathcal L,\qquad
\mathsf C=\mathcal Q\mathcal I\mathcal L,\qquad
\mathsf T_k=\mathsf B+k\mathsf C.
\tag{2.1}
$$

The kernel of $\mathcal Q$ consists exactly of constant five-vectors. Use the bilinear determinant polarization

$$
\mathfrak b(X,Y)=\det(X+Y)-\det X-\det Y,
$$

$$
\mathfrak b(S,Y)=sY_{11}+pY_{22}-rY_{12}-qY_{21}.
\tag{2.2}
$$

In particular $\det(S+\epsilon Y)=\det S+\epsilon\mathfrak b(S,Y)+\epsilon^2\det Y$. Full matrices in these linear maps are auxiliary; actual sources retain positivity and rank one.

**Lemma 2.2 (finite sign transfer).** Suppose $\mathsf T_a$ is invertible and $\mathsf H=\mathsf T_a^{-1}\mathsf C$. If $\mathfrak b(S,\mathsf H S)$ takes both strict signs on positive rank-one sources, there are actual collisions with slopes $a,a+\epsilon$ for arbitrarily small $\epsilon>0$ and one entire constant drift per run.

**Proof.** Write every positive rank-one source as

$$
S=\sigma E(u,v),\qquad
E(u,v)=\begin{pmatrix}uv&u\\v&1\end{pmatrix},\qquad\sigma,u,v>0.
\tag{2.3}
$$

Interpolate the positive parameters of two strictly signed sources. This gives a compact path of positive rank-one sources $S(\theta)$. Let $m>0$ be a common lower bound for its entries, let $K=1+\max_{\theta,a,b}|(\mathsf H S(\theta))_{ab}|$, and let $\eta>0$ be the smaller magnitude of the endpoint transfer-form values. For

$$
0<\epsilon<\min\{m/(2K),\eta/(4K^2)\},
$$

with any further prescribed positive upper bound, $S+\epsilon\mathsf H S$ remains positive. Also $|\det(\mathsf H S)|\le2K^2$, so the continuous function

$$
\mathfrak b(S,\mathsf H S)+\epsilon\det(\mathsf H S)
$$

retains opposite endpoint signs and has a zero. At that zero set $S_1=S$ and $S_0=S+\epsilon\mathsf H S$. The determinant expansion makes both sources rank one, and

$$
\mathsf T_aS_0=\mathsf T_aS_1+\epsilon\mathsf CS_1
=\mathsf T_{a+\epsilon}S_1.
\tag{2.4}
$$

Therefore their undrifted five-vectors differ by one constant, whose initial value is $u_0=\operatorname{tr}(S_0-S_1)$. Taking

$$
k_0=a,\quad k_1=a+\epsilon,\qquad
D_0(\tau)=0,\quad D_1(\tau)=u_0
\tag{2.5}
$$

makes every original reading agree, including the initial reading. The slopes differ, so the effective targets differ. Equation (1.2) realizes both runs with positive unread states and fixed positive rows. If $|a|<1/16$ and $\epsilon<1/16$, both slope magnitudes are less than $1/8$, and every gain at $0\le i\le4$ exceeds $1/2$. No gain division is used. ∎

## 3. Four necessary recorded-clock equalities

Assume the exact endpoint stratum

$$
(A_i)_{22}=1\qquad(0\le i\le4).
\tag{3.1}
$$

Define five-vectors and coordinatewise products

$$
\mathbf1=(1,1,1,1,1)^{\mathsf T},\quad
\mathbf t=(0,1,2,3,4)^{\mathsf T},\quad
\mathbf x=((A_i)_{21})_i,\quad
\mathbf y=((A_i)_{12})_i,\quad
\mathbf d=((A_i)_{11}-1)_i,
$$

$$
\mathbf t\mathbf x=(ix_i)_i,\qquad
\mathbf t\mathbf y=(iy_i)_i.
$$

**Theorem 3.1.** Uniform recovery of the entire constant-drift target requires

$$
\begin{aligned}
\Delta_x&=\det[\mathbf1,\mathbf t,\mathbf x,\mathbf y,\mathbf t\mathbf x]=0,\\
\Delta_y&=\det[\mathbf1,\mathbf t,\mathbf x,\mathbf y,\mathbf t\mathbf y]=0,\\
\Delta_{px}&=\det[\mathbf1,\mathbf t,\mathbf x,\mathbf d,\mathbf t\mathbf x]=0,\\
\Delta_{yp}&=\det[\mathbf1,\mathbf t,\mathbf d,\mathbf y,\mathbf t\mathbf y]=0.
\end{aligned}
\tag{3.2}
$$

The first two are credited prior conditions. More precisely, suppose that deleting any noninitial endpoint leaves four independent matrices. If any determinant in (3.2) is nonzero, the original five readings have a finite collision between distinct actual targets with both slopes arbitrarily close to zero and all sampled gains strictly positive. There is no additional independence assumption on $\mathbf1,\mathbf t,\mathbf x,\mathbf y$.

**Proof.** Assume the survivor-span hypothesis for the stronger assertion. The endpoints span the four-dimensional matrix space, so $\mathcal L$ is injective. With $K_0=E_{22}$, (3.1) gives $\mathcal L K_0=\mathbf1$, and hence

$$
\ker\mathsf B=\mathbb RK_0,\qquad\operatorname{rank}\mathsf B=3,
\qquad \mathsf C K_0=\mathbf e=(1,2,3,4)^{\mathsf T}.
\tag{3.3}
$$

The pencil $\mathsf T_k$ is regular. At $k=-1/j$, $\mathsf T_kX=0$ says $(1-i/j)\operatorname{tr}(A_iX)$ is constant. Its value at $j$ is zero. All other gains are nonzero, so the four independent survivors force $X=0$. Thus $\mathsf T_{-1/j}$ is invertible. Its determinant is a nonzero polynomial in $k$, and $\mathsf T_a$ is invertible for every sufficiently small nonzero $a$.

Choose a nonzero left null covector $w$ of $\mathsf B$. The functional $h=w\mathsf C$ is nonzero, since otherwise every $\mathsf T_k$ would have range in $\ker w$, contradicting regularity. At a positive rank-one $S$, its determinant tangent space is

$$
V_S=\{V:\mathfrak b(S,V)=0\}.
$$

It has dimension three, and $\mathfrak b(S,K_0)=p>0$. Therefore $\mathsf B$ maps $V_S$ isomorphically onto its range. The quotient derivative at slope zero,

$$
(V,\lambda)\longmapsto\mathsf BV+\lambda\mathsf CS,
$$

is invertible precisely when $h(S)\ne0$. Such a source exists: if $h(E(u,v))=h_puv+h_qu+h_rv+h_s$ vanished for every $u,v>0$, the polynomial root bound first in $u$, then in $v$, would force all coefficients to vanish.

Introduce four-vectors

$$
\mathbf a=\mathsf BE_{12},\quad\mathbf b=\mathsf BE_{21},\quad
\mathbf c=\mathsf BE_{11},\qquad
\mathbf A=\mathsf CE_{12},\quad\mathbf B'=\mathsf CE_{21},\quad
\mathbf C'=\mathsf CE_{11}.
$$

They are the tails at indices $1,\ldots,4$ of $\mathbf x,\mathbf y,\mathbf d,\mathbf t\mathbf x,\mathbf t\mathbf y,\mathbf t+\mathbf t\mathbf d$, respectively. In particular, $(\mathbf C\prime)_i=i(A_i)_{11}=i(1+d_i)$ on these tail indices. The vectors $\mathbf a,\mathbf b,\mathbf c$ are independent by (3.3). In chart (2.3),

$$
\mathsf T_k(\sigma E(u,v))=\sigma F(u,v,k),
$$

$$
F=k\mathbf e+u(\mathbf a+k\mathbf A)
+v(\mathbf b+k\mathbf B')+uv(\mathbf c+k\mathbf C').
\tag{3.4}
$$

Its derivative determinant in coordinates $(\sigma,u,v,k)$ is $\sigma^3j(u,v,k)$, where $j=\det[F,F_u,F_v,F_k]$. The chart inverse is $\sigma=s,u=q/s,v=r/s$, so the preceding interior nonsingularity gives $j(\bar u,\bar v,0)\ne0$ for some $\bar u,\bar v>0$.

The exact polynomial boundary identities are

$$
j(u,0,k)=ku\det[\mathbf e,\mathbf a,
\mathbf b+k\mathbf B'+u(\mathbf c+k\mathbf C'),\mathbf A],
\tag{3.5}
$$

$$
j(0,v,k)=kv\det[\mathbf e,
\mathbf a+k\mathbf A+v(\mathbf c+k\mathbf C'),\mathbf b,\mathbf B'].
\tag{3.6}
$$

For (3.5), subtract $uF_u$ from the first column, leaving $k\mathbf e$, and use $F_k=\mathbf e+u\mathbf A$. The second column's $k\mathbf A$ term then vanishes against the last. Subtracting $vF_v$ and using $F_k=\mathbf e+v\mathbf B'$ proves (3.6). These are auxiliary boundary evaluations; no boundary source is used as an actual run.

The coefficients of $k$ at zero in (3.5) and (3.6) are

$$
u_x(u)=u\{\det[\mathbf e,\mathbf a,\mathbf b,\mathbf A]
+u\det[\mathbf e,\mathbf a,\mathbf c,\mathbf A]\},
$$

$$
u_y(v)=v\{\det[\mathbf e,\mathbf a,\mathbf b,\mathbf B']
+v\det[\mathbf e,\mathbf c,\mathbf b,\mathbf B']\}.
\tag{3.7}
$$

All nonconstant five-vectors in (3.2) have coordinate zero at index zero. Expansion in that row identifies the four determinants in (3.7) with $\Delta_x,\Delta_{px},\Delta_y,\Delta_{yp}$, respectively.

If $\Delta_x$ or $\Delta_{px}$ is nonzero, choose $u_*>0$ for which $u_*(\Delta_x+u_*\Delta_{px})\ne0$. Such a point exists because this polynomial is not identically zero. Then $j(u_*,0,k)$ has a simple zero at $k=0$ and opposite strict signs for sufficiently small positive and negative $k$. Choose the sign of an arbitrarily small nonzero $a$ so that its boundary sign is opposite to $j(\bar u,\bar v,0)$. Also require $\mathsf T_a$ invertible, $|a|<1/16$, and preservation of the interior sign at $a$. Regularity and continuity allow all of these choices. Finally choose $v_*>0$ sufficiently small to preserve the boundary sign at $(u_*,v_*,a)$. This gives two actual positive sources with opposite $j$ signs at the same invertible slope. If $\Delta_y$ or $\Delta_{yp}$ is nonzero, (3.6) gives the same argument with the roles of $u,v$ exchanged.

For $\mathsf H=\mathsf T_a^{-1}\mathsf C$, factoring $\mathsf T_a$ from the derivative columns gives the exact identity

$$
j(u,v,a)=-\det(\mathsf T_a)\mathfrak b(E(u,v),\mathsf H E(u,v)).
\tag{3.8}
$$

Indeed the factored columns are $E,E_u,E_v,\mathsf HE$ and, in entry order $(p,q,r,s)$,

$$
\det[E,E_u,E_v,X]=-\mathfrak b(E,X).
$$

This follows by subtracting $uE_u+vE_v$ from the first column and expanding; the resulting expression is $-X_{11}+vX_{12}+uX_{21}-uvX_{22}$. Consequently the two interior sources give opposite transfer-form signs. Lemma 2.2 produces a finite collision with whole constant drifts and positive rank-one sources at slopes $a,a+\epsilon$. Both slopes can be made arbitrarily close to zero: choose $a$ first as above, then $\epsilon$ below any further positive bound. Its positive-gain estimate applies. Equation (2.4) verifies every original reading, and (1.2) realizes the fixed-row histories.

This proves the stronger assertion. A uniformly recovering history must satisfy the survivor-span hypothesis by Lemma 2.1, and hence all four equalities. ∎

**Corollary 3.2 (mirror stratum).** The corresponding theorem holds when every $(A_i)_{11}=1$.

**Proof.** Apply Theorem 3.1 to $A'_i=JA_iJ$ with multipliers $JW_iJ$. A conjugated $J$ is $J$, and a conjugated $M$ is the finite word $JMJ$; an empty word stays empty. Thus this is a legal history with the same recorded indices. Its sequences are $\mathbf x'=\mathbf y$, $\mathbf y'=\mathbf x$, $\mathbf d'=((A_i)_{22}-1)_i$, and its four equalities are (3.2) with these substitutions. Independence of survivors is preserved by conjugation. Transfer any constructed collision back by $S_b=JS'_bJ$, $c_b=Jc'_b$, $\ell_b=\ell'_bJ$, with the same slopes and entire drifts. All factors are positive and fixed in their runs, and $\operatorname{tr}((JA_iJ)S'_b)=\operatorname{tr}(A_iJS'_bJ)$. This is an algebraic correspondence between runs, with no inserted conjugation acquisition. ∎

## 4. An infinite family passing the two credited tests

**Theorem 4.1.** For every integer $N\ge3$, define the five-read history $H_N$ by

$$
\begin{aligned}
A_0&=I,& A_1&=L^N=\begin{pmatrix}1&0\\N&1\end{pmatrix},\\
A_2&=UL^{2N-1}=\begin{pmatrix}2N&1\\2N-1&1\end{pmatrix},\\
A_3&=U^{N-1}JA_2=\begin{pmatrix}2N^2-1&N\\2N&1\end{pmatrix},\\
A_4&=U^NA_3=\begin{pmatrix}4N^2-1&2N\\2N&1\end{pmatrix}.
\end{aligned}
\tag{4.1}
$$

Every deletion, including deletion of the initial endpoint, leaves four independent matrices, and $\Delta_x=\Delta_y=0$. For every $N\ge4$, $\Delta_{px}\ne0$, and the history has actual finite constant-drift collisions with positive sampled gains and both slopes arbitrarily close to zero. Thus the added tests strictly strengthen the earlier two, even after all survivor-span conditions are imposed.

**Proof.** The successive left multipliers are

$$
L^N,\qquad UL^{N-1},\qquad U^{N-1}J,\qquad U^N.
\tag{4.2}
$$

Chronologically these are $N$ copies of $(J,M)$; then $N-1$ copies of $(J,M)$ followed by $(M,J)$; then $J$ followed by $N-1$ copies of $(M,J)$; then $N$ copies of $(M,J)$. They have lengths $2N,2N,2N-1,2N$, totaling $8N-1$ literal atoms, with no interior reads. Multiplication gives exactly (4.1), at consecutive indices $0,1,2,3,4$. Equation (1.2) and the positivity of each atom give the actual single-source realization, including every unread state.

After subtracting $I$, the nonconstant trace coefficient rows on $(p,q,r)$ for $A_1,A_2,A_3$ are

$$
(0,N,0),\qquad(2N-1,2N-1,1),\qquad(2N^2-2,2N,N).
$$

Their determinant is $N(N-2)\ne0$, so $I,A_1,A_2,A_3$ are independent. The unique dependence among all five, up to scalar, is

$$
(2-N)A_0+(2N-2)A_1-2NA_2+(2N-2)A_3+(2-N)A_4=0.
\tag{4.3}
$$

To verify it entry by entry, the coefficients sum to zero, and their pairings with the three nonconstant sequences are

$$
\begin{aligned}
\mathbf x:&\quad (2N-2)N-2N(2N-1)+(2N-2)2N+(2-N)2N=0,\\
\mathbf y:&\quad -2N+(2N-2)N+(2-N)2N=0,\\
\mathbf d:&\quad -2N(2N-1)+(2N-2)(2N^2-2)+(2-N)(4N^2-2)=0.
\end{aligned}
$$

The last sum expands to $(-4N^2+2N)+(4N^3-4N^2-4N+4)+(-4N^3+8N^2+2N-4)=0$. These sequences and the constant lower-right entry determine all matrix entries. All coefficients in (4.3) are nonzero for $N\ge3$. A dependence on four survivors would extend to one on five with a zero coefficient, contradicting uniqueness. This proves every deletion assertion. The upper-right entries $0,0,1,N,2N$, together with $I\ne L^N$, also show that all endpoints are distinct.

The off-diagonal sequences are

$$
\mathbf x=(0,N,2N-1,2N,2N)^{\mathsf T},\quad
\mathbf y=(0,0,1,N,2N)^{\mathsf T},\qquad
\mathbf t=(\mathbf x+\mathbf y)/N.
\tag{4.4}
$$

This is an equality on the actual recorded clock. It forces both earlier determinants to vanish; the vectors $\mathbf1,\mathbf t,\mathbf x,\mathbf y$ are dependent here.

Use the tails $\mathbf a,\mathbf b,\mathbf c,\mathbf e,\mathbf A$ from Section 3. The first three are independent by the span calculation, and a left null covector of their four-by-three matrix is

$$
w=(2N-2,-2N,2N-2,2-N).
$$

Equation (4.3) verifies its three zero pairings. Direct symbolic expansion gives

$$
\begin{aligned}
w\mathbf A
&=(2N-2)N-2N(4N-2)+(2N-2)6N+(2-N)8N\\
&=-2N(N-3).
\end{aligned}
\tag{4.5}
$$

For $N\ge4$, $\mathbf A$ is therefore outside $\operatorname{span}(\mathbf a,\mathbf b,\mathbf c)$. Meanwhile $\mathbf e=(\mathbf a+\mathbf b)/N$, so $\mathbf e,\mathbf a,\mathbf c$ are independent. It follows that $\Delta_{px}=\det[\mathbf e,\mathbf a,\mathbf c,\mathbf A]\ne0$. All hypotheses of Theorem 3.1 have been verified. Its finite construction produces positive rank-one sources $S_1$ and $S_0=S_1+\epsilon\mathsf T_a^{-1}\mathsf CS_1$, slopes $a,a+\epsilon$ arbitrarily close to zero, and whole constants $0,\operatorname{tr}(S_0-S_1)$. Equations (2.4)–(2.5) give equality at all five original readings. This proves the collision and strictness assertions. ∎

## 5. A finite collision with all four tests zero

**Theorem 5.1.** The member $H_3$ satisfies every survivor-span condition and all four equalities (3.2), yet has a finite collision with strictly positive sampled gains. In particular the four necessary equalities, even combined with all those span conditions, are insufficient for recovery.

**Proof.** The endpoints are

$$
I,\quad\begin{pmatrix}1&0\\3&1\end{pmatrix},\quad
\begin{pmatrix}6&1\\5&1\end{pmatrix},\quad
\begin{pmatrix}17&3\\6&1\end{pmatrix},\quad
\begin{pmatrix}35&6\\6&1\end{pmatrix}.
\tag{5.1}
$$

Legality, the recorded clock, and independence after every deletion follow from Theorem 4.1 at $N=3$. The earlier equalities follow from (4.4). The covector $w=(4,-6,4,-1)$ annihilates the independent $\mathbf a,\mathbf b,\mathbf c$. At $N=3$, (4.5) gives $w\mathbf A=0$. Also

$$
w\mathbf B'=-4N+(2N-2)3N+(2-N)8N=-2N(N-3)=0.
$$

Thus both $\mathbf A$ and $\mathbf B'$ lie in $\operatorname{span}(\mathbf a,\mathbf b,\mathbf c)$, as does $\mathbf e=(\mathbf a+\mathbf b)/3$. The two added determinants vanish as well.

In entry order $(p,q,r,s)$, the quotient matrices are

$$
\mathsf B=\begin{pmatrix}0&3&0&0\\5&5&1&0\\16&6&3&0\\34&6&6&0\end{pmatrix},\qquad
\mathsf C=\begin{pmatrix}1&3&0&1\\12&10&2&2\\51&18&9&3\\140&24&24&4\end{pmatrix},
$$

$$
\mathsf T_1=\begin{pmatrix}1&6&0&1\\17&15&3&2\\67&24&12&3\\174&30&30&4\end{pmatrix}.
$$

Define the auxiliary linear map

$$
\mathsf H\begin{pmatrix}p&q\\r&s\end{pmatrix}
=\begin{pmatrix}
p&(-4p+7q-r)/6\\
(-6p+q+5r)/6&4p-4q+r+s
\end{pmatrix}.
\tag{5.2}
$$

Then $\mathsf T_1\mathsf H=\mathsf C$: its four rows applied to $(p,q,r,s)$ give, respectively,

$$
p+3q+s,\quad12p+10q+2r+2s,\quad
51p+18q+9r+3s,\quad140p+24q+24r+4s.
\tag{5.3}
$$

This identity is on auxiliary matrices and does not assert an independently acquired source.

Fix any $0<\epsilon<1$. For $1\le x\le2$ set

$$
S_1(x)=\begin{pmatrix}1&x\\1&x\end{pmatrix},\qquad
\mathsf HS_1(x)=\begin{pmatrix}1&(7x-5)/6\\(x-1)/6&5-3x\end{pmatrix},\qquad
S_0(x)=S_1(x)+\epsilon\mathsf HS_1(x).
\tag{5.4}
$$

The first source is strictly positive and rank one. Every entry of $S_0$ is strictly positive: its upper-left entry is $1+\epsilon$, the upper-right correction is positive, the lower-left entry is at least one, and the lower-right entry is at least $x-\epsilon\ge1-\epsilon>0$.

The exact determinant expansion is

$$
\det S_0(x)=\epsilon b(x)+\epsilon^2d(x),\qquad
b(x)=\frac{35-18x-x^2}{6},\quad
d(x)=\frac{175-96x-7x^2}{36}.
\tag{5.5}
$$

For verification, $b=x+(5-3x)-(7x-5)/6-x(x-1)/6$, and $d=5-3x-(7x-5)(x-1)/36$. At $x=1$ these values are $8/3,2$; at $x=2$ they are $-5/6,-5/4$. Thus $\det S_0(1)>0$ and $\det S_0(2)<0$. Continuity supplies $x_\epsilon\in(1,2)$ with $\det S_0(x_\epsilon)=0$. Both selected sources are strictly positive rank one, and they differ in their upper-left entry.

At this selected $x$, take

$$
k_0=1,\quad k_1=1+\epsilon,\qquad
D_0(\tau)=0,\quad D_1(\tau)=\epsilon(6-3x_\epsilon).
\tag{5.6}
$$

These are one entire constant drift per run. Equations (5.2)–(5.4) give

$$
\mathsf T_1S_0=\mathsf T_1S_1+\epsilon\mathsf CS_1
=\mathsf T_{1+\epsilon}S_1.
\tag{5.7}
$$

The two undrifted five-vectors consequently differ by their initial difference

$$
\operatorname{tr}(S_0-S_1)=\epsilon(6-3x_\epsilon)=D_1-D_0.
$$

This checks equality of all five original observations, including the initial one. Every sampled gain is positive since both slopes are positive. Equation (1.2), separately for each selected source, gives the actual positive factors and fixed rows; words (4.2) preserve positive unread states. Sources and slopes differ, so the collision lies beyond the representation fibres. This constructs a finite collision for every fixed $\epsilon\in(0,1)$, without a claim that these exceptional slopes approach zero. ∎

Together, Theorems 4.1 and 5.1 exclude every integer member $H_N$, $N\ge3$. For $N\ge4$ the collision slopes can approach zero; the separately proved $N=3$ construction has slopes $1,1+\epsilon$. Corollary 3.2 transfers the corresponding statements to the conjugate histories.

## 6. Exhaustive regular constant-diagonal classification

The preceding four equalities are not merely tests for the displayed family. Together with the survivor condition, they force the endpoint sequence that already has the finite collision of Theorem 5.1.

**Theorem 6.1 (classification).** Let a legal five-read history have $A_0=I$, actual recorded indices $0,1,2,3,4$, and

$$
(A_i)_{22}=1\qquad(0\le i\le4).
$$

Assume that deleting any noninitial endpoint leaves four independent real matrices. Define $\mathbf 1,\mathbf t,\mathbf x,\mathbf y,\mathbf d,\mathbf t\mathbf x,\mathbf t\mathbf y$ as in (3.2), and assume all four equalities (3.2). Then

$$
A_0=I,\quad
A_1=\begin{pmatrix}1&0\\3&1\end{pmatrix},\quad
A_2=\begin{pmatrix}6&1\\5&1\end{pmatrix},\quad
A_3=\begin{pmatrix}17&3\\6&1\end{pmatrix},\quad
A_4=\begin{pmatrix}35&6\\6&1\end{pmatrix}.
\tag{6.1}
$$

Conversely, this endpoint sequence is legal, every noninitial deletion leaves four independent matrices, and all four equalities hold. The conclusion classifies endpoints only; any finite legal words producing these endpoints are allowed.

**Proof.** Write

$$
A_i=\begin{pmatrix}a_i&y_i\\x_i&1\end{pmatrix},\qquad d_i=a_i-1.
$$

Every cumulative matrix and every transition word is nonnegative integral with determinant $\pm1$. The survivor hypothesis first implies that the endpoints are pairwise distinct: if two endpoints agreed, a deletion of a noninitial endpoint different from those two would leave a repeated member among four survivors. Subtracting $I$ from the other endpoints shows that the three-vectors $(d_i,x_i,y_i)$ are independent for every three of the four noninitial indices. In particular, the tail columns

$$
a=(x_1,x_2,x_3,x_4)^{\mathsf T},\quad
b=(y_1,y_2,y_3,y_4)^{\mathsf T},\quad
h=(d_1,d_2,d_3,d_4)^{\mathsf T}
$$

are independent.

We need the following transition rigidity. If

$$
A=\begin{pmatrix}a&y\\x&1\end{pmatrix},\qquad
W=\begin{pmatrix}h_0&b_0\\c_0&e_0\end{pmatrix},\qquad A'=WA,
$$

then the lower-right entry condition is $c_0y+e_0=1$. If $y\ge2$, nonnegative integrality gives $c_0=0,e_0=1$; unimodularity then gives $h_0=1$, so $W=U^{b_0}$. If $y=1$, either the same upper shear occurs, or $c_0=1,e_0=0$, in which case unimodularity gives $b_0=1$ and $W=U^{h_0}J$. If $y=0$, unimodularity of $A$ gives $A=L^x$. Also, for every fixed $B$,

$$
U^jB=B+jKB,\qquad K=\begin{pmatrix}0&1\\0&0\end{pmatrix},
$$

so all upper-shear extensions of one endpoint lie in a two-dimensional linear space.

The first two noninitial upper-right entries must be $y_1=0$ and $y_2=1$. If $y_2\ge2$, then $A_2,A_3,A_4$ lie in one two-dimensional upper-shear space, and deleting $A_1$ leaves span at most three. Monotonicity of upper-right entries rules out $y_1\ge2$. If $y_1=y_2=0$, then $I,A_1,A_2$ are lower shears and deleting either later endpoint leaves span at most three. If $y_1=y_2=1$, distinctness forces $A_2=JA_1$; the next distinct endpoint has upper-right at least two and the following upper-shear plane contradicts a survivor condition after deleting the other member of $\{A_1,A_2\}$. The case $y_1=1,y_2=0$ is impossible by monotonicity. Hence $A_1=L^n$ for an integer $n\ge1$ and $y_2=1$.

The transition from $A_1=L^n$ to $A_2$ has multiplier $W=(\begin{smallmatrix}h_0&1\\c_0&1\end{smallmatrix})$, with $h_0,c_0$ nonnegative integers. Its determinant condition is $h_0-c_0=\pm1$, so the two first-column entries differ by one. If $h_0=c_0+1$, put $C=n+c_0+1$; if $c_0=h_0+1$, put $C=n+c_0$. In both cases $C\ge n+1$, and multiplication by $L^n$ gives the two possibilities

$$
P_C=\begin{pmatrix}C&1\\C-1&1\end{pmatrix},\qquad
N_C(1)=\begin{pmatrix}C-1&1\\C&1\end{pmatrix}.
$$

Write more generally

$$
N_C(v)=\begin{pmatrix}Cv-1&v\\C&1\end{pmatrix}\qquad(v\ge1).
$$

If the third upper-right entry is one, the third endpoint is the swapped member of the pair and the fourth endpoint is an upper-shear extension of one of them. It cannot extend $P_C$: for every $v\ge1$,

$$
U^{v-1}P_C=\begin{pmatrix}(C-1)v+1&v\\C-1&1\end{pmatrix},
$$

whose tail satisfies $d=(C-1)y$, as does $A_1=L^n$; deleting the swapped member then leaves span at most three. Thus it extends $N_C(1)$. If the third upper-right entry is at least two, $A_3$ is an upper-shear extension of either $A_2$ or $JA_2$, and $A_4$ is an upper-shear extension of $A_3$. It cannot extend $A_2$: then $A_2,A_3,A_4$ lie in one two-dimensional upper-shear space, so deleting $A_1$ leaves span at most three. It also cannot extend $P_C$: then deleting $A_2$ leaves $I,L^n,A_3,A_4$ with the tail relation $d=(C-1)y$, again giving span at most three. Therefore $A_3$ extends $N_C(1)=JA_2$, forcing $A_2=P_C$. Therefore every survivor-regular history has one of the two forms

$$
\begin{array}{ll}
\mathrm{Type\ A}:& I,L^n,P_C,N_C(t),N_C(u),\qquad u>t\ge1,\\[2mm]
\mathrm{Type\ B}:& I,L^n,N_C(1),P_C,N_C(u),\qquad u\ge2.
\end{array}
\tag{6.2}
$$

No parameter choice is assumed to satisfy the survivor condition; (6.2) is only a necessary normal-form list.

Now put

$$
e=(1,2,3,4)^{\mathsf T},\quad X=(ix_i)_{i=1}^4,\quad Y=(iy_i)_{i=1}^4,
\quad V=\operatorname{span}(a,b,h).
$$

Expanding the four determinants in row zero gives

$$
\det[e,a,b,X]=\det[e,a,b,Y]=\det[e,a,h,X]=\det[e,h,b,Y]=0.
\tag{6.3}
$$

Suppose first that $e\notin V$. Then $e,a,b,h$ is a basis. The two equations containing $Y$ put $Y$ in

$$
\operatorname{span}(e,a,b)\cap\operatorname{span}(e,h,b)=\operatorname{span}(e,b).
$$

The first tail coordinate of both $b$ and $Y$ is zero, while that of $e$ is one, so $Y$ is proportional to $b$. In both normal forms $y_2=1$ and $y_3>0$; proportionality would require the scalar to be two at coordinate two and three at coordinate three, a contradiction. Hence $e\in V$.

Write $e=\lambda a+\mu b+\nu h$. The first coordinate gives $\lambda=1/n$, so $e,b,h$ are independent. Equation (6.3) then gives $Y\in V$. The vector $e$ is not proportional to $a$: in Type A its third and fourth coordinates are both $C$ while those of $e$ are $3$ and $4$, and in Type B its second and fourth coordinates are both $C$ while those of $e$ are $2$ and $4$. Thus at least one of $\mu,\nu$ is nonzero. If $\nu\ne0$, then $e,a,b$ is a basis and the first equation in (6.3) gives $X\in V$; if $\mu\ne0$, then $e,a,h$ is a basis and the third equation gives $X\in V$. Therefore

$$
e,X,Y\in V.
\tag{6.4}
$$

Type B is impossible. In that form,

$$
a=(n,C,C-1,C),\quad b=(0,1,1,u),\quad h=(0,C-2,C-1,Cu-2).
$$

Let $w=(w_1,w_2,w_3,w_4)$ annihilate $V$. Its fourth coordinate is nonzero, since otherwise the first three independent tail rows would have a nontrivial left relation; normalize $w_4=1$. From $wb=wY=0$, with $Y=(0,2,3,4u)$, we obtain

$$
w_2+w_3+u=0,\qquad 2w_2+3w_3+4u=0,
$$

so $w_2=u,w_3=-2u$. But then

$$
wh=u(C-2)-2u(C-1)+(Cu-2)=-2,
$$

contradicting (6.4).

In Type A,

$$
a=(n,C-1,C,C),\quad b=(0,1,t,u),\quad h=(0,C-1,Ct-2,Cu-2),
$$

with $Y=(0,2,3t,4u)$. Again normalize $w_4=1$. The equations $wb=wY=0$ give

$$
w_2=u,\qquad w_3=-\frac{2u}{t},\qquad w_1=\frac{6u}{t}-2u-4
$$

after also imposing $we=0$. Substitution into $wh=0$ gives

$$
u(4-t)=2t.
$$

Since $u>t\ge1$ are integers, $t<4$; $t=1$ gives $u=2/3$, $t=2$ gives $u=2$ contrary to $u>t$, and therefore $t=3,u=6$. Thus $w=(-4,6,-4,1)$. The remaining relations $wa=0$ and $wX=0$ give, respectively,

$$
-4n+3C-6=0,
$$

and

$$
-4n+4C-12=0.
$$

Subtracting gives $C=6$, and then $n=3$. Hence (6.1) follows from (6.2).

Conversely, the displayed endpoints are reached by successive multipliers

$$
L^3,\qquad UL^2,\qquad U^2J,\qquad U^3,
$$

which are finite $M/J$ words. Their first three noninitial tail rows are $(0,3,0),(5,5,1),(16,6,3)$ and have nonzero determinant. The unique dependence is

$$
A_0-4A_1+6A_2-4A_3+A_4=0.
$$

All noninitial coefficients are nonzero, so every noninitial deletion leaves four independent matrices. Finally, for $a=(3,5,6,6)$, $b=(0,1,3,6)$ and $h=(0,5,16,34)$, the covector $w=(-4,6,-4,1)$ annihilates $a,b,h,e,X,Y$. Thus all four determinants vanish. This proves the converse and the classification. ∎

**Corollary 6.2 (uniform exclusion of the classified class and its mirror).** Every history in Theorem 6.1 has the finite collision of Theorem 5.1, with two strictly positive rank-one sources, two different positive sampled-gain slopes, and one entire constant drift per run. The same sources work for any legal intervening words producing the classified endpoints, because the observations depend on the cumulative endpoints and every $M/J$ atom preserves the positive source column.

If instead every $(A_i)_{11}=1$, use $A'_i=JA_iJ$ and $W'_i=JW_iJ$. Wrapping a finite word by $J$ gives another finite $M/J$ word (and an empty word remains empty after cancellation), with the same recorded indices and lower-right entries one. The four mirrored determinant tests become the four tests of Theorem 6.1 after exchanging the diagonal and off-diagonal sequences. Therefore the mirrored endpoints are

$$
I,\quad J\begin{pmatrix}1&0\\3&1\end{pmatrix}J,
\quad J\begin{pmatrix}6&1\\5&1\end{pmatrix}J,
\quad J\begin{pmatrix}17&3\\6&1\end{pmatrix}J,
\quad J\begin{pmatrix}35&6\\6&1\end{pmatrix}J,
$$

and the conjugated $H_3$ collision transfers by $S\mapsto JSJ$, $c\mapsto Jc$, and $\ell\mapsto\ell J$, with slopes and complete drifts unchanged. This is an algebraic correspondence between original runs; no conjugation acquisition or extra clock is inserted.

The endpoint classification concerns the survivor-regular all-four-zero branch. For recovery, the following three branches exhaust every legal five-read history in (3.1). If a noninitial survivor set is dependent, Lemma 2.1 gives a collision at a common sampled-zero-gain slope. If all such survivor sets are independent and at least one determinant in (3.2) is nonzero, Theorem 3.1 gives a finite collision with both slopes arbitrarily close to zero and all sampled gains positive. If all survivor sets are independent and all four determinants vanish, Theorem 6.1 forces $H_3$, and Theorem 5.1 gives its finite collision at slopes $1,1+\epsilon$, for every $0<\epsilon<1$. The exact mirror transfers each branch. Thus every legal five-read history whose lower-right sequence is identically one or whose upper-left sequence is identically one fails uniform recovery. This does not assert a positive-gain collision in the failed-survivor branch.

A remaining candidate for five-read recovery must satisfy every noninitial survivor condition and have neither diagonal sequence identically one. The results here do not settle the general recovery status of that remaining class, provide a five-read protocol, or exclude arbitrary varying-diagonal histories. The unrestricted residual remains $5\le C_{\mathrm{fix}}(0)\le6$.

## 7. Credited bounds on the unchanged all-degree programme

Let $C_{\mathrm{fix}}(d)$ be the least uniform exact-read count over all predetermined finite-word histories for (1.1). The credited results on this identical model are

$$
C_{\mathrm{fix}}(d)=d+5\quad(d\ge1),\qquad
5\le C_{\mathrm{fix}}(0)\le6.
\tag{7.1}
$$

Here is a self-contained verification of the bounds used to delimit this companion.

For the lower bound use the injective actual-target chart

$$
(p,q,r,k,\delta_0,\ldots,\delta_d)\in(0,\infty)^3\times\mathbb R^{d+2},\qquad
S=\begin{pmatrix}p&q\\r&qr/p\end{pmatrix},\quad
D(\tau)=\sum_{h=0}^d\delta_h\tau^h.
$$

It has dimension $n=d+5$, and (1.2) realizes every point. On any fixed $m$-read history the observation map is smooth. If $m<n$, take its greatest attained derivative rank $\rho\le m<n$. If $\rho=0$, integrating its derivative on a small convex chart ball makes the map constant there. Otherwise a nonzero maximal $\rho$-minor persists on a neighborhood with constant rank $\rho$. The implicit function theorem makes the level set of the corresponding first $\rho$ outputs a graph over a small connected ball of dimension $n-\rho>0$. Every other output differential is a linear combination of these first differentials and vanishes on the graph's tangent vectors. Integrating along paths in the graph makes all outputs constant. Distinct chart points therefore have identical complete data. Fixed earlier stopping can be padded along its predetermined history to its asserted bound; equality of the padded data includes every stopping prefix. This proves $C_{\mathrm{fix}}(d)\ge d+5$, with no adaptive-word conclusion.

For the upper bounds reuse the terminal-repetition construction from *Terminal repetition and recorded-clock obstructions with affine gain*. Put

$$
Q=\begin{pmatrix}6&1\\5&1\end{pmatrix},\quad
T=\begin{pmatrix}11&2\\6&1\end{pmatrix},\quad
B=\begin{pmatrix}17&3\\6&1\end{pmatrix}.
$$

For $d\ge1$ its $d+5$ recorded endpoints are $I,L^2,Q,T$, followed by $B$ at every index $4,\ldots,d+4$. The successive nonempty multipliers are $L^2,UL^3,UJ,U$, of literal lengths $4,8,3,2$; subsequent transitions are empty. Indeed $Q=UL^5$, $T=UJQ$, $B=UT$. These are legal common-source histories, and (1.2) applies.

Use the source coordinates

$$
\chi=16p+6q+3r,\quad t=6p+r,\quad v=q-p,
$$

$$
p=(\chi-3t-6v)/4,\quad q=(\chi-3t-2v)/4,\quad
r=(11t+18v-3\chi)/2,\quad s=qr/p.
\tag{7.2}
$$

At fixed $\chi$ the positive $(t,v)$ domain is convex, since its first three entry conditions are open affine half-planes. Let $a=p+s$. The single polynomial

$$
P(\tau)=D(\tau)+(a+\chi)(1+k\tau)
$$

has degree at most $d$, and is determined by its actual terminal values $z_j=P(j)$ at $j=4,\ldots,d+4$. Interpolation is valid because these are $d+1$ distinct nodes; uniqueness follows from the polynomial root bound. Trace expansion gives the four early residuals

$$
\chi=P(0)-z_0,\quad W=2(P(1)-z_1)-\chi,\quad
Y=P(2)-z_2,\quad Z=P(3)-z_3,
$$

$$
(W,Y,Z)=F_\chi(t,v,k)
=\bigl((1+k)(3t+2v)+k\chi,\ (1+2k)(2t+v),\ (1+3k)t\bigr).
\tag{7.3}
$$

For example the trace differences from $B$ at these early endpoints are $\chi,\chi-2q,2t+v,t$, and $2(\chi-2q)=\chi+3t+2v$. Direct expansion of the derivative determinant gives

$$
\begin{aligned}
-\det DF_\chi
&=p(96k^2+38k+6)+q(36k^2+24k+4)+r(18k^2+7k+1)\\
&=p\{96(k+19/96)^2+215/96\}
+4q(3k+1)^2+r\{18(k+7/36)^2+23/72\}>0.
\end{aligned}
\tag{7.4}
$$

This determinant proves global injectivity through an exact finite identity, not just local nonsingularity. With $y=(t,v)$, for any two points at fixed $\chi$ the bilinear form of (7.3) gives

$$
F_\chi(y_0,k_0)-F_\chi(y_1,k_1)
=DF_\chi(\bar y,\bar k)(y_0-y_1,k_0-k_1)^{\mathsf T},
\tag{7.5}
$$

where bars are arithmetic means; this uses $k_0y_0-k_1y_1=\bar k(y_0-y_1)+\bar y(k_0-k_1)$. Convexity makes the midpoint's $p,q,r$ positive, with $s$ reconstructed as $qr/p$. Equation (7.4) makes its derivative invertible for every real midpoint slope. Equal full data already determine equal $P,\chi,W,Y,Z$ and hence force equal $t,v,k$, equal $S$, and the same entire $D=P-(p+s+\chi)(1+k\tau)$.

For arbitrary proposed data first require $\chi>0$. A finite inverse on the image follows by taking the distinct real roots of

$$
-(W-\chi k)(1+2k)(1+3k)+2Y(1+k)(1+3k)-Z(1+k)(1+2k)=0.
$$

Its leading coefficient is $6\chi>0$, so it has at most three distinct real roots. At each root solve the rows $(1+k)(3,2)$, $(1+2k)(2,1)$, $(1+3k)(1,0)$ against $(W-\chi k,Y,Z)$. At most one gain vanishes; every surviving pair has nonzero determinant. The displayed cubic is exactly the augmented three-by-three determinant, so it includes consistency of any erased row. Reconstruct (7.2), require positive entries, form the one whole polynomial $D$, and require its degree bound and all original equations at every index. Actual data supply a passing candidate; the positive factorization makes every passing candidate sufficient; (7.5) gives uniqueness. This covers lower degrees, cancellation, every gain zero and negative gain without division by a vanishing gain. Thus the credited upper bound is on the exact target, rather than on lifted parameters.

At $d=1$ this construction has six endpoints $I,L^2,Q,T,B,B$. Restricting its recovered entire affine drift to the constant-drift submodel gives $C_{\mathrm{fix}}(0)\le6$. The absorbed gain term is affine, so its degree-$d$ interpolation argument cannot itself be used at $d=0$ with only one terminal read. Nothing here gives a uniformly recovering five-read history.

## 8. Credits and remaining boundaries

The original programme and *Shared affine gain and zero-crossing recovery* supply the positive rank-one model, effective target, counted initial read, finite cumulative-word convention, positive representation fibres, and the all-fixed-history lower bound. Their particular calibration-prefix obstruction keeps its prefix-specific scope. The earlier $\max(d+6,7)$-read nine-atom construction is credited and is not a new conclusion here.

*Sharp positive-degree recovery and six-read stability with affine gain* is credited, through the supplied terminal-repetition volume, for the established sharp positive-degree counts, fifteen-atom $d=1$ construction, parity and $6d+9$ constructions, and the source-coordinate, determinant, midpoint and cubic-inverse methods. Those external-to-this-volume constructions are not additional premises of the proofs above. The supplied *Terminal repetition and recorded-clock obstructions with affine gain* directly supplies and proves the seventeen-atom terminal construction audited in Section 7, its exact all-degree correspondence, the noninitial erasure-span and finite sign-transfer bridges, and the two off-diagonal conditions $\Delta_x=\Delta_y=0$. Its excluded family $I,L,Q_w,T_{3,w},T_{4,w}$ remains a credited earlier family.

The supplied fallible proposal *Two additional diagonal-stratum determinants, and finite collisions for an infinite family passing both prior tests* supplies the added conditions, family $H_N$, exceptional $H_3$ collision, and the candidate endpoint classification. The added information is the next source-coordinate coefficient in each boundary identity (3.5)–(3.7). The classification proof in Theorem 6.1 is independently audited here from arbitrary legal transition words; it does not take the proposal's conclusion as authority. No independence of $\mathbf1,\mathbf t,\mathbf x,\mathbf y$ is added; their dependence is precisely what allows the strictness witnesses (4.4) to pass the two earlier tests. These are mathematical supplier credits, without a claim of independent approval or external priority.

The new necessary conditions apply in (3.1) and its exact mirror. Theorem 6.1 exhausts the lower-right-one class after the survivor condition and all four equalities, and Corollary 6.2 transfers the finite $H_3$ collision to that classified class and its mirror. Histories failing any noninitial survivor condition already have Lemma 2.1's sampled-zero-gain collision, in any endpoint stratum. Within either constant-diagonal-one stratum, survivor-regular histories outside the four zero equalities have Theorem 3.1's finite positive-gain collision. These three branches exclude every legal five-read history in either stated stratum; being outside the endpoint classification does not leave its recovery status unresolved there. The remaining general question concerns survivor-regular histories with neither diagonal sequence identically one. No classification or uniform exclusion of that remaining class is established here, and the mirror correspondence has exactly the stated conjugate scope.

The unrestricted residual is still $5\le C_{\mathrm{fix}}(0)\le6$. Resolving it requires either a legal predetermined five-read history with global recovery of the whole $(S,k,D)$ for every real slope, or an actual-source finite collision for every legal five-read history. The four necessary equalities are insufficient, and no derivative zero, rank count alone, boundary source, or auxiliary lifted solution is promoted to a collision. The positive-degree equality in (7.1) is credited existing progress; the all-degree programme remains incomplete because the constant-drift residual remains.

All proofs are ordinary conditional exact-real textual mathematics. The $8N-1$ and seventeen literal counts are construction counts, distinct from recorded reads; no unrestricted atom optimum is asserted. There is no adaptive lower bound, numerical-stability or noisy-decoding result, precision/bit/time or physical-resource certification, general-neural-network conclusion, empirical or Lean/kernel certification, or worldwide-originality assertion. Strict positivity, one rank-one common source, one fixed row per run, arbitrary real gain slope, one whole declared-degree drift, actual consecutive reading indices, and all original observations are retained.

## 追加锚（本行以下为增补区）
