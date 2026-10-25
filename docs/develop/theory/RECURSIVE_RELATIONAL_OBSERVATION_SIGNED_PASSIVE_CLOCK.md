# Recursive Relational Observation: A Signed Passive Clock

## 1. The actual signed source and four observation tasks

**Definition 1.1 (the native source and its serial menu).** Fix one unknown finite rooted path with cells at distances $0,\ldots,N-1$, $N\ge1$, and one fixed rational symmetric matrix

$$
T=\begin{pmatrix}
a_0&c_0&&0\\
c_0&a_1&\ddots&\\
&\ddots&\ddots&c_{N-2}\\
0&&c_{N-2}&a_{N-1}
\end{pmatrix},\qquad
c_i>0,\qquad -I\preceq T\preceq I.
\tag{SPC.1}
$$

The diagonal entries are arbitrary rationals subject to the displayed contraction condition. The field is authentically initialized to $b=e_0$, with its other $N-1$ entries zero. At every completed cut the installed serial menu is

| Command | Actual next field | Complete declared output |
| --- | --- | --- |
| Read | $x$ | the literal rational $b^{\mathsf T}x$ |
| Tick | $Tx$ | the literal rational $b^{\mathsf T}Tx$ after the update |
| Hold | $x$, preventing autonomous evolution during local work | its fixed acknowledgement |
| Add$(u)$, if separately installed, $u\in\mathbb Q$ | $x+ub$ | its fixed declared acknowledgement |

Acknowledgements contain no hidden metadata. An intentional Tick is an actual update, including when its output is used to identify phase. Hold does not manufacture an observation of an unexecuted Tick. There is no coefficient, size, chosen-index moment, reset, source-copy, full-field-read or phase port in this menu. A mathematical Space expression below does not add such a port.

This is the serial menu of [Recovery Geometry II, §36][P], with its strict positive-spectrum source promise replaced by (SPC.1). Our $c_i$ are that source's adjacent-link coefficients $b_i$; $b$ here denotes the actual unit input field. All other stated operation semantics are retained.

**Assumption 1.2 (installation and source continuity).** The source class, fixedness of $T$, binding to its actual root, authentic unit preparation, nondestructive Read, exact signed rational serialization, successful serial calls and Hold control are installed premises. The observer has the actual source reference, Read/Tick/Hold rights, and storage and control backing for its calls. Add has a separate installed right and takes the actually supplied rational input. There is no autonomous evolution between serial commands; Hold explicitly protects the local processing intervals used below. No source-dependent timing, allocation, identity or coefficient-length side channel is exposed. Neither $N$ nor a spectral gap is supplied as advice. The source is never substituted between acquisition and continued use.

These premises describe a conditional exact digital service. Physical conformance of an instrument to them is **ASSUMED-UNVERIFIED**. No numerical recovery in this volume proves that conformance or creates a missing reference, right, preparation or backing resource.

**Definition 1.3 (passive cuts and acquired outputs).** A passive run uses no Add. Put

$$
x_k=T^k b,\qquad m_j=b^{\mathsf T}T^j b,\qquad m_0=1.
\tag{SPC.2}
$$

Its designated ordered root list through cut $k$ consists of one actual initial Read and the returning output of each of its $k$ actual Ticks:

$$
\mathcal T_k=(m_0,m_1,\ldots,m_k).
\tag{SPC.3}
$$

Read or Hold insertions are not new indices in this list. It records neither wall time nor the full command journal. The list may be streamed rather than retained. A later local calculation reproducing one of its rational values is a prediction from earned data, not an additional acquired source output.

The question is when the native law and current field, this actual ordered list, a finite endpoint law with a literal suffix, and a finite predictive record determine the same source and passive phase. The source class includes negative and zero eigenvalues and either endpoint $\pm1$.

## 2. The exact spectral condition for a signed passive clock

**Theorem 2.1 (rooted interior weight, a cubic residual and two-output phase separation).** Let $E$ be any finite-dimensional real inner-product space, let $T:E\to E$ be selfadjoint with $-I\preceq T\preceq I$, and let $b\in E$ be a unit vector. Eigenspaces may have arbitrary multiplicities. Write $P_\lambda$ for the orthogonal spectral projections and $m_j=\langle b,T^j b\rangle$. The following conditions are equivalent:

1. Some $\lambda$ satisfies $0<|\lambda|<1$ and $\|P_\lambda b\|^2>0$.
2. $(T^3-T)b\ne0$.
3. $k\mapsto(m_k,m_{k+1})$ is injective on $\mathbb N_0$.
4. For every $K\ge0$ that map is injective on the infinite tail $\{k:k\ge K\}$.
5. The vector orbit $T^k b$ has no eventual period at most two: there are no $K\ge0$ and $p\in\{1,2\}$ such that $T^{k+p}b=T^k b$ for all $k\ge K$.

In fact, under condition 1, for every $l>k\ge0$ one of the two coordinates strictly decreases from the pair at $k$ to the pair at $l$. If condition 1 fails, $T^{k+2}b=T^k b$ for every $k\ge1$.

**Proof.** Apply the finite real spectral theorem and combine repeated eigenvectors into their full eigenspace projections. With $w_\lambda=\|P_\lambda b\|^2$,

$$
w_\lambda\ge0,\qquad \sum_\lambda w_\lambda=1,\qquad
m_j=\sum_\lambda w_\lambda\lambda^j,
\tag{SPC.4}
$$

where the sum is over distinct eigenvalues in $[-1,1]$. As usual $\lambda^0=1$, including at zero. Orthogonality gives

$$
\|(T^3-T)b\|^2
=\sum_\lambda w_\lambda\lambda^2(1-\lambda^2)^2.
\tag{SPC.5}
$$

Each summand is nonnegative and is strictly positive exactly at a rooted eigenvalue with $0<|\lambda|<1$. This proves $1\Leftrightarrow2$ without a simple-spectrum hypothesis.

Assume 1 and take $l>k$. Set $d=l-k\ge1$ and choose $\epsilon\in\{0,1\}$ so that $e=k+\epsilon$ is even. Then

$$
m_{k+\epsilon}-m_{l+\epsilon}
=\sum_\lambda w_\lambda\lambda^e(1-\lambda^d)>0.
\tag{SPC.6}
$$

For every $\lambda\in[-1,1]$, both factors $\lambda^e$ and $1-\lambda^d$ are nonnegative. At the eigenvalue in condition 1 they are both strictly positive. Hence the two pairs cannot coincide. This proves 3 and its stronger coordinate statement, and restriction gives 4.

The same rooted eigenvalue also prevents an orbit repeat with gap $p=1$ or $2$ at any index: projecting such an equality gives

$$
\lambda^k(\lambda^p-1)P_\lambda b=0,
$$

whose scalar factor is nonzero. Thus 1 implies 5.

If 1 fails, all nonzero projections of $b$ lie at $-1,0,1$. The zero projection disappears after the first Tick, and the remaining two projections satisfy $T^{k+2}b=T^k b$ for every $k\ge1$. This contradicts 5 and makes the scalar pairs at $k,k+2$ equal at arbitrarily late indices, contradicting both 3 and 4. These contrapositives finish every equivalence. $\square$

The finite spectral theorem and the positive rooted weights in (SPC.4) are mature suppliers. The phase statement uses their actual relation to this readout: it does not identify a list of eigenvalues with a prepared/readable spectral measure. [Wave, §§4.2–4.6][Wave] makes the corresponding distinction for unitary correlations. Here the operator is a real contraction, so its rooted eigenvalues can decay rather than lie on the unit circle.

**Definition 2.2 (good and bad rooted sources).** Call a rooted selfadjoint contraction good if it satisfies Theorem 2.1, and bad otherwise. Goodness concerns the spectral weight seen by $b$, not the existence of an unseen eigenvalue elsewhere in $E$. The native path will be cyclic, so it has no such unseen subspace.

## 3. Earning the signed native law and deciding the class

**Proposition 3.1 (the signed application of native Gram reconstruction).** Every source of Definition 1.1 has cyclic root $b$. One common exact protocol, given no $N$ or gap advice, determines $N$, the full native rooted $T$, its least monic impulse recurrence $q$ and its finite reduced transfer after exactly $2N$ actual Ticks and $2N+1$ scalar returns. It ends held at the actual field $T^{2N}b$. This is an attained horizon, not an every-source lower bound in this closed signed class.

**Proof.** The native triangularity argument of P, Lemma 37.1, uses tridiagonality and positive adjacent links, not positivity of the eigenvalues. Explicitly, for $0\le j<N$, $T^j b$ is supported on cells $0,\ldots,j$, with cell $j$ equal to

$$
\gamma_j=\prod_{i<j}c_i>0,\qquad \gamma_0=1.
\tag{SPC.7}
$$

Multiplication enlarges support by at most one cell, and its new extreme coordinate is $c_j\gamma_j$. Induction proves the assertion. Thus

$$
K_{N-1}=[b,Tb,\ldots,T^{N-1}b]
\tag{SPC.8}
$$

is triangular with nonzero diagonal and is a basis of the actual cells. In particular $b$ is cyclic. For every $r\ge0$ the sign-independent Gram identity is

$$
H_r=(m_{i+j})_{0\le i,j\le r}=K_r^{\mathsf T}K_r,
\qquad K_r=[b,Tb,\ldots,T^r b].
\tag{SPC.9}
$$

Consequently $H_r>0$ for $r<N$, whereas $H_N$ is singular of rank $N$.

Use the actual acquisition schedule of P, Theorem 37.2: one initial Hold and Read, then two returning Ticks at each stage $r=1,2,\ldots$, followed by Hold during the exact rational singularity test of $H_r$. The first singular block is exactly $H_N$. The recorded scalar prefix is exactly $(m_0,\ldots,m_{2N})$, all from this specimen, and the actual source has advanced to $2N$.

For completeness, the finite flat block determines the needed law without a positive shifted block. Solve

$$
q(z)=z^N+\sum_{j<N}q_jz^j,\qquad
H_{N-1}(q_j)_{j<N}=-(m_N,\ldots,m_{2N-1})^{\mathsf T}.
\tag{SPC.10}
$$

The basis (SPC.8) makes the equations equivalent to $q(T)b$ being orthogonal to a basis, hence to $q(T)b=0$. Commutation with $T$ then makes $q(T)$ zero on that basis and therefore zero on the whole actual space. No nonzero polynomial of degree below $N$ annihilates $b$, by its triangular independence. The characteristic polynomial is monic of degree $N$ and annihilates $T$, so it equals $q$. Also

$$
m_{s+N}=-\sum_{j<N}q_jm_{s+j}\qquad(s\ge0).
\tag{SPC.11}
$$

If a polynomial $v$ supplied a smaller all-shift scalar recurrence, $v(T)b$ would be orthogonal to every $T^s b$, including the basis (SPC.8), and hence zero, a contradiction. This proves least order $N$.

The all-future uniqueness in this argument is not restricted to a competitor of known size. For any finite selfadjoint realization of the earned prefix, the squared norm of its $q(T)b$ is the same quadratic expression in moments through $2N$ and is zero, since it is zero for the actual realization. The competitor therefore satisfies the same recurrence from the same first $N$ moments. This is the sign-independent invariant-Krylov part of Main, Theorem 137.13; the extra shifted-positivity assumption there is used for a nonnegative operator realization and is not imposed here.

Finally use the supplied native Jacobi reconstruction of P, Proposition 37.3, with the polynomial Gram pairing

$$
\langle p,s\rangle_m=\sum_{i,l}p_i s_l m_{i+l}
=\langle p(T)b,s(T)b\rangle.
$$

Its parameter correspondence can be written without a spectral sign condition. Set $p_0=1$, so $h_0=1$. For $1\le j<N$, the equations for the lower coefficients of a monic degree-$j$ polynomial have coefficient matrix $H_{j-1}>0$ and rational right-hand side, so they have a unique rational solution. The resulting monic $p_j$, orthogonal to degrees below $j$, satisfies

$$
p_j(T)b=\gamma_j e_j,\qquad
h_j=\langle p_j,p_j\rangle_m=\gamma_j^2,
\qquad 0\le j<N.
\tag{SPC.12}
$$

Indeed the smaller powers span exactly the preceding native cells, and removing their projections from $T^j b$ leaves its positive extreme coordinate. Hence

$$
\begin{aligned}
a_j&=\frac{\langle zp_j,p_j\rangle_m}{h_j}&& (0\le j<N),\\
c_j&=\sqrt{h_{j+1}/h_j}>0&& (0\le j<N-1).
\end{aligned}
\tag{SPC.13}
$$

These use moments through $2N-1$. All monic coefficients and pairings are obtained by rational nonsingular solves. Each positive link root is a rational square root on the promised image: if a reduced positive rational is a rational square, both its numerator and denominator are integer squares. Exact integer roots therefore recover the actual positive rational $c_j$. This invokes neither a real-number oracle nor a new sign convention for the cells.

The finite endpoint law is

$$
F_T(z)=b^{\mathsf T}(zI-T)^{-1}b
=\frac{\det(zI-T_{\{1,\ldots,N-1\}})}{q(z)}
=\sum_{j\ge0}m_jz^{-j-1}.
\tag{SPC.14}
$$

The numerator is $1$ when $N=1$. Cofactors and the formal expansion at infinity give the equalities. Reduction cannot cancel a factor: a proper reduced fraction with smaller monic denominator would give, by multiplying its Laurent expansion, a smaller all-shift recurrence, contrary to least order. Thus its reduced monic denominator is exactly $q$.

P, Propositions 37.3–37.4, and the coefficient-driven Jacobi supplier credited in §9 provide the reconstruction algebra. The displayed correspondence shows why it remains valid here: symmetry and the strict Gram form replace no hypothesis by an unearned positivity assertion about the shifted form. $\square$

**Theorem 3.2 (the exact rational good-class test).** For the actual native path, $\deg q=N$ and

$$
\begin{aligned}
T\text{ is good}
&\quad\Longleftrightarrow\quad q\nmid z^3-z\\
&\quad\Longleftrightarrow\quad
\Delta:=m_6-2m_4+m_2>0.
\end{aligned}
\tag{SPC.15}
$$

The class is decidable by rational operations on the earned law. Any moments in (SPC.15) not present in the acquired prefix are computed locally using (SPC.11), without additional source calls. Every bad native path has $N\le3$ and satisfies $x_{k+2}=x_k$ for $k\ge1$.

**Proof.** The degree assertion is Proposition 3.1. Divide any polynomial $v$ by $q$ over $\mathbb Q$. Since $q(T)b=0$, $v(T)b=0$ if and only if its remainder annihilates $b$. A remainder of degree below $N$ can do so only when zero, by (SPC.8). Applying this to $v=z^3-z$ proves

$$
(T^3-T)b=0\quad\Longleftrightarrow\quad q\mid z^3-z.
\tag{SPC.16}
$$

Selfadjointness also gives

$$
\Delta=\langle b,(T^3-T)^2b\rangle
=\|(T^3-T)b\|^2\ge0.
\tag{SPC.17}
$$

Theorem 2.1 proves (SPC.15). Polynomial division and comparison of exact rationals decide it. Starting from the retained $q$ and $(m_0,\ldots,m_{N-1})$, (SPC.11) supplies the finite list through index six. At $N=1$ or $2$, some displayed moments were not actual acquisition outputs; this local extension is explicitly a prediction from the earned law. At $N\ge3$ the acquisition already includes them.

In the bad class the nonconstant monic $q$ divides the degree-three polynomial $z^3-z$, so $N\le3$. Equation (SPC.16), multiplied by $T^{k-1}$ for $k\ge1$, gives $T^{k+2}b=T^k b$. On this cyclic path it also gives $T^3=T$. There is no assertion of this equality between $x_0$ and $x_2$: a nonzero zero-eigenspace component can disappear at the first Tick. $\square$

## 4. Four independent expressions on the good passive image

**Definition 4.1 (the four exposed data types).** Let

$$
\mathcal D_{\rm good}
=\{(T,k,x):T\text{ satisfies (SPC.1) and is good},\ k\ge2N,\ x=T^k b\}.
\tag{SPC.18}
$$

The four expressions on this common actual image are as follows.

| Expression | Exposed data and independent meaning |
| --- | --- |
| Space $S$ | The native rooted weighted path $T$ and its present field $x$, in actual rooted-distance coordinates. |
| Time $\mathcal T$ | The actual paid ordered root list $(m_0,\ldots,m_k)$, as in (SPC.3). |
| Boundary $B$ | The finite reduced rational endpoint transfer $F_T$ and its trailing literal pair $(m_{k-1},m_k)$, observed at two consecutive actual passive cuts. |
| Memory $M$ | The least monic recurrence $q$, the first $N$ impulse moments $\mu=(m_0,\ldots,m_{N-1})$, and the $N$-entry predictive state $w=(b^{\mathsf T}T^j x)_{0\le j<N}$. |

Thus $w_j$ predicts the root after $j$ future passive Ticks, including the current root at $j=0$. Boundary has two actual past/current scalar readings and no phase label; it has no unmeasured future output. Memory contains predictions rather than an archive of all source events. Space exposes adjacency and a present field rather than a journal. Time exposes only the specified passive root observations, not arbitrary prior Reads, Holds, controls, durations or implementation events. None of these numeric data types includes an operational right or a source reference.

**Theorem 4.2 (effective four-view recovery and route agreement).** Every expression in Definition 4.1 determines exactly the same $(T,k,T^k b)\in\mathcal D_{\rm good}$, by an exact procedure terminating on its declared actual image. Consequently all recovery routes between the four expressions agree.

**Proof.** First, for an earned good $T$, enumerate locally

$$
(b,Tb),\ (Tb,T^2b),\ (T^2b,T^3b),\ldots
\tag{SPC.19}
$$

and compare the corresponding root pairs with a supplied pair promised to be $(m_r,m_{r+1})$. Rational multiplication and equality tests suffice. The true finite $r$ is reached, and Theorem 2.1 makes the match unique. There is no assertion that this search recognizes inputs outside the image or has a bound in $N$ alone.

From Space compute the pair

$$
(b^{\mathsf T}x,b^{\mathsf T}Tx)=(m_k,m_{k+1})
$$

locally from its given law and full present field. Apply (SPC.19) to recover $k$. Its given $T$ and $x$ are already the native law and field. Computing the second number is not an actual source Tick.

From Time, its length gives $k$. Since $k\ge2N$, its initial segments contain the first singular $H_N$. Apply Proposition 3.1 to those already acquired values, issuing no new source calls, to recover the native $T$ and then compute $T^k b$.

From Boundary, the formal Laurent expansion of its finite rational $F_T$ gives the impulse sequence. Its first flat block and the native reconstruction recover $T$ and $N$ by Proposition 3.1. Match its given literal pair to $(m_r,m_{r+1})$ using (SPC.19). This yields $r=k-1$, so the current phase is $k=r+1$, with current field $T^k b$. The result uses the last element of the pair as the current cut, not the first.

From Memory, the degree of its least recurrence is $N$. The recurrence and its $N$ initial moments generate the prefix through $2N$ and hence the native law. If $N\ge2$, its first two predictive entries are $(w_0,w_1)=(m_k,m_{k+1})$, determining $k$. If $N=1$, write $q=z+q_0$; the pair $(w_0,-q_0w_0)$ has the same meaning and determines $k$ as well. Finally set

$$
\mathcal O_N=
\begin{pmatrix}b^{\mathsf T}\\ b^{\mathsf T}T\\ \vdots\\ b^{\mathsf T}T^{N-1}\end{pmatrix}
=K_{N-1}^{\mathsf T}.
\tag{SPC.20}
$$

It is invertible by (SPC.8), so $w=\mathcal O_Nx$ recovers the entire native field $x=\mathcal O_N^{-1}w$. On the passive image this equals $T^k b$.

Conversely the recovered triple computes the specified finite transfer, least recurrence, initial moments, present field, predictive window, and finite root list and suffix. Each expression therefore maps back to itself as numerical data, and every route factors through the same unique triple. If $V_i$ denotes a view and $D_i$ its inverse to that triple, then on the common image $D_iV_i$ is the identity and every conversion is $V_jD_i$. Thus

$$
(V_lD_j)(V_jD_i)=V_lD_i,
\tag{SPC.21}
$$

which is route agreement for every choice of views.

The Time values regenerated from another view equal the actual paid list, because the actual initialization and passive run are premises of the image. This numerical equality neither fabricates acquisition provenance nor recovers unrecorded Read/Hold timings. The analogous distinction applies to reproducing Boundary's literal suffix from the law and phase. $\square$

**Proposition 4.3 (intertwining passive Tick).** The inverses in Theorem 4.2 intertwine the four updates with the actual passive Tick

$$
(T,k,x)\longmapsto(T,k+1,Tx).
\tag{SPC.22}
$$

Space updates its native field by $T$. Time appends the actual return $m_{k+1}$. Boundary keeps $F_T$ and changes its suffix from $(m_{k-1},m_k)$ to $(m_k,m_{k+1})$, using that actual return. Memory keeps $(q,\mu)$ and changes $w$ to

$$
w'_j=w_{j+1}\quad(0\le j<N-1),\qquad
w'_{N-1}=-\sum_{j<N}q_jw_j.
\tag{SPC.23}
$$

These updates preserve $\mathcal D_{\rm good}$.

**Proof.** For every current field, $w'_j=b^{\mathsf T}T^{j+1}x$; the last entry is (SPC.23) because $q(T)=0$. The other three updates are exactly their definitions at the next actual passive cut. The new phase remains at least $2N$, and goodness is a property of the fixed rooted law. Each inverse therefore returns the same successor in (SPC.22). In particular Boundary's inverse reads its updated pair as beginning at phase $k$ and ending at phase $k+1$. Equation (SPC.21) also applies at that successor, so dynamics does not introduce a route-dependent phase offset. $\square$

## 5. Actual late-phase acquisition and the literal-window minimum

**Theorem 5.1 (two actual scalar outputs and the advanced installation cut).** Suppose the law of one good native source has been earned as in Proposition 3.1, and it is now at an authentic passive phase $k\ge2N$ whose counter has not been retained as an accessible input. One actual Read and one actual returning Tick suffice to identify the phase. One subsequent Hold protects local decoding and synchronized predictor installation at the true advanced cut $k+1$. The protocol uses two scalar outputs, one Hold acknowledgement and no Add.

If $N=1$ in the good class, one Read already suffices by its absolute root value. With a following Hold the synchronized installation can stay at the original cut $k$, with no Tick.

**Proof.** Read returns $r=m_k$. Execute one actual Tick; its returned output is $s=m_{k+1}$ and the actual field is now $T^{k+1}b$. Execute Hold. During this held interval match $(r,s)$ by (SPC.19) to obtain the unique $k$. Install

$$
\widehat x=T^{k+1}b,\qquad w=\mathcal O_N\widehat x
\tag{SPC.24}
$$

with the earned law and actual retained source capability. Both records describe the actual advanced field. The pair $(r,s)$ itself is now the trailing literal pair at cut $k+1$. Retaining an installation at $T^k b$ would fail synchronization; the protocol uses (SPC.24).

For $N=1$ write $T=(a)$. Goodness is exactly $0<|a|<1$, and $m_k=a^k$. The sequence $|m_k|=|a|^k$ is strictly decreasing on all $k\ge0$. Exact enumeration of these rational magnitudes therefore identifies $k$ from the one actual root output, even when $a<0$. Hold then permits installation of the unchanged actual field $a^k$. No logarithm, real approximation or phase oracle is needed. $\square$

The known law used here comes from the same specimen's authenticated preparation and actual acquisition. If it is instead supplied by another installation, equality of numeric laws does not supply the continuity, passivity or capability hypotheses of this theorem.

**Theorem 5.2 (minimum uniform consecutive literal-root width).** Among observations consisting solely of a consecutive window of literal scalar roots, with the law already known, width two is the minimum uniform width that identifies every good passive phase throughout the signed native class. This remains true after restriction to arbitrarily late passive tails. The assertion is about the number of scalar entries in this specific window, not arbitrary sensor dimension, bit length, scalar encodings of multiple values or all adaptive identification procedures.

**Proof.** Theorem 2.1 proves that the forward window $(m_k,m_{k+1})$ identifies every $k$. Equivalently the trailing window $(m_{k-1},m_k)$ identifies every $k\ge1$, including every cut in (SPC.18).

For the necessary failure of width one, fix any rational $0<a<1$ and the native two-cell source

$$
T=\begin{pmatrix}0&a\\a&0\end{pmatrix},\qquad b=e_0.
\tag{SPC.25}
$$

It has eigenvalues $a,-a$, positive link $a$, and $T^2=a^2I$. It is good, with

$$
m_{2r}=a^{2r},\qquad m_{2r+1}=0.
\tag{SPC.26}
$$

On every infinite tail, two different odd phases have the identical one-entry literal window zero. In particular such phases can both exceed the law-acquisition cut $2N=4$. Thus width one fails even with this exact known law and arbitrary local computation. The same example excludes width zero. Together with the width-two construction this proves the asserted minimum.

A sensor giving, for example, the locally computed scalar $\|T^k b\|^2=m_{2k}$ has a different observation meaning. On every good source these values strictly decrease: in (SPC.4) each difference $m_{2k}-m_{2k+2}$ is nonnegative and an interior rooted eigenvalue makes it positive. Such an extra full-field quadratic sensor would identify phase with one scalar. It is not a literal root port in Definition 1.1 and is not installed by this argument. $\square$

## 6. Retained prediction for arbitrary current fields and controls

**Definition 6.1 (the callable record).** Retain the earned $(T,q,\mu)$, a predictive state $w$, and, in a redundant native-coordinate version, a field record $\widehat x$. These are installed while the same actual source is held. At acquisition use the genuine cut $h=2N$; at the two-output late entry use $h=k+1$; at the scalar one-output entry use $h=k$. In each case initialize

$$
\widehat x=T^h b,\qquad w=\mathcal O_N\widehat x.
\tag{SPC.27}
$$

Keep the actual reference, rights and backing as separate installed resources. Serialize each real source call and its local record update before exposing the next completed cut. A forecast made on scratch data sends no command to the source.

The retained update rules are

| Command | Predictive record | Native record | Predicted complete output |
| --- | --- | --- | --- |
| Read | unchanged | unchanged | $w_0$ |
| Tick | (SPC.23) | $T\widehat x$ | new $w_0$ |
| Hold | unchanged | unchanged | declared Hold acknowledgement |
| Add$(u)$, when installed | $w_j\leftarrow w_j+u\mu_j$ for every $j<N$ | $\widehat x\leftarrow\widehat x+ub$ | declared Add acknowledgement |

**Theorem 6.2 (all-field sufficiency and complete common future use).** For every earned native law, good or bad, the map $x\mapsto\mathcal O_Nx$ is a bijection on $\mathbb Q^N$. For every rational field $x$, the update table of Definition 6.1 predicts the complete output and entire successor for each installed command. Starting from any actual synchronized installation, it therefore predicts every finite common adaptive continuation, including rational Add inputs when authorized, while maintaining

$$
\widehat x=x_{\rm actual},\qquad w=\mathcal O_Nx_{\rm actual}.
\tag{SPC.28}
$$

This is an assertion about future behavior from the current field. It does not recover the past control journal from that field.

**Proof.** Equation (SPC.20) and cyclicity give invertibility over $\mathbb Q$. Thus the predictive state determines the complete native field, for arbitrary $x$, with no passive-orbit restriction. This also explains the length of this particular predictive window. For $0\le r<N$, the first $r$ rows of $\mathcal O_N$ have a nonzero rational kernel vector $v$, whereas $\mathcal O_Nv\ne0$. Hence $x$ and $x+v$ have the same first $r$ predicted roots but differ at some later index below $N$. Fewer than $N$ consecutive predictive entries cannot preserve complete arbitrary-field future root prediction. This is the supplied linear-observability dimension argument for this task, not an arbitrary-encoding memory lower bound or a lower bound for passive phase alone.

Read and Hold preserve (SPC.28) and have the stated outputs. For Tick, $q(T)=0$ gives (SPC.23) for every $x$, and its new first entry is exactly $b^{\mathsf T}Tx$, the returning root. For Add,

$$
\bigl(\mathcal O_N(x+ub)\bigr)_j
=(\mathcal O_Nx)_j+u b^{\mathsf T}T^jb
=w_j+u\mu_j.
\tag{SPC.29}
$$

The native update is the actual source update; its acknowledgement is part of the installed contract, rather than an inferred measurement. These identities establish the one-operation invariant and complete declared outputs.

Induct on the finite command sequence. Equal earlier outputs cause a common adaptive policy to select the same next command, input and stopping choice; the one-operation identities preserve synchronization. A common fixed random tape may be included among the policy's inputs, giving the same induction for each tape. All legal input rights and serial execution conditions remain the installed ones. Goodness is unnecessary for this future-use invariant.

An explicit limitation already present in P, Counterexample 42.1, remains within this class. For $T=(1/2)$ and any current rational $v$, a Tick followed by Add$(v/2)$ returns the current field to $v$, whereas the empty continuation leaves it at $v$ already. Their tick and pulse journals differ. If that command/output history is not retained, the equal current fields have identical common future behavior. Thus invertible all-field predictive coordinates do not imply controlled-history inversion. $\square$

## 7. The bad-class obstruction includes complete future behavior

**Theorem 7.1 (the native field cannot recover the missing two-step chronology).** Fix a bad native source. For every $k\ge1$, cuts $k$ and $k+2$ have the identical native law and complete present field, although their actual passive root lists have different lengths. In particular this holds for all $k\ge2N$, when Boundary and Memory also coincide at the two cuts. If the same reference/right installation is retained and no separate counter, archive or phase-bearing metadata is an input, every common finite continuation in the declared menu has matching complete outputs and corresponding identical successors at the two cuts, including installed Add inputs and adaptive choices.

Consequently no function of the native law and complete current field, nor any such common future experiment, can recover the passive transcript length on this bad late-passive image.

**Proof.** Theorem 3.2 gives $T^{k+2}b=T^kb$ for $k\ge1$. Thus the actual native law and field agree at the two cuts. The lists (SPC.3) have lengths $k+1$ and $k+3$, so they are distinct ordered finite lists even when their later values alternate or are constant. At $k\ge2N\ge2$, both entries of the trailing pair have index at least one and hence repeat after two Ticks; the transfer is fixed. Memory is a function of that fixed law and the equal complete fields. Thus those two expressions also coincide at these late cuts.

The menu's legality depends only on its installed rights and its rational input, and its field successors depend only on $(T,x,u)$ as applicable. Identical fields therefore give identical Read roots, identical Tick returns and fields, identical Hold acknowledgements, and identical Add acknowledgements and fields for every common $u$. Induction gives identical outputs and successors for a fixed finite word. For a common adaptive policy, identical earlier observations yield identical next commands and inputs; the same induction applies, including a common random tape. No hidden phase is an argument of the menu's declared output or transition.

If a claimed reconstruction from the law and field existed, applying it to these identical inputs would yield one transcript length at both cuts, contradicting the two different lengths. The future-indistinguishability just proved gives the analogous obstruction to an experiment trying to choose that length from later declared outputs.

A separately retained counter or archive distinguishes the entries because it supplies additional information. It is outside the indistinguishable input, rather than a counterexample to this theorem. At phase zero a zero-eigenvalue component can still be present; the theorem's $k\ge1$ condition preserves that distinction. $\square$

## 8. Same-run calls, exact arithmetic and simultaneous resources

**Definition 8.1 (resource coordinates).** Encode each rational by its reduced signed numerator and positive denominator in binary, with decodable framing; let $\ell(r)$ be that word length. Let $B$ be the total length of the $2N-1$ native coefficient words, so $B=\Omega(N)$. This is a parameter for charging actual resources, not advice to the acquisition protocol. A rational arithmetic count carries its actual operand and result widths. Positive rational-square-root extraction on a promised square is charged separately from field operations. Programs, counters, output framing, source reference, call rights, Hold control, preparation and backing are additional resources on the same run.

**Proposition 8.2 (attained actual call and traffic counts).** The acquisition in Proposition 3.1 uses exactly one Read, $2N$ Ticks, $N+1$ Holds and no Add. Its scalar return count is $2N+1$; its other returns are $N+1$ fixed Hold acknowledgements. The last held interval includes law decoding and synchronized installation at cut $2N$.

The general late protocol in Theorem 5.1 uses one Read, one Tick and one Hold, giving two scalar returns and one acknowledgement. Its source is installed at the advanced cut $k+1$. The $N=1$ one-output variant uses one Read and one Hold, with no Tick, and stays at cut $k$.

A direct simultaneous-buffer native Tick evaluates $3N-2$ scalar multiplications and $2N-2$ scalar additions. Thus acquisition has source arithmetic

$$
2N(3N-2)\text{ multiplications},\qquad
2N(2N-2)\text{ additions},
\tag{SPC.30}
$$

and the general late protocol adds one such Tick. Actual transmission includes each rational word, command frame, acknowledgement and any rational Add input separately.

**Proof.** There is one Hold before the initial Read and one after each of the $N$ tick pairs. Each Tick returns its new root, so no extra Read supplies the intermediate moments. After the final Hold all computation uses the already earned prefix and protected current field. The late protocols are their stated serial words.

For a direct Tick the $N$ diagonal terms and the two directed contributions from each of $N-1$ links give $3N-2$ products; summing the rows uses $(3N-2)-N=2N-2$ additions. Two state buffers prevent overwriting inputs. This convention evaluates the stored slots even if some diagonal entries are zero. It is an attained implementation, not a lower bound against algebraic simplification.

If the command-frame lengths are $\ell_R,\ell_T,\ell_H$ and the Hold acknowledgement length is $a_H$, acquisition's combined request/return traffic in these units is exactly

$$
\ell_R+2N\ell_T+(N+1)\ell_H
+\sum_{j=0}^{2N}\ell(m_j)+(N+1)a_H.
\tag{SPC.31}
$$

The late pair protocol instead adds $\ell_R+\ell_T+\ell_H+\ell(m_k)+\ell(m_{k+1})+a_H$. The scalar variant adds $\ell_R+\ell_H+\ell(m_k)+a_H$. Setup, serialization buffers and controller work are still separate coordinates. $\square$

**Proposition 8.3 (one attained arithmetic and width account).** Acquisition and signed law decoding admit the same conservative bounds as P, Proposition 41.3:

$$
O(N^4)\text{ rational field operations},\qquad
N-1\text{ positive rational-square-root extractions},\qquad
U=O\bigl(N^2B+N\log(N+1)\bigr)
\tag{SPC.32}
$$

for maximum integer/rational intermediate width. The test (SPC.15) is additional finite rational calculation from that law, with no new port. Once the law is known, one attained late-pair decoding and installation uses $O(N(k+N+1))$ local field operations, with a conservative width bound

$$
V_k=O\bigl(U+(k+N+2)B+\log(k+N+2)\bigr).
\tag{SPC.33}
$$

These are upper bounds for specified exact calculations. They are neither bit/runtime optima nor phase-independent bounds in $N$.

**Proof.** Put $D$ equal to the product of the native coefficient denominators. This is used to prove a bound; it is not supplied before acquisition. Then $\log_2D\le B$, every coordinate of $T^jb$ has denominator dividing $D^j$, and every such coordinate has absolute value at most one because $\|T\|\le1$. Thus the acquired moments and source values through $2N$ have width $O(NB+1)$. Signed eigenvalues and endpoint eigenvalues preserve precisely this bound.

At each stage use the lcm of the currently acquired moment denominators to scale the tested block to integers. The final lcm $L$ divides $D^{2N}$ and has logarithm $O(NB)$. Every scaled entry is bounded by $L$ in absolute value. An $s$-row minor has absolute value at most $s^{s/2}L^s$, by Hadamard's inequality, so its width is $O(s\log L+s\log(s+1))$, within (SPC.32). Fraction-free elimination expresses its pivots through these minors and exact divisions. All leading pivots before the first flat block's final zero are nonzero, by the strictly positive Gram blocks. Products before exact division still have width $O(U)$.

A cubic elimination at each size $r+1$, $1\le r\le N$, costs $O(N^4)$ field operations in total. The monic orthogonality solves and (SPC.10), with integer-scaled augmented columns, obey the same minor bounds and another $O(N^4)$ allowance. With a common determinant denominator for each solved $p_j$, its norm and diagonal pairings are sums of at most $(j+1)^2$ bounded products over a common denominator. They stay within $O(U)$ width rather than multiplying unrelated denominators term by term. This is exactly P's width argument: it uses Gram positivity and absolute bounds, and no positive shifted block.

Each of the $N-1$ rational-square roots in (SPC.13) is implemented by integer-root extraction on its reduced numerator and denominator, followed by exact squaring checks. These are $2(N-1)$ integer-root calculations on width $O(U)$ inputs. Tridiagonal continuants compute the finite transfer within a conservative cubic polynomial-arithmetic allowance and the same width bound. Sparse propagation to cut $2N$ and a further $N-1$ local steps construct (SPC.27) in $O(N^2)$ field operations. The finite recurrence extension through index six for (SPC.15) fits within these bounds.

If $A(W)$ charges a rational field operation including reduction at width $O(W)$ and $R(W)$ an integer-root calculation at that width, the algebraic decoding cost is bounded by $O(N^4A(U)+NR(U))$, with its actual comparisons, lcm/gcd, counters, allocations and serialization also charged. Thus an arithmetic count is not a unit-cost real-number assertion.

For the late step, generate (SPC.19) by sparse native multiplication and keep its two current candidate fields and a growing integer index. At the unique matching pair the fields are $T^kb,T^{k+1}b$, so the second candidate is already the required installed field. The search takes $k+1$ candidate comparisons and at most $k+1$ sparse multiplications from $b$. Constructing its $N$ predictive entries adds $N-1$ sparse steps, hence $O(N(k+N+1))$ operations. All powers used have exponent at most $k+N$, up to an immaterial one-step buffer, so the denominator and norm bounds give (SPC.33), including the fixed law arithmetic and growing index. In the scalar variant the same argument enumerates magnitudes with $O(k+1)$ operations and no actual source advance. $\square$

**Definition 8.4 (a simultaneous layout).** A concrete law-acquisition/installation layout keeps the following resources together; its stores are added, not selected from separate best cases.

| Coexisting item | Numerical storage or explicit separate charge |
| --- | --- |
| The actual native specimen | $N$ cells, $N-1$ links, coefficient storage $B$ |
| Two actual source state buffers at acquisition | $O(N^2B+N)$ bits |
| The earned $2N+1$ scalar prefix | $O(N^2B+N)$ bits |
| Elimination and polynomial scratch | $O(N^2)$ words of width $O(U)$ |
| Retained $T,q,\mu,w$ and redundant $\widehat x$ | $B+O(NU+N^2B+N)$ bits |
| Source reference, Read/Tick/Hold rights and optional Add right | their actual representation and backing |
| Authentic preparation, class/root assurance and Hold/controller installation | their actual preparation, retained representations and backing |
| Program, parsers, finite controls, indices and output buffers | their actual simultaneous bits; output copies are each counted |

The local index uses $O(\log(N+1))$ bits at acquisition. Preparing the authentic field includes the zero values in the other cells. A reference binds this specimen but exposes neither a free phase nor an additional cap, port or source description. A common backing can be counted once only if it is actually shared.

At a late cut $h=k+1$, the same numerical layout may retain the earned prefix and law while using two $N$-entry candidate fields, $N$ predictive entries and a redundant $N$-entry native record at width $O(V_k)$. The actual source still has its two buffers, with current coordinate width $O((h+1)B+1)$. The old algebraic scratch can be released; if retained, it is charged as $O(N^2U)$ bits. The local phase index now has $O(\log(k+2))$ bits. Fixed-law stores, earned prefix, candidate work, present record, output words, reference/rights and actual source all coexist. This gives, for example, the conservative numerical sum

$$
2B+O\bigl(N^2B+NU+N^2U+NV_k\bigr)+L_{\rm out},
\tag{SPC.34}
$$

when the old scratch is retained, in addition to the separately charged program, assurance, control, references, rights and backing. This sum has not included a complete archive through phase $h$.

**Proposition 8.5 (same-specimen lifetime accounting and later widths).** Suppose acquisition is followed on that same specimen by $k-2N$ further passive Ticks, then by the general late protocol. The source has made exactly $k+1$ lifetime Ticks and two lifetime Reads, returning $k+3$ scalar outputs in total. The Holds are the acquisition's $N+1$, the late protocol's one, and any actually inserted intervening Holds. The late entry need not retain the number of intervening Ticks; their actual source work and scalar traffic remain part of this same run.

A full materialization of the Time expression, or a separate command archive, has its own storage and construction cost. Even $N=1$ does not bound exact output widths independently of phase. After Add inputs, widths also depend on the actual inputs and continuation, not just $N,B$ and passive phase.

**Proof.** There are $2N+(k-2N)+1=k+1$ Ticks. The initial and late Reads are distinct calls, even when the late Read duplicates the previous Tick's scalar value. Each Tick returns one scalar, giving $k+1+2=k+3$. Time includes the initial root and the Tick outputs, so the extra late Read does not increase its designated length. Holding and streaming rather than retaining intermediate outputs does not undo their physical calls or traffic. In the scalar variant no final Tick is made: the corresponding totals are $k$ Ticks, two Reads and $k+2$ scalar outputs.

At any passive epoch $h$, the state coordinates and predictive entries have widths bounded by $O((h+N)B+1)$. A materialized root list through $h$ therefore has an upper bound $O((h+1)^2B+h+1)$ bits, as well as the local propagation and serialization work used to construct it. It is not a fixed-size memory component in (SPC.34). For the good scalar law $T=(1/2)$, the literal root $2^{-h}$ has denominator length $h+1$, and the full list has $\Theta((h+1)^2)$ bits. This establishes unbounded literal width at fixed $N$, rather than a lower bound on every possible phase algorithm.

For later use, predictive Tick has $N$ recurrence products, $N-1$ additions and a shift/copy. Add has $N$ products and $N$ additions for $w$; retaining $\widehat x$ adds its own update, including one native-root addition for Add and the direct native Tick arithmetic for Tick. Read serializes the current output and Hold returns its acknowledgement, with actual control work. Source updates are charged in addition to these observer updates.

An arbitrary rational pulse may have unbounded encoding length and may increase the field norm. Therefore the passive bound $|x_i|\le1$ is not used after controls. Arithmetic and transmission are charged at the actual maximum widths along that finite continuation, including the inputs. A policy retaining every command/output keeps additional growing storage. Finite dimension, a finite recurrence and a finite program supply none of these stores for free. $\square$

**Proposition 8.6 (the positive-class lower horizon does not transfer).** The every-source $2N$ lower horizon of P, Theorem 38.3, is not an every-source lower bound for the closed signed class (SPC.1), although Proposition 3.1 attains $2N$ on every source.

**Proof.** After the initial Read, execute one returning Tick. If $m_1=1$ or $m_1=-1$, the unit vector and contraction bound give

$$
1=|\langle b,Tb\rangle|\le\|Tb\|\le1.
$$

Equality in Cauchy–Schwarz yields $Tb=m_1b$. Native cyclicity then forces $N=1$, and the entire law is $T=(m_1)$. If neither equality occurs, continue the acquisition schedule of Proposition 3.1, taking its still-needed $m_2$ and then the later pairs. This is one uniformly correct protocol on the whole signed class, yet it certifies $N=1$ and the full law after one Tick on each endpoint scalar source, less than $2N=2$.

P's strict positive-tail extension uses a positive Schur-complement margin at both spectral endpoints. In the present class a scalar endpoint $T=(1)$ cannot receive a nonzero extra positive link while preserving $T\preceq I$: a positive semidefinite $I-\widetilde T$ with first diagonal zero must have its first row zero, by its two-by-two principal minors. The endpoint $-1$ has the analogous obstruction for $I+\widetilde T$. Thus that supplier's witness family is not an available every-source extension here. The argument proves neither a different global acquisition optimum nor a universal minimum scalar-output count. $\square$

## 9. Suppliers, parameter correspondence and the remaining programme

**Convention 9.1 (fixed sources and mathematical credit).** Repository references in this volume are interpreted at public revision [39687802cb999fa97ebdbf17f226a541563cc351][Pin]. Ordinary proofs here carry no assertion of fresh Lean verification. The finite spectral theorem, Gram positivity, Jacobi inverse spectral theory, finite observability, rational linear algebra and polynomial recurrence methods are mature theory. Their roles and the actual hypotheses used here are the following.

| Supplier | Actual correspondence and limit |
| --- | --- |
| [P, §§36–37, 39–41][P] | Its actual serial Read/returning-Tick/Hold menu, native root, unit preparation, Gram acquisition, positive-link orientation, least recurrence, reduced transfer and predictive state are the direct suppliers. Symmetry and positive links suffice for its Gram/Jacobi algebra. Its passive one-root phase proof uses $0<T<I$; (SPC.6) supplies the signed replacement, with a two-entry literal suffix in Boundary. Its arbitrary-field predictor is preserved in §6. |
| [Main, §137.13][Main] | Use its equal-rank even Gram block and invariant-Krylov all-future mechanism with scalar input $J(u)=ub$, $r=N$, $M_j=m_j$. Its shifted positivity $S_{N-1}\succeq0$ concerns a positive realization. The signed proof uses selfadjointness and the zero norm of $q(T)b$ and does not claim that shifted positivity. |
| [Finite Ho–Kalman source][HK] and [owning Scribe][HKS] | `sample_factorizations`, `factorized_exact_recovery`, `finite_samples_exact_recovery` and `finite_samples_order_lower_bound` supply finite block algebra. Here $F=\mathbb Q$, one input/output, $h=N$, samples $s_j=m_j$ for $0\le j<2N$, reference $A=T$, input $B=b$, output $C=b^{\mathsf T}$, selected times $0,\ldots,N-1$, and order $N$ after the actual first flat block. A nonsingular block alone supplies a dimension lower bound; native cyclicity and flatness supply the upper-order/acquisition bridge. |
| [Coefficient-driven Jacobi source][CJ] and [owning Scribe][CJS] | `coefficient_driven_jacobi_characteristic_polynomial` and `multiplication_matrix_charpoly` supply monic Gram–Schmidt/Jacobi and companion characteristic-polynomial algebra. Take $E=\mathbb R^N$, power basis $T^jb$, $q$ from (SPC.10), moment $m$, actual Euclidean inner product and coefficient multiplication equal to actual $T$. Its Hankel, strict-positivity and selfadjointness hypotheses are exactly (SPC.8)–(SPC.10). Normalization of its monic basis is the actual positive-link cell basis by (SPC.12). Its private `orthogonal_power_basis_monic`, `orthogonal_power_basis_upper_zero`, `squared_norm_pos`, `jacobi_subdiagonal_one` and `jacobi_tridiagonal` already support this algebra; they are credited rather than treated as missing new results. |
| [Finite Stieltjes source][FS] and [owning Scribe][FSS] | Private `finite_hankel_eq_gram` and `finite_hankel_posSemidef`, and public `moment_eq_operator_pairing`, use nonnegative weights and allow arbitrary real nodes in those particular claims. Take nodes $\lambda$ and weights $w_\lambda$ from (SPC.4). The public combined `finite_stieltjes_operator_realization` also assumes nonnegative nodes; it is not invoked for negative spectrum. |
| [Atomic Hankel–Vandermonde source][HV] and [owning Scribe][HVS] | `hankel_moment_matrix_factorization` and its shifted/pencil companions apply to arbitrary finite complex nodes and weights. Here real $\lambda,w_\lambda$ embed into $\mathbb C$, and `order` is the number of moment rows. These identities do not require distinct nodes or imply positive rank on their own; actual native rank comes from (SPC.7)–(SPC.9). |
| [Gram–Schmidt coefficient-field source][GSC] and [owning Scribe][GSCS] | Its `gram_schmidt_coordinates_mem_coefficient_field` has a normalized companion-trace-moment hypothesis. The rooted weights here need not be uniform trace weights. That extra hypothesis is not silently imported; rational recovery instead uses the actual moment solves and promised rational link squares in Proposition 3.1. |
| [Pinned mathlib Gram–Schmidt][MathGS] | At dependency revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, `gramSchmidt_orthogonal`, `gramSchmidt_triangular` and `gramSchmidtBasis` are upstream suppliers used by the coefficient-driven source. The real power basis is indexed by $0,\ldots,N-1$ and is independent by (SPC.8). Reading these declarations supplies provenance, not a new compilation claim. |
| G. Teschl, *Jacobi Operators and Completely Integrable Nonlinear Lattices*, AMS Mathematical Surveys and Monographs 72, [§2.5, (2.109)–(2.118), printed pp.42–43, and finite-support paragraph on p.44][Teschl] | `literature-attested`: the Hamburger moment Gram form, orthogonalization, Jacobi coefficients and finite-support termination already include signed real spectral support. His $C(N+1)=0$ corresponds to $\det H_N=0$, his $a(n)$ to our $c_{n-1}$ and his $b(n)$ to our $a_{n-1}$. Theorem 2.13 assumes nonfinite support; it is the following finite-support paragraph, not that infinite-support hypothesis, that matches this finite source. The native reconstruction itself is credited. |

**Definition 9.2 (the relation to the other native owners).** The following source correspondences fix which parts of the broader common-relation objective are advanced by this construction.

[NDR, §§1–6][NDR] studies unknown immutable ordered labelled binary trees, all finite literal addresses, four-valued replies, independent context completions and paid reconstruction. Its source is not a rational Jacobi path; no tree reply is identified with a moment here. Its distinction between acquired values, retained context and actual chronology applies as a discipline: even a complete current source description need not recover past events. Theorem 7.1 supplies that obstruction for the actual signed path, rather than transferring NDR's certificate or ratio bounds.

[Process Geometry, §§44.1 and 44.9][PG] has one evolving native tree, declared substitution/graft actions, separately supplied read ports, and simultaneous node/address/record costs. Its actual-image and one-history requirements are preserved here by one fixed path and actual returning Ticks, not by importing a free tree update or a free affine sensor. Its same-run resource accounting is the relevant comparison for §8; no node-count bound becomes a rational bit-cost bound.

[Constructor Boundary Networks, §1 and its native boundary constructions][CBN] assumes a finite-depth stationary tree family, paid preparation, later target selection, complete retained alphabets, and an authentic supplied iteration count in its trajectory decoder. Here the source evolves by $T$, the root target is fixed, and no count is supplied: on the good image the count is earned from the literal pair. Its target-after-preparation, correlated tree fibers and boundary-network cardinalities are not suppliers of this signed clock, and their original tasks are not settled by it.

[Wave, §§4 and 12–13][Wave] distinguishes rooted spectral weights from an uncalibrated eigenvalue list, and supplies conditional finite-wave representations with explicitly installed references and records. A unitary correlation has unit-modulus spectral nodes; it is not identified with the contractive impulse law (SPC.2). In fact the real selfadjoint bad rooted support $\{-1,0,1\}$ locates why surviving unit-modulus components can fail to clock this passive task. No coherent phase-reference or quantum instrument is added to the rational root menu.

The public additions [Attractive Boundary Response, §9][ABR] and [Quadratic Clock Uniform Designs, §30][UQD] retain different original sources: respectively a whole-group heat/Green form with its original clock and a common fixed quadratic report world $(\tau,A,B,\eta)$ over integer indices. The former has infinite-dimensional analytic domains, and the latter permits unknown gain/zero and bounded adversarial report errors. Neither installs the unknown finite rational path, exact root serialization, authentic impulse or returning-Tick/Hold interface here. Conversely this source's exact rational phase test supplies neither a full-Green inequality nor a noisy quadratic-clock minimax bound.

**Conclusion 9.3 (the source-relative advance and exact limits).** The `repo-derived` contribution is the conjunction of the exact rooted cubic/two-output criterion in Theorem 2.1, its rational good/bad decision on the actually acquired native law, the four independently specified expressions with compatible recovery on $k\ge2N$, the paid late-phase protocol at its true advanced cut, and the complete native bad-class future indistinguishability. The signed Jacobi reconstruction and generic all-field predictive algebra are credited suppliers with explicit hypothesis correspondences. This classification extends P's positive passive-clock consumer to precisely the good part of the closed signed class and identifies the obstruction on its complement; it does not claim that Hamburger/Jacobi reconstruction is new.

The acquired objects are the actual initial Read and returning Tick outputs. The class, source fixedness/binding, authentic preparation, exactness, Hold, reference, rights and backing are supplied premises. The class decision and predicted missing moments are finite consequences of the earned law. Arbitrary-field future prediction survives installed Add, whereas passive phase inversion does not invert arbitrary controlled histories. Literal-window width two is the stated uniform minimum; no arbitrary-sensor lower bound, positive-class horizon inheritance, global bit/runtime optimum or minimum total physical resource follows.

This conditional single-source result leaves the original fixed-$G_{\rm gc}$/original-$Q$ tasks in their stated domains. It does not construct a common realization for all source models, derive all physical laws, prove universal $\alpha/\beta$ generation, or complete the continuing space/time/boundary/memory programme. Bridges to physical acquisition and to other original apparatuses require their own actual initialization, operations, observations and resource correspondences. No worldwide originality or proof-assistant certification is asserted.

[Pin]: https://github.com/the-omega-institute/trureturing/tree/39687802cb999fa97ebdbf17f226a541563cc351
[P]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY_II.md
[Main]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md
[NDR]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DISCOVERY_AND_RETAINED_CONTEXT.md
[PG]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md
[CBN]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[Wave]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/docs/develop/theory/AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md
[ABR]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/docs/develop/theory/FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md
[UQD]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/docs/develop/theory/FIB_UNCALIBRATED_QUADRATIC_CLOCK_UNIFORM_REPORT_DESIGNS.md
[HK]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.lean
[HKS]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/Blueprint/D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.scribe.cs
[CJ]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.lean
[CJS]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/Blueprint/D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.scribe.cs
[FS]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/D5/S3/Constants/FiniteStieltjesOperatorRealization.lean
[FSS]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/Blueprint/D5/S3/Constants/FiniteStieltjesOperatorRealization.scribe.cs
[HV]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.lean
[HVS]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/Blueprint/D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.scribe.cs
[GSC]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/D5/S3/Constants/Moments/GramSchmidtCoefficientField.lean
[GSCS]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/Blueprint/D5/S3/Constants/Moments/GramSchmidtCoefficientField.scribe.cs
[MathGS]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.lean
[Teschl]: https://www.mat.univie.ac.at/~gerald/ftp/book-jac/jacop.pdf

## 追加锚（本行以下为增补区）
