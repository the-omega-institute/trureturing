# Episturmian refined repetition

## 1. Definitions and source conventions

**Definition 1.1 (Primary language and directive limits).** Let $A$ be a finite alphabet.
For $a\in A$ put $L_a(a)=a$ and $L_a(b)=ab$ for $b\ne a$, and compose morphisms in
written order. For a directive $\Delta\in A^{\mathbb N}$ write
$\mu_n=L_{\Delta_0}\cdots L_{\Delta_{n-1}}$, with $\mu_0$ the identity.
Starting from $u_0=\varepsilon$, let $u_{n+1}$ be the shortest palindrome beginning
with $u_n\Delta_n$, and set $c_\Delta=\lim_n u_n$.
An episturmian word with directive $\Delta$ means exactly a one-sided word $w$ with
$\mathcal L(w)=\mathcal L(c_\Delta)$, as in [P, §3]. This includes every intercept.
All factors $w[i,j)$ below are zero-based and half-open; $T$ is the shift and
$\ell(U)=(|U|_a)_{a\in A}$ is the Parikh vector.

A directive is strict on $B$ if its letters are precisely $B$ and every letter of
$B$ occurs infinitely often. Uniform recurrence of a directive means bounded gaps
of each of its finite factors. In particular, every letter in its alphabet has
bounded gaps. For a strict directive $y$ on $B$, let $X_y^+$ and $X_y^{\mathbb Z}$
be the one-sided and two-sided subshifts whose finite factors belong to
$\mathcal L(c_y)$. The strict episturmian language is minimal; consequently every
word in these subshifts has that whole language. Its recurrence and compactness
also show that every word of $X_y^+$ has a two-sided extension: realize each of its
longer prefixes at occurrences with arbitrarily long left contexts and take a
convergent subsequence. Thus both subshifts have exactly the primary language.
We use $\omega(\Delta)=\bigcap_{N\ge0}\overline{\{T^n\Delta:n\ge N\}}$.
Membership $y\in\omega(\Delta)$ means that every finite prefix of $y$ occurs in
$\Delta$ at arbitrarily large directive positions.

**Definition 1.2 (Exact refined exponent).** For words $U,V$ of the same positive
length $L$, Nguyen's $(\epsilon,\delta)$-closeness means that all mismatching
positions belong to the union of $\delta$ intervals of $\{1,\ldots,L\}$ whose
union has cardinality at most $\epsilon L$; empty intervals are allowed.
For $\rho\ge1$, Condition $(*)_\rho$ means that for every $\epsilon>0$ there are
one integer $\delta\ge0$ and integer sequences $r_k,s_k,t_k$ such that

$$
-1\le r_k<s_k<t_k,\qquad t_k\ge\rho s_k,\qquad s_k-r_k\longrightarrow\infty,
$$

and, eventually in $k$, the two length-$L_k=t_k-s_k$ words
$w[r_k+1,r_k+L_k+1)$ and $w[s_k+1,t_k+1)$ are $(\epsilon,\delta)$-close.
The integer $\delta$ is fixed before the sequence varies.
Set $\operatorname{Rdio}(w)=\sup\{\rho\ge1:(*)_\rho\}$.
Requiring exact equality instead gives Nguyen's ordinary exponent
$\operatorname{Dio}(w)$, and $\operatorname{Dio}(w)\le\operatorname{Rdio}(w)$.
These are precisely [N, Definitions 2.1, 2.3, 2.5], including period growth.

**Definition 1.3 (Joint local alignment).** A strict directive $y$ on $B$ has
property LA if, for every $0<\eta<1$, there are integers $q,S\ge1$ and
$z\in\mathbb N^B$ such that

$$
\sum_{a\in B}z_a=q,\qquad q\le\eta S,\qquad
\sup_{v\in X_y^+}
\bigl|\{0\le i<S:v_i\ne v_{i+q}\text{ or }\ell(v[i,i+q))\ne z\}\bigr|
\le\eta S.
$$

The vector $z$ is common to all starts and all model words. In particular this is
stronger than a bound on letter mismatches alone.

**Definition 1.4 (Endpoint and measure quantities).** For a uniformly recurrent
strict directive $y$ on $d\ge2$ letters, write $X=X_y^{\mathbb Z}$ and let $\mu$
be its unique invariant probability. The suppliers establishing uniqueness are
specified in Proposition 3.1. Put

$$
\begin{aligned}
p_X(n)&=|\mathcal L_n(X)|=(d-1)n+1,\\
b_X(n)&=|\{U\in\mathcal L_n(X):U_0\ne U_{n-1}\}|,\\
\beta_X&=\liminf_{n\to\infty}\frac{b_X(n)}{p_X(n)},\\
d_\mu(q)&=\mu\{x:x_0\ne x_q\},\qquad
\kappa=\liminf_{q\to\infty}d_\mu(q).
\end{aligned}
$$

Rigidity means that some $q_j\to\infty$ satisfy
$\|H\circ T^{q_j}-H\|_2\to0$ for every $H\in L^2(\mu)$.
A uniform factor-balance constant $F$ bounds the difference of the numbers of
fully contained, overlapping occurrences of every factor $U$ in any two
equal-length factors, independently of $U$. A frequency comparison constant
$R\ge1$ satisfies $\mu[U]\le R\mu[V]$ for all factors of the same length.
Distinct-factor counts $b_X(n)$ and sampled probabilities $d_\mu(n-1)$ are
separate quantities.

## 2. Transfer from a directive omega-limit

**Proposition 2.1 (All-intercept transfer).** Suppose $\Delta\in A^{\mathbb N}$
has bounded constant runs and $\omega(\Delta)$ contains a uniformly recurrent
directive $y$ strict on $B\subseteq A$ with LA. Then every episturmian word with
directive $\Delta$, with every intercept, has $\operatorname{Rdio}=\infty$.
There is no recurrence assumption on $\Delta$, and $B$ may be a proper subalphabet.

**Proof.** Choose $D\ge2$ with
$\forall i\ \exists j<D:\Delta_{i+j}\ne\Delta_i$, and put $C=D+2$.
For $m_n=\min_{a\in A}|\mu_n(a)|$ and $M_n=\max_{a\in A}|\mu_n(a)|$, the
bounded-run estimates [Repo, `mu_length_uniform_ratio`, `mu_length_blocks_ge`,
`mu_length_mono`] give

$$
M_n\le C m_n,\qquad m_n\ge\lfloor n/D\rfloor+1.                 \tag{2.1}
$$

Their stated bounded-run hypothesis is exactly the displayed condition on $D$;
it does not require every letter of $A$ to recur. The condition passes to $y$,
since its finite factors occur in $\Delta$. In particular $|B|\ge2$.

We first spell out the intercept interface from actual decoding, rather than
from equality of languages. By [P, §3.1, equation (1)], successive decoding of
any episturmian word $w$ gives tails $v_n$ directed by $T^n\Delta$ and

$$
w=T^{j_n}\mu_n(v_n),\qquad 0\le j_n<|\mu_n((v_n)_0)|.          \tag{2.2}
$$

Here is the strict offset bound. It is true at level zero. At the next decoding
write $v_n=T^b L_a(v_{n+1})$, $a=\Delta_n$, $b\in\{0,1\}$.
For $b=0$, the first new image begins with $\mu_n(a)$, and $v_n$ begins with $a$,
so the previous offset stays inside it. For $b=1$, actual decoding is chosen
because $v_n$ does not start with $a$. Thus $c=(v_{n+1})_0\ne a$ and $v_n$
starts with $c$. The deletion removes $\mu_n(a)$; the new offset is
$j_n+|\mu_n(a)|<|\mu_n(c)|+|\mu_n(a)|=|\mu_{n+1}(c)|$.
This proves (2.2) inductively for every intercept. The same argument applies to
every finite directive prefix and any of its actual tails.

Fix $\rho>1$ and $\epsilon>0$. Choose

$$
0<\eta\le\min\left\{\frac1{4C},\frac{\epsilon}{64C},
                         \frac1{4C(\rho+1)}\right\}.
$$

Choose $q,S,z$ from LA; hence $S\ge1/\eta\ge4C$.
Write $\psi_h=L_{y_0}\cdots L_{y_{h-1}}$ on the whole alphabet $A$.
The same growth estimate (2.1), applied to $y$ on $A$, permits a fixed $h$ with
$\min_{a\in A}|\psi_h(a)|\ge S+q$.
Extend $z$ by zero on $A\setminus B$.

We need a finite template statement for every word $v$ whose directive begins
with $y[0,h)$. Actual decoding gives
$v=T^k\psi_h(v')$, with $0\le k<|\psi_h(v'_0)|$.
Since every image has length at least $S+q$, the prefix $v[0,S+q)$ meets at most
two image blocks. For $b\in B$, the block $\psi_h(b)$ is a primary model factor:
$c_y=\psi_h(c_{T^h y})$, and the strict directed tail contains $b$.
For $c\in A\setminus B$, instead one has

$$
\psi_h(c)=u_h c,\qquad u_{h+1}=\psi_h(y_h)u_h.                 \tag{2.3}
$$

The central-word identity is [P, §3.1, identities (4)–(6)] in zero-based indexing.
The first identity follows by induction from the second, since
$\psi_{h+1}(c)=\psi_h(y_h)\psi_h(c)$.
Thus the prefix in question is a concatenation of at most two model factors and
at most two exceptional single letters. Empty pieces may be omitted.

Exclude starts $i<S$ whose length-$(q+1)$ context crosses a cut between these
pieces or contains an exceptional letter. There are at most three cuts and two
exceptional positions, so at most $3q+2(q+1)\le6(q+1)$ starts are excluded.
For each remaining model piece, extend that piece to a model word beginning with
it, and apply LA. A local start inside that piece corresponding to a global
start $i<S$ has local index less than $S$. Each of the at most two pieces
therefore contributes at most $\eta S$ additional bad starts. Since
$1\le q\le\eta S$, the complete bad set $E\subseteq[0,S)$ has

$$
|E|\le2\eta S+6(q+1)\le14\eta S\le16\eta S.                 \tag{2.4}
$$

At every other start, both $v_i=v_{i+q}$ and $\ell(v[i,i+q))=z$ hold.
This argument includes cuts through images of letters outside $B$.

Choose increasing occurrence positions $n\to\infty$ of $y[0,h)$ in $\Delta$.
For each such $n$, use (2.2) for the specified original word $w$.
The tail $v_n$ satisfies the finite template statement. Put

$$
A_n(i)=|\mu_n(v_n[0,i))|,\quad
p_n=\sum_{a\in A}|\mu_n(a)|z_a,\quad L_n=A_n(S)-j_n.
$$

At a good start $i$, the common vector gives
$A_n(i+q)-A_n(i)=p_n$. The equal letters at $i$ and $i+q$ then give agreement
of their entire image blocks at the single displacement $p_n$.
Consequently all mismatches between $w[0,L_n)$ and $w[p_n,p_n+L_n)$ lie in

$$
\bigcup_{i\in E_n}
\left( [A_n(i),A_n(i+1))\cap[j_n,A_n(S))\right)-j_n.          \tag{2.5}
$$

These are at most $S$ integer intervals with total length at most $M_n|E_n|$.
This is the common-vector image argument also used in [SS, Lemma 4.2]; the
finite template and bounded distortion here supply it without recurrence of
the original directive or equality of the original and model alphabets.

Using (2.1), $S\ge4C$, and (2.4), we obtain

$$
\begin{aligned}
p_n&\ge q m_n\longrightarrow\infty,\\
L_n&\ge m_n(S-C)\ge m_nS/2>0,\\
\frac{p_n}{L_n}&\le2C\eta,\\
\frac{M_n|E_n|}{L_n}&\le32C\eta\le\epsilon.
\end{aligned}                                                     \tag{2.6}
$$

Set $\delta=S$, padding (2.5) with empty intervals, and translate its coordinates
by one to positions $1,\ldots,L_n$. All of $\eta,q,S,z,h,\delta$ were fixed before
$n$ varies. Finally set

$$
r_n=-1,\qquad s_n=p_n-1,\qquad t_n=p_n+L_n-1.
$$

The compared words are exactly those of Definition 1.2. They satisfy
$-1\le r_n<s_n<t_n$, $s_n-r_n=p_n\to\infty$, and $t_n\ge\rho s_n$, since
(2.6) implies $L_n\ge(\rho-1)p_n$.
Thus $(*)_\rho$ holds for every $\rho>1$, proving the assertion. $\square$

## 3. The consumed endpoint and rigidity interface

**Proposition 3.1 (Auxiliary-model interface).** Let $y$ be a uniformly recurrent
strict directive on $B$, $d=|B|\ge2$. There exist finite constants $F$ and $R\ge1$
as in Definition 1.4. The following conditions are equivalent:

1. Some $w$ with $\mathcal L(w)=\mathcal L(c_y)$ has $\operatorname{Rdio}(w)=\infty$.
2. Every such $w$, with every intercept, has $\operatorname{Rdio}(w)=\infty$.
3. $(X_y^{\mathbb Z},T,\mu)$ is rigid.
4. $y$ has LA.
5. $\beta_{X_y}=0$.

Moreover $\beta_{X_y}/R\le\kappa\le R\beta_{X_y}$. If $\beta_{X_y}>0$, every
such one-sided word satisfies the finite bound

$$
\operatorname{Rdio}(w)\le1+\frac{F(d-1)R}{\beta_{X_y}}.       \tag{3.1}
$$

**Proof.** We first instantiate the suppliers on the primary language.
In [DZ, Theorem 2.2] the morphism $\tau_a$ is exactly $L_a$; the index sequence
is the directive of the palindromic-closure characteristic word. Thus
[DZ, Theorem 3.1] applies: bounded gaps of each letter of $y$ make the primary
shift linearly recurrent. It is minimal, uniquely ergodic and aperiodic, with
complexity $(d-1)n+1$, the strict Arnoux–Rauzy complexity.
The frequency comparison preceding [DMR, Theorem 6.3] supplies $R$ for this
linearly recurrent shift.

For the balance input note that [B, Theorems 1, 2] use right morphisms
$R_a(a)=a$, $R_a(b)=ba$ for $b\ne a$. This does give the same language here.
For each $h$ and $b\in B$,

$$
R_{y_0}\cdots R_{y_{h-1}}(b)
=\operatorname{rev}\bigl(\psi_h(b)\bigr).
$$

The $L$-image $\psi_h(b)$ is a primary factor as in the proof of Proposition 2.1, and the
primary language is closed under reversal [P, §3]. The right images of a fixed
letter are nested prefixes: adding the next right morphism either leaves that
image unchanged or appends another image. Their lengths tend to infinity.
Their limit therefore lies in the primary minimal subshift, and its language
is the whole primary language. Balancedness is a language property.
The bounded constant runs of $y$ are exactly bounded weak partial quotients in
[B]. Its Theorem 1 supplies a uniform factor-balance constant $F$; its Theorem 2
also supplies letter balance. No rigidity conclusion is imported from balance.

Write $f_a=\mu[a]$. By [BCB, Proposition 2.9], minimality, unique ergodicity and
letter balance give continuous real functions $g_a$ with
$\mathbf1_{[a]}-f_a=g_a\circ T-g_a$. For $G=(g_a)_{a\in B}$, telescoping gives

$$
\ell(x[0,q))-qf=G(T^q x)-G(x) \quad(x\in X_y^{\mathbb Z}).    \tag{3.2}
$$

Suppose first that $q_j\to\infty$ is a rigidity sequence. Let
$A_j=\{x:\|G(T^{q_j}x)-G(x)\|_\infty<1/4\}$.
Rigidity and Chebyshev's inequality give

$$
\mu(A_j^c)\le16\sum_{a\in B}\|g_a\circ T^{q_j}-g_a\|_2^2\longrightarrow0.
$$

For all large $j$, $A_j$ has positive measure. At any point of $A_j$, (3.2)
is an integer vector within $1/4$ of $q_jf$. There is at most one such integer
vector, since distinct integer vectors have sup-distance at least one.
Call it $z_j$; it is nonnegative and has coordinate sum $q_j$. At every point
of $A_j$ the Parikh vector is this same $z_j$. Consequently
$\mu\{x:\ell(x[0,q_j))\ne z_j\}\le\mu(A_j^c)\to0$.
This uses the high-measure conclusion, in addition to nonemptiness.
Also

$$
d_\mu(q_j)=\tfrac12\sum_{a\in B}
 \|\mathbf1_{[a]}\circ T^{q_j}-\mathbf1_{[a]}\|_2^2\longrightarrow0.
$$

Given $0<\eta<1$, fix one $q=q_j$ and $z=z_j$ for which the clopen set
$J=\{x:x_0\ne x_q\text{ or }\ell(x[0,q))\ne z\}$ has $\mu(J)<\eta/2$.
Unique ergodicity makes its time averages uniform: otherwise empirical measures
along longer and longer exceptional orbit segments would have an invariant
weak limit whose integral of the continuous function $\mathbf1_J$ differs from
$\mu(J)$, contradicting uniqueness. Thus every sufficiently large $S$, enlarged
so that $q\le\eta S$, gives LA. The estimate holds on all one-sided words by
the extension in Definition 1.1.

For clarity, factor balance also gives an explicit uniform bound for this step.
For any factor $U$ of length $k$ and any factor $W$ of length $M\ge k$, the
counts $N_U(W)$ have diameter at most $F$. Their invariant-measure average is
$(M-k+1)\mu[U]$. Every one of these counts therefore satisfies

$$
|N_U(W)-(M-k+1)\mu[U]|\le F.                                  \tag{3.3}
$$

Apply this with $k=q+1$ and $M=S+q$. Summing over the length-$(q+1)$ cylinders
defining $J$ gives
$|\sum_{i<S}\mathbf1_J(T^ix)-S\mu(J)|\le Fp_X(q+1)$.
Hence it suffices to take
$S\ge\max\{1,q/\eta,2Fp_X(q+1)/\eta\}$.

Conversely, integrate LA to get $d_\mu(q)\le\eta$ for its selected $q$.
These selected $q$ tend to infinity as $\eta\downarrow0$. Indeed, if
$d_\mu(q)=0$ for a fixed positive $q$, invariance implies $x_i=x_{i+q}$ for all
$i$ almost surely; full support then makes every point $q$-periodic, contrary
to aperiodicity. Thus each finite set of positive $q$ has a positive minimum
of $d_\mu(q)$. For a cylinder $C$ depending on a finite coordinate set $E$,

$$
\mu(C\mathbin\triangle T^{-q}C)\le |E|d_\mu(q).
$$

Cylinder indicators span a dense subspace of $L^2(\mu)$, and the Koopman
operators are isometries. This proves rigidity. The same cylinder argument
shows that $\kappa=0$ is equivalent to rigidity, without a balance hypothesis.

The endpoint comparison is the cylinder-frequency comparison of
[DMR, Lemma 6.4], used here quantitatively. Summing the frequencies of all
$p_X(n)$ equal-length cylinders and using $R$ gives

$$
\frac1{Rp_X(n)}\le\mu[U]\le\frac R{p_X(n)}.
$$

The endpoint-disagreeing length-$(q+1)$ cylinders partition
$\{x:x_0\ne x_q\}$. Hence

$$
\frac{b_X(q+1)}{Rp_X(q+1)}\le d_\mu(q)
 \le\frac{R b_X(q+1)}{p_X(q+1)}.                               \tag{3.4}
$$

Taking lower limits proves the stated inequalities for $\kappa$ and $\beta_X$,
and identifies conditions 3, 4 and 5. In particular no identification of
unweighted distinct-factor counts with sampled frequencies has been assumed.

To connect these conditions to refined repetition, let $W$ be a length-$(L+q)$
factor and $H$ the number of disagreements between $W[0,L)$ and $W[q,q+L)$.
Summing (3.3) over endpoint-disagreeing factors gives

$$
d_\mu(q)\le\frac HL+\frac{Fp_X(q+1)}L.                        \tag{3.5}
$$

For exact Nguyen witnesses to $(*)_\rho$, $\rho>1$, put
$q_k=s_k-r_k$ and $L_k=t_k-s_k$. Their interval cover implies
$H_k\le\epsilon L_k$ eventually. Since $r_k\ge-1$,
$s_k\ge q_k-1$ and $L_k\ge(\rho-1)(q_k-1)$. Their required period growth is
$q_k\to\infty$. By (3.5) and the exact complexity,

$$
\kappa\le\epsilon+\frac{F(d-1)}{\rho-1}.
$$

Condition $(*)_\rho$ holds for every $\epsilon>0$, so if $\kappa>0$, every
admissible $\rho>1$ satisfies $\rho\le1+F(d-1)/\kappa$.
Taking the supremum and then using $\kappa\ge\beta_X/R$ proves (3.1).
Only a necessary consequence of the interval cover is used for this upper bound.

Condition 1 now implies $\kappa=0$, hence condition 3. From condition 4,
Proposition 2.1 with $\Delta=y$ applies, since recurrence gives
$y\in\omega(y)$; it proves condition 2. Condition 2 implies condition 1.
All five conditions and the finite bound follow. $\square$

## 4. Consequences for the unchanged question

**Corollary 4.1 (At most three letters).** Every aperiodic episturmian word over
an alphabet of cardinality at most three has $\operatorname{Rdio}=\infty$,
for arbitrary directive and intercept.

**Proof.** First suppose the directive has unbounded constant runs.
The existing theorem [Repo, `not_boundedPQ_dio_top`] gives infinite ordinary
prefix exponent. Its definition `DioAdmissible` uses prefixes $UV^{\ell/|V|}$,
$V\ne\varepsilon$, of length $N=|U|+\ell$, with $N/(|U|+|V|)$ arbitrarily large.
To check the additional Nguyen period growth explicitly, fix $\rho\ge1$ and,
for each integer $j\ge1$, choose such a prefix with ratio at least $j(\rho+1)$.
Put $P=j|V|$. Then $|U|+P\le j(|U|+|V|)$, so
$N\ge(\rho+1)(|U|+P)$ and $\ell>P$. The periodic tail also has period $P$.
With $r=|U|-1$, $s=|U|+P-1$, $t=N-1$, the two compared words coincide,
$t\ge\rho s$, and $s-r=P\ge j\to\infty$. Thus Definition 1.2 holds with
$\delta=0$. This is the period-growth dictionary for the reused ordinary result.

Otherwise $\omega(\Delta)$ is nonempty and compact and contains a minimal
nonempty closed shift-invariant set $Y$: intersect chains of such sets and
apply compactness. Every $y\in Y$ is uniformly recurrent. Indeed, the inverse
shift translates of any cylinder meeting $Y$ cover $Y$ by minimality, and a
finite subcover bounds all hitting gaps. Let $B$ be its alphabet. The inherited
run bound excludes $|B|=1$, hence $2\le|B|\le3$.
For $|B|=2$ the primary Sturmian system has the irrational mechanical coding
$x_i(t)=\lfloor t+(i+1)\theta\rfloor-\lfloor t+i\theta\rfloor$
[P, §3 and §3.1]. Lebesgue measure pushes forward to its unique invariant measure.
Along integers $q_j\to\infty$ with $q_j\theta\to0$ modulo one, the measure of
letter mismatches tends to zero: disagreement requires crossing one of the two
coding boundaries. The cylinder argument in Proposition 3.1 gives rigidity.
For $|B|=3$, [BST, Theorem 3.8] applies: the directive is recurrent, contains
all three letters and has bounded weak partial quotients. It supplies a
measurable conjugacy to a toral translation, which is rigid by continuity of
translations in $L^2$. Its right-morphism language is the primary language by
the reversal correspondence in Proposition 3.1. Proposition 3.1 gives LA for
either model, and Proposition 2.1 transfers it to the original word. $\square$

**Corollary 4.2 (Exact remaining universal condition).** The assertion in
[N, Question 9.2], over all finite alphabets and all aperiodic episturmian words,
is equivalent to the following assertion:
for every $d\ge4$ and every nonperiodic uniformly recurrent strict directive
$y$ on $d$ letters, $\beta_{X_y}=0$. Equivalently, the remaining condition is

$$
\forall\zeta>0\ \forall N\ge1\ \exists n\ge N:\quad
b_{X_y}(n)<\zeta\bigl((d-1)n+1\bigr).                          \tag{4.1}
$$

**Proof.** We first justify excluding periodic directives using the stationary
supplier, including its symbolic-shift interface. Let $y=v^\infty$, where $v$
contains every letter of its alphabet. Put $\psi=L_v$ and $\chi=R_v$.
The primary word is fixed by $\psi$, and the primitive $\psi$ and $\chi$
languages agree by reversal as in Proposition 3.1. The incidence matrices of
$L_a$ and $R_a$ agree; their transposes are the fully subtractive generators
of [AD, Theorem 1]. Transposition reverses the period order, still leaving
every letter present, so that theorem gives primitivity and the Pisot property.
[Barge, Corollary 4.3] therefore applies to this arbitrary finite product of
right Arnoux–Rauzy substitutions, in every dimension. Its conclusion is pure
discrete spectrum for the geometric tiling flow.

Let $h_a>0$ be its Perron–Frobenius tile lengths. This flow is the suspension
over the primary symbolic shift with roof $r(x)=h_{x_0}$, as in [Barge, §2].
Using the continuous letter coboundaries already supplied inside Proposition 3.1,
put $c=\sum_a h_a f_a>0$ and $K=\sum_a h_a g_a$. Then
$r-c=K\circ T-K$. The map
$[x,s]_r\mapsto[x,s+K(x)]_c$ conjugates this suspension to the constant-roof
suspension: its seam identity is $r(x)+K(x)=c+K(Tx)$, and the inverse subtracts
$K(x)$. It preserves the invariant suspension probabilities by uniqueness.
The time-$c$ map of the latter suspension is $(x,s)\mapsto(Tx,s)$ almost
everywhere. Its closed reducing subspace of functions independent of $s$ is
$L^2(\mu)$. Pure discrete spectrum of the flow gives pure discrete spectrum
of this time map and of that reducing subspace. Thus the symbolic shift itself
has pure discrete spectrum; no arbitrary-roof implication has been used.

A countable eigenbasis now supplies rigidity: for its first $J$ unit-modulus
eigenvalues choose an arbitrarily large positive $q_J$ with their $q_J$-th
powers within $1/J$ of one. These returns exist in the compact closure of
the powers in a finite product of circles. Choose $q_J\ge J$; convergence on
finite eigenfunction spans and the isometry of the operators give strong
convergence on all $L^2$. Proposition 3.1 therefore gives $\beta_{X_y}=0$ for
every periodic strict directive, without a restriction on the period order.

Assume now (4.1) for every indicated nonperiodic model. For an arbitrary original
directive, the unbounded-run branch is exactly the zero-error argument in
Corollary 4.1. In the bounded-run branch choose the minimal omega-limit model
as there. Models on two or three letters are handled there; periodic models
of every alphabet size were handled above. Every other model is a nonperiodic
uniformly recurrent strict directive on at least four letters, so (4.1) and
Proposition 3.1 give LA. Proposition 2.1 then gives the exact refined witnesses
for every original intercept. Conversely, if Question 9.2 has a positive answer,
apply it to $c_y$ for any model in (4.1). Strictness on at least two letters
makes this word aperiodic; Proposition 3.1 forces $\beta_{X_y}=0$. $\square$

## 5. Mathematical boundary and references

**Boundary 5.1.** Condition (4.1) for every nonperiodic uniformly recurrent
strict directive on at least four letters remains an unpaid assertion here.
Neither an all-dimensional balance theorem nor a positive partial-rigidity rate
below one proves it. A counterexample through Proposition 3.1 requires an
actual such directive and constants $\zeta>0,N$ with
$b_X(n)\ge\zeta((d-1)n+1)$ for every $n\ge N$; it would give the finite bound
$1+F(d-1)R/\zeta$ for its actual episturmian words. No such directive or bound
is constructed here. The universal Question 9.2 is therefore unresolved.

The source-relative deductions in Propositions 2.1 and 3.1 combine the credited
suppliers below; they carry no assertion of worldwide priority. The coboundary consequence of balance, cylinder-frequency comparison,
stationary spectrum and the ordinary
unbounded-run theorem retain their own statements and hypotheses.

- [N] Q.-K. Nguyen, *Spectrum of the Refined Diophantine Exponent*,
  [arXiv:2608.20191v2](https://arxiv.org/pdf/2608.20191v2), Definitions 2.1, 2.3,
  2.5 and Question 9.2.
- [P] J. Peltomäki, *Initial nonrepetitive complexity of regular episturmian words
  and their Diophantine exponents*, [arXiv:2103.08351v3](https://arxiv.org/pdf/2103.08351v3),
  [doi:10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942), §3–3.1.
- [SS] J. Seo and W. Steiner, *Transcendence of dendric beta-expansions with pure
  discrete spectrum*, [arXiv:2610.00856v2](https://arxiv.org/pdf/2610.00856v2),
  Lemmas 4.1–4.2; their tiling and original-directive recurrence hypotheses are retained there.
- [BCB] V. Berthé and P. Cecchi Bernales, *Balancedness and coboundaries in symbolic
  systems*, [arXiv:1810.07453v1](https://arxiv.org/pdf/1810.07453v1), Proposition 2.9.
- [DZ] D. Damanik and L. Q. Zamboni, *Arnoux–Rauzy Subshifts: Linear Recurrence,
  Powers, and Palindromes*, [arXiv:math/0208137v1](https://arxiv.org/pdf/math/0208137v1),
  Theorems 2.2 and 3.1.
- [DMR] S. Donoso, A. Maass and T. Radić, *On partial rigidity of S-adic subshifts*,
  [arXiv:2312.12406v2](https://arxiv.org/pdf/2312.12406v2), Theorem 6.3, Lemma 6.4
  and the preceding frequency comparison. Their complete words have equal endpoints.
- [B] H. Bowley, *Uniform Factor-Balancedness in Arnoux–Rauzy Words*,
  [arXiv:2609.33919v2](https://arxiv.org/pdf/2609.33919v2), Theorems 1 and 2.
- [BST] V. Berthé, W. Steiner and J. M. Thuswaldner, *Geometry, dynamics, and
  arithmetic of S-adic shifts*, [arXiv:1410.0331v5](https://arxiv.org/pdf/1410.0331v5),
  [doi:10.5802/aif.3273](https://doi.org/10.5802/aif.3273), Theorem 3.8 (three letters).
- [Barge] M. Barge, *Pure discrete spectrum for a class of one-dimensional
  substitution tiling systems*, [arXiv:1403.7826v2](https://arxiv.org/pdf/1403.7826v2),
  §2 and Corollary 4.3 (the geometric flow).
- [AD] A. Avila and V. Delecroix, *Some monoids of Pisot matrices*,
  [arXiv:1506.03692v1](https://arxiv.org/pdf/1506.03692v1), Theorem 1.
- [Repo] The pinned primary definitions and ordinary-exponent and morphism-length
  suppliers are [MorphicDecomposition](https://github.com/the-omega-institute/trureturing/blob/bd817014953ec22f9433fdf40fb9f653beb8d1cd/D5/S1/Words/Episturmian/MorphicDecomposition.lean)
  and [BoundedPowers](https://github.com/the-omega-institute/trureturing/blob/bd817014953ec22f9433fdf40fb9f653beb8d1cd/D5/S1/Words/Episturmian/BoundedPowers.lean).

## 追加锚（本行以下为增补区）
