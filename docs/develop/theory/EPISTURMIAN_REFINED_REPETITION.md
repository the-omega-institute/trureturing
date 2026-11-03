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
is the whole primary language. This is also the right S-adic language: all its
generating images are primary factors, while every factor of the limit occurs
in one of its nested generating prefixes. Balancedness is a language property.
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

## 6. The actual finite-sheet model and its return foundation

**Definition 6.1 (Fixed geometry and physical labels).** Identify the model alphabet
with $B=\{0,\ldots,d-1\}$, $d\ge2$. For $H\ge d$ let $Y_H$ be the closed set
of directives for which every length-$H$ window contains every letter of $B$.
Unless a compact minimal hull is specified, fix a uniformly recurrent $y\in Y_H$.
Write $A_N=M_{L_{y_0}}\cdots M_{L_{y_{N-1}}}$, with incidence columns
$M_\sigma e_b=\ell(\sigma(b))$. Let $f=f_y$ be the normalized frequency vector,
and put

$$
\begin{gathered}
V=\{x\in\mathbb R^d:\mathbf1^{\mathsf T}x=0\},\qquad
\Lambda=V\cap\mathbb Z^d,\qquad K=V/\Lambda,\qquad p:V\longrightarrow K,\\
\pi_f(x)=x-(\mathbf1^{\mathsf T}x)f,\qquad
\alpha=p(\pi_f(e_{d-1})),\qquad C=4H2^H,\qquad M=(2C+1)^{d-1}.
\end{gathered}                                                     \tag{6.1}
$$

Use the same Lebesgue measure $\lambda$ on $V$ for all directives: $\Lambda$
has covolume one. Haar measure $du$ on $K$ is a probability. The actual BST
subtiles, with its positive-prefix convention, are

$$
\mathcal R_y(a)=\overline{\{\pi_f\ell(P):Pa\text{ is a prefix of a limit
word of }(L_{y_n})_{n\ge0}\}},\qquad
\mathcal R_y=\bigcup_a\mathcal R_y(a).                         \tag{6.2}
$$

The following instantiation supplies the objects used throughout §§7–10.
Every length-$H$ incidence product is positive: applying the morphisms from
right to left preserves every letter already present, and adds each directing
letter if it is absent. Each morphism at most doubles length, so its positive
product has entries between $1$ and $2^H$. Each $M_{L_a}$ is unimodular.
Its transpose is the fully subtractive generator of [AD, Theorem 1]. Transposing
a product reverses its order; every product of length at least $H$ still contains
every generator. That theorem therefore gives a primitive Pisot product.
Its characteristic polynomial is irreducible: if a monic integral proper factor
did not contain the simple dominant root, all its roots would have modulus
less than one, whereas its nonzero constant term is an integer. Thus the
sequence is primitive and algebraically irreducible in the sense of [BST].

This is the primary language of Definition 1.1. Each $L_{y[0,N)}(b)$ occurs in
$c_y=L_{y[0,N)}(c_{T^Ny})$, since the strict tail contains $b$; conversely the
growing prefixes $L_{y[0,N)}(y_N)$ of $c_y$ exhaust it. Consequently the generic
S-adic language of these actual left substitutions is exactly $\mathcal L(c_y)$,
as also identified by [P, §3.1] and [DZ, Theorem 2.2]. The generic [BST,
Theorem 3.1] is applied to this sequence itself. Its separate ternary
Theorem 3.8 uses right substitutions; the reversal argument in Proposition 3.1
is the language bridge for that earlier application, not a change of the
sequence in (6.2).

For the uniform balance input [DHS, equation (4), Lemmas 5–6] applies to exactly
these left substitutions. Its modified matrices have norm at most one and,
after the initial $H-1$ places, contract each length-$H$ block by at most

$$
\theta=\frac{2^H-d}{2^H-1}<1.
$$

Its Proposition 1 and Lemma 3 give, on every tail, discrepancy at most
$(H-1)+H/(1-\theta)\le H2^H-1$ and letter balance less than $C$.
In particular all the sets in (6.2), including every tail's subtiles in its
own fixed space $V$, lie in $[-C,C]^d\cap V$.
For every prefix length $\ell$, recurrence of $y$ gives a return position
$n\ge1$ with $y[n,n+\ell)=y[0,\ell)$; the language after $n+\ell$ has this
same balance bound. These are exactly the balanced-return hypotheses of
[BST, Theorem 3.1]. Its Lemma 5.9 supplies Property PRICE, including the
recurrent left vector; no assertion about a typical directive is needed.

Strong coincidence holds at the first substitution: all $L_{y_0}(b)$ begin
with $y_0$, and the prefixes before that common letter are empty. Hence
[BST, Theorem 3.1(ii)–(iv), Proposition 7.7 and Proposition 8.4] supplies compact
subtiles with null boundaries, disjointness in measure, the multiple tiling
$\{z+\mathcal R_y(a):z\in\Lambda,a\in B\}$, and the almost everywhere
bijective, measure-preserving exchange

$$
D_y(x)=x+\pi_f(e_a)=x+e_a-f\quad(x\in\mathcal R_y(a)).       \tag{6.3}
$$

This is BST's equation (8.1), with its sign unchanged. Reflecting all tiles by
$x\mapsto-x$ would replace the increment by $f-e_a$ and the base translation
by $-\alpha$; such a reflected representation is not used here.
Strong coincidence does not assert geometric coincidence or degree one.

Let $m=m_y$ be the multiple-tiling degree. Disjointness of the subtiles and
lattice disintegration give, for almost every $u\in K$,

$$
\begin{gathered}
S_y(u)=\mathcal R_y\cap p^{-1}(u),\qquad |S_y(u)|=m,\qquad
\lambda(\mathcal R_y)=m,\\
\int_{\mathcal R_y}\Phi(x)\,d\lambda(x)
 =\int_K\sum_{x\in S_y(u)}\Phi(x)\,du.                     \tag{6.4}
\end{gathered}
$$

Indeed one may integrate the lattice periodization over
$\{u\in V:0\le u_a<1\ (a<d-1)\}$, a fundamental domain of $\Lambda$.
In each fiber the first $d-1$ lattice coordinates range over intervals of
length $2C$, each containing at most $2C+1$ integers; the final coordinate is
determined by their sum. Thus $1\le m\le M$.
Order the physical points of $S_y(u)$ lexicographically as
$r_{1,y}(u),\ldots,r_{m,y}(u)$. These measurable sections do not depend on a
choice of base lift. Ordering their lattice offsets from any one lift gives
the same order, and translating a whole physical fiber preserves it.
Since $\pi_f(e_a)-\pi_f(e_{d-1})=e_a-e_{d-1}\in\Lambda$, (6.3) maps
$S_y(u)$ bijectively onto $S_y(u+\alpha)$. Define the actual permutation
$c_y:K\to\operatorname{Sym}(m)$ by

$$
D_y(r_{i,y}(u))=r_{c_y(u)i,y}(u+\alpha).                    \tag{6.5}
$$

The probability on the exchange is $\lambda|_{\mathcal R_y}/m$.
Equation (6.4) identifies it with Haar measure times uniform measure on the
$m$ labels; this is the measured skew product
$\widehat D_y(u,i)=(u+\alpha,c_y(u)i)$.
To relate it to the two-sided system, discard the invariant null set where
some forward or backward iterate of $D_y$ is undefined or ambiguous, and code
$x$ by its subtile labels at all $D_y^kx$, $k\in\mathbb Z$. Its finite factors
are those of the primary language. [BST, Lemma 8.3 and Proposition 8.4] makes
the future coding an almost everywhere bijective representation; invertibility
of $D_y$ then realizes its natural extension by these two-sided itineraries.
Their stationary law is the unique law $\mu_y$ on $X_y^{\mathbb Z}$.
Thus this is the actual two-sided primary shift, with actual physical sheet
labels, rather than an arbitrary extension of a rotation.

**Lemma 6.2 (Factorial amplification of actual returns).** In Definition 6.1 put
$E=M!$, and define

$$
\begin{aligned}
F_{q,y}(u)&=c_y(u+(q-1)\alpha)\cdots c_y(u),\qquad h=q\alpha,\\
\Omega_y(q)&=\sum_{r=1}^{E-1}\operatorname{Haar}
 \{u:F_{q,y}(u+rh)\ne F_{q,y}(u)\},\\
\omega_y(v)&=\frac1m\sum_{i=1}^m\operatorname{Haar}
 \{u:a_y(u+p(v),i)\ne a_y(u,i)\},
\end{aligned}                                                    \tag{6.6}
$$

where $a_y(u,i)$ is the subtile letter of $r_{i,y}(u)$.
Then $\omega_y(v)\to0$ as $v\to0$, and, for every $q\ge1$ and any lift
$\varepsilon_q\in V$ of $q\alpha$,

$$
d_{\mu_y}(Eq)\le\Omega_y(q)+\omega_y(E\varepsilon_q).       \tag{6.7}
$$

Moreover the primary shift is rigid if and only if there are $q_j\to\infty$
with $q_j\alpha\to0$ such that $F_{q_j,y}$ has a subsequence converging in
measure. Equivalently there are such returns with $\Omega_y(q_j)\to0$.

**Proof.** Translation continuity in $L^1(K)$ of the finitely many measurable
letter indicators proves the assertion about $\omega_y$.
Outside the union defining $\Omega_y(q)$, all $E$ factors in

$$
F_{Eq,y}(u)=F_{q,y}(u+(E-1)h)\cdots F_{q,y}(u)
$$

are the same permutation. Its order divides $m!$, hence $E$, so this product
is the identity. Consequently
$\operatorname{Haar}\{F_{Eq,y}\ne\mathrm{id}\}\le\Omega_y(q)$.
On the complement the label is unchanged, and only the base translates by
$Eq\alpha$. Comparing the actual letters and integrating the uniform sheets
gives (6.7). If its right side tends to zero at growing times, the cylinder
argument in Proposition 3.1 proves rigidity.

For completeness, suppose $h_j=q_j\alpha\to0$ and, after restriction to a
subsequence, $F_{q_j,y}\to P$ in measure. The limit takes values in
$\operatorname{Sym}(m)$. For each fixed $r$,

$$
\operatorname{Haar}\{F_{q_j,y}(\,\cdot+rh_j)\ne P\}
\le\operatorname{Haar}\{F_{q_j,y}\ne P\}
 +\operatorname{Haar}\{P(\,\cdot+rh_j)\ne P\}\longrightarrow0.
$$

The cocycle identity therefore gives $F_{Eq_j,y}\to P^E=\mathrm{id}$ in
measure. Together with $Eh_j\to0$, this proves strong convergence to the
identity first on continuous base functions times sheet indicators, then on
all $L^2$ by density and isometry. Conversely, rigidity makes every base
character return, hence $q_j\alpha\to0$. Applied to the sheet indicators it
makes the average moved fraction of labels tend to zero. A nonidentity
permutation moves at least one of the $m$ labels, so
$\operatorname{Haar}\{F_{q_j,y}\ne\mathrm{id}\}\to0$.
Each summand in $\Omega_y(q_j)$ is at most twice this measure, proving the
last equivalence. These arguments use the actual $F_{q,y}$ from (6.5).
A finite range alone gives no compactness in measure: the functions on
$[0,1)$ taking a fixed transposition or the identity according to the $j$-th
binary digit disagree on measure $1/2$ for distinct $j$. They are a boundary
on that compactness inference, not AR cocycles. $\square$

## 7. Joint geometric oscillation and actual Parikh charge

**Theorem 7.1 (Crossings and cancellation in the same exchange).** Use the actual
model of §6, and suppress $y$ on its objects. For $v\in V$ and $q\ge1$ put

$$
\begin{aligned}
G(v)&=\lambda(\mathcal R\mathbin\triangle(\mathcal R-v)),\\
W(v)&=\sum_a\lambda(\mathcal R(a)\mathbin\triangle(\mathcal R(a)-v)),\\
\Delta_q(v)&=\operatorname{Haar}\{u:F_q(u+p(v))\ne F_q(u)\},\\
H_{q,v}(x)&=D^q(x+v)-D^q(x)-v\quad(x\in\mathcal R\cap(\mathcal R-v)),\\
J(q,v)&=\lambda\{x\in\mathcal R\cap(\mathcal R-v):H_{q,v}(x)\ne0\}.
\end{aligned}                                                     \tag{7.1}
$$

Thus $J$ is a raw $\lambda$-mass, not a probability already divided by $m$.
Let $\iota(x)_k$ be the actual subtile letter of $D^kx$. Then

$$
\begin{gathered}
H_{q,v}(x)=\ell(\iota(x+v)[0,q))-\ell(\iota(x)[0,q))\in\Lambda,
\qquad \|H_{q,v}(x)\|_\infty\le2C+\|v\|_\infty.
\end{gathered}                                                     \tag{7.2}
$$

$$
\Delta_q(v)\le\frac{G(v)+qW(v)}2.                            \tag{7.3}
$$

$$
\frac{J(q,v)}m-G(v)\le\Delta_q(v)\le J(q,v)+G(v),\qquad
J(q,v)\le\frac{qW(v)}2.                                    \tag{7.4}
$$

For any lift $\varepsilon_q$ of $q\alpha$ this gives

$$
\Omega_y(q)\le\frac{E(E-1)}4
       \bigl(G(\varepsilon_q)+qW(\varepsilon_q)\bigr).        \tag{7.5}
$$

Along growing base returns with $\varepsilon_q\to0$, vanishing of $\Omega_y(q)$
is equivalent to vanishing of every $J(q,r\varepsilon_q)$, $1\le r<E$.
In particular $qW(\varepsilon_q)\to0$ is sufficient for rigidity. It is not
asserted necessary.

**Proof.** All statements are unaffected by the null boundary sets and their
iterates. For the initial fibers compare $S(u+p(v))-v$ with $S(u)$.
Lattice disintegration (6.4), used with their physical representatives, gives

$$
\int_K\#\bigl(S(u)\mathbin\triangle(S(u+p(v))-v)\bigr)\,du=G(v).
                                                               \tag{7.6}
$$

The two sets each have $m$ points almost everywhere. If unequal, their
symmetric difference has at least two points. Hence the initial exceptional
base set $A_v$, where they are unequal, has measure at most $G(v)/2$.
Off $A_v$ the lexicographic labels pair $r_i(u)$ with $r_i(u)+v$ exactly.
Translation preserves the physical order even when a chosen base lift crosses
a fundamental-domain boundary.

Set

$$
B_v=\bigcup_a\bigl(\mathcal R(a)\setminus(\mathcal R(a)-v)\bigr),
\qquad \lambda(B_v)=W(v)/2.                                  \tag{7.7}
$$

The equality follows from equal measures of a set and its translate and from
subtile disjointness in measure. Start with $u\notin A_v$. If none of its
$m$ trajectories visits $B_v$ in the first $q$ steps, the paired points stay
in the same subtile at each step. The translations (6.3) then keep their
difference equal to $v$. At time $q$ the images of all $m$ starting points
exhaust the two terminal fibers, so these terminal fibers themselves translate
exactly and their lexicographic labels match. Thus $F_q(u+p(v))=F_q(u)$.
For each $k$, (6.4) and preservation of $\lambda$ give

$$
\int_K\sum_{i=1}^m\mathbf1_{B_v}(D^kr_i(u))\,du
 =\lambda(B_v).
$$

A union bound over visits and sheets, together with the initial exception,
proves (7.3). In particular this sharper estimate needs no separate terminal
exception.

For the charge, telescope the two actual trajectories in (6.3). Their $-f$
terms cancel, leaving
$\sum_{k<q}(e_{\iota(x+v)_k}-e_{\iota(x)_k})$, exactly the difference of the
jointly realized Parikh vectors in (7.2). Its coordinate sum is zero. Both
terminal points belong to $[-C,C]^d$, giving the stated norm bound.
There is no independently optimized branch or independently chosen word in
this identity.

For comparison with $J$, exclude both $A_v$ and the bases with
$u+q\alpha\in A_v$. Their union has measure at most $G(v)$. On the remaining
bases, initial and terminal physical fibers both match by translation.
Consequently the number $N(u)$ of nonzero charges among the $m$ initial pairs
is exactly the number of labels on which $F_q(u+p(v))$ and $F_q(u)$ differ.
It is zero when these permutations agree and between $1$ and $m$ otherwise.
Let $J_{\rm good}$ be the integral of $N$ on these good bases, and let
$\Delta_{\rm good}$ be their permutation-disagreement measure. Then

$$
\Delta_{\rm good}\le J_{\rm good}\le m\Delta_{\rm good},\qquad
0\le J-J_{\rm good}\le mG(v),\qquad
0\le\Delta_q-\Delta_{\rm good}\le G(v).
$$

These inequalities prove the first two bounds in (7.4). This separate argument
has a terminal exception; using only its upper bound would lose the $G(v)/2$
constant in (7.3).
If a paired trajectory has nonzero charge, it has a first different subtile
assignment before time $q$. Before that time its two points differ by $v$;
at that time the first point belongs to $B_v$. The measure-preserving map
$D^k$ and a union bound on the initial points of $\mathcal R\cap(\mathcal R-v)$
therefore give $J(q,v)\le q\lambda(B_v)$, the last bound in (7.4).

Finally, translation invariance and the triangle inequality give
$G(rv)\le rG(v)$ and $W(rv)\le rW(v)$ for positive integers $r$.
Apply (7.3) at $r\varepsilon_q$ and sum $r=1,\ldots,E-1$ to obtain (7.5).
Both $G(v)$ and $W(v)$ tend to zero with $v$, by $L^1(V)$ translation
continuity. Since $E$ and $m$ are fixed, (7.4) proves the asserted equivalence
between vanishing oscillation and vanishing charge masses at returns.
Equations (7.5) and (6.7) prove the sufficient crossing criterion. $\square$

The finitely many possible charges for small $v$ do not determine their masses.
Many crossings can cancel to zero total charge. Null boundaries give
$W(v)\to0$, but give no rate coupled to $q$ and hence do not imply
$qW(\varepsilon_q)\to0$ along a growing return sequence.

## 8. Static continuity on an actual minimal directive hull

**Theorem 8.1 (Fixed-space hull continuity).** Fix a nonempty compact minimal
directive subshift $Y\subseteq Y_H$, with its product topology and shift $T$.
Use (6.1)–(6.5) for each $y\in Y$, always in the same $V,\Lambda,K,\lambda$.
Then $y\mapsto f_y$ is continuous, and every
$y\mapsto\mathcal R_y(a)$ is Hausdorff continuous. The integer $m_y$ is
constant on this $Y$, say $m$. Moreover

$$
\begin{gathered}
\lambda(\mathcal R_y(a))=mf_{y,a},\qquad
 y\longmapsto\mathbf1_{\mathcal R_y(a)}\text{ is continuous in }L^1(V,\lambda).
\end{gathered}                                                     \tag{8.1}
$$

$$
 y\longmapsto c_y\text{ is continuous in measure as a map into }
 L^0(K,\operatorname{Sym}(m)).                               \tag{8.2}
$$

$$
\lim_{s\downarrow0}\ \sup_{\substack{y\in Y\\v\in V,\ \|v\|_\infty\le s}}
 W_y(v)=0.                                                  \tag{8.3}
$$

The assertion concerns one fixed minimal hull. It makes no assertion that
different minimal subsets of $Y_H$ have the same degree.

**Proof.** Every point of a compact minimal directive subshift is uniformly
recurrent: finitely many inverse translates of any nonempty cylinder cover
$Y$, bounding its hitting gaps. Thus the hypotheses of §6 hold for all $y\in Y$.
The frequencies exist by §6. Their morphic relation is
$f_y=A_Nf_{T^Ny}/(\mathbf1^{\mathsf T}A_Nf_{T^Ny})$: count letters in
$c_y=L_{y[0,N)}(c_{T^Ny})$ and pass to frequencies. In particular writing
any tail frequency as the normalization of a positive length-$H$ product,
whose entries lie in $[1,2^H]$, applied to its next tail gives

$$
f_{T^Ny,a}\ge\frac1{d2^H}\quad(a\in B,\ N\ge0).           \tag{8.4}
$$

Here the lower bound follows from entries at least one and an upper bound
$d2^H$ for the sum after application to a normalized positive vector.

The contraction required for the subtiles must include the changing
projections. Put $g=f_{T^Ny}$ and $h_N=A_N^{\mathsf T}\mathbf1$, and define

$$
P_Nx=x-g\frac{h_N^{\mathsf T}x}{h_N^{\mathsf T}g}.
$$

Since $A_Ng=(h_N^{\mathsf T}g)f_y$, we have

$$
\pi_{f_y}A_N=A_NP_N,\qquad
 P_N\mathbb R^d\subset h_N^\perp=A_N^{-1}V,\qquad
 \|P_N\|_\infty\le1+d2^H.                                  \tag{8.5}
$$

The last bound uses (8.4) and positivity of $h_N$; the matrix norm is induced
by the coordinate sup norm. [DHS, equation (4), Lemmas 5–6] gives modified
products $\widetilde A_N$ agreeing with $A_N$ on this exact hyperplane
$A_N^{-1}V$, not on an unrelated fixed tail hyperplane. Their norms satisfy

$$
\|\widetilde A_N\|_\infty\le
 \theta^{\lfloor\max\{0,N-H+1\}/H\rfloor}=:\rho_N
 \longrightarrow0.
$$

Therefore (8.5) gives the uniform projected contraction

$$
\|\pi_{f_y}A_N\|_\infty\le(1+d2^H)\rho_N\longrightarrow0.  \tag{8.6}
$$

This also proves frequency continuity without a separate projective estimate.
If $z$ shares the first $N$ directive letters with $y$, write $g_z=f_{T^Nz}$.
Then $f_z=A_Ng_z/(h_N^{\mathsf T}g_z)$, where
$h_N^{\mathsf T}g_z\ge1$ because the morphisms are nonerasing. Consequently

$$
\|f_z-f_y\|_\infty
 =\frac{\|\pi_{f_y}A_Ng_z\|_\infty}{h_N^{\mathsf T}g_z}
 \le(1+d2^H)\rho_N\longrightarrow0.
$$

In [BST, Proposition 5.6] with initial hyperplane $V$, the level-$N$
hyperplane is $h_N^\perp$ and its projection is along $g$.
Its subtile is exactly $P_N\mathcal R_{T^Ny}(b)$: apply $P_N$ to the
prefix definition in the tail's fixed space $V$. Thus that proposition gives,
with the correctly transported projection,

$$
\mathcal R_y(a)=
 \bigcup_{\substack{b\in B,\ P,S\in B^*\\L_{y[0,N)}(b)=PaS}}
 \left(\pi_{f_y}\ell(P)+\pi_{f_y}A_N\mathcal R_{T^Ny}(b)\right).
                                                               \tag{8.7}
$$

Every tail subtile is nonempty and lies in the common box. Hence (8.6) puts
$\mathcal R_y(a)$ within Hausdorff distance
$\delta_N=C(1+d2^H)\rho_N\to0$ of the finite skeleton
$\{\pi_{f_y}\ell(P):L_{y[0,N)}(b)=PaS\}$.
First choose $N$ to make this error small. For directives sharing this
length-$N$ prefix the finite index set and its vectors $\ell(P)$ are fixed.
Only then choose a longer common prefix to make $f_z-f_y$ so small that
all these finitely many skeleton points are close; their displacement is
$-|P|(f_z-f_y)$. This proves Hausdorff continuity. In particular it does not
multiply a frequency-continuity estimate by an uncontrolled growing prefix
length. [BST, Proposition 5.12] supplies related convergence along PRICE
return subsequences on its transported hyperplanes; (8.4)–(8.7) supply the
additional uniform fixed-space argument needed here.

Let $z\to y$ in $Y$. Hausdorff convergence and common compact support put
$\mathcal R_z$ in every fixed outer neighborhood of $\mathcal R_y$ eventually.
The measures of those neighborhoods decrease to $\lambda(\mathcal R_y)$.
Since $m_z=\lambda(\mathcal R_z)$, this proves upper semicontinuity of the
bounded integer-valued degree. To establish its shift invariance one must
also identify the hyperplanes. Take a recurrent left vector $v$ for $y$.
[BST, Lemma 7.2] makes the multiple-tiling degree on every transported
$(v^{(N)})^\perp$ equal to the degree on $v^\perp$.
[BST, Proposition 7.5], applied both to the initial sequence and to each tail,
identifies these degrees with their respective degrees on $\mathbf1^\perp=V$.
Consequently $m_{T^Ny}=m_y$. Each nonempty closed superlevel set
$\{y:m_y\ge k\}$ is therefore forward invariant. Minimality makes it all of
$Y$, so $m_y$ is constant.

For volumes, [BST, Lemma 7.4] gives the vector of subtile measures as $m$
times the measures of the projected coordinate faces on the recurrent-left
hyperplane. Project along $f_y$ from that hyperplane to $V$; the same linear
Jacobian multiplies every component on both sides. Proposition 7.5 identifies
the $m$ on $V$. In the covolume-one normalization,
$\lambda(\pi_{f_y}[0,a])=f_{y,a}$. For example for $a=d-1$, in the first
$d-1$ coordinates the projected face has matrix
$I-f_{y,<d-1}\mathbf1^{\mathsf T}$ and determinant
$1-\sum_{a<d-1}f_{y,a}=f_{y,d-1}$; permuting coordinates gives every other
face, with the same lattice normalization. This proves the volume formula
in (8.1).
Hausdorff convergence implies
$\lambda(\mathcal R_z(a)\setminus\mathcal R_y(a))\to0$ by outer
neighborhoods. The now continuous volumes give the reverse difference as
well. This proves the asserted $L^1$ continuity and, by the finite union,
$L^1$ continuity of $\mathbf1_{\mathcal R_y}$.

It remains to compare the actual one-step labels. Disintegration excludes
source bases where $S_z(u)\ne S_y(u)$ with measure tending to zero, since
$\lambda(\mathcal R_z\mathbin\triangle\mathcal R_y)\to0$.
Exclude also bases having a common source point assigned to different letters;
their measure is at most
$\sum_a\lambda(\mathcal R_z(a)\mathbin\triangle\mathcal R_y(a))$, which
also tends to zero. For a remaining common point $x$ of letter $a$, put
$v=f_y-f_z$. Its images satisfy $D_zx=D_yx+v$, independently of $a$.
Their base points differ by $p(v)$, since $\alpha_z=\alpha_y+p(v)$.
The target-fiber comparison is therefore between
$S_z(u+\alpha_y+p(v))-v$ and $S_y(u+\alpha_y)$.
The integral of its cardinal symmetric difference is
$\lambda((\mathcal R_z-v)\mathbin\triangle\mathcal R_y)$, which tends to
zero by $L^1$ continuity and translation continuity. Outside this further
exception the source order is identical and the target order is identical
after translation by $v$. Hence $c_z(u)=c_y(u)$, proving (8.2) into the one
fixed $\operatorname{Sym}(m)$.

Finally the image of compact $Y$ under each indicator map in (8.1) is compact
in $L^1(V)$. A finite net and
$\|\tau_v f-f\|_1\le2\|f-g\|_1+\|\tau_v g-g\|_1$ make translation
continuity uniform on a compact $L^1$ family. Apply this to the finitely many
letters to obtain (8.3). $\square$

Uniform one-step continuity does not give precompactness of
$\{F_{q,y}:q\to\infty\}$, a common-time induction identity, or a rate for
$qW_y(\varepsilon_q)$. No such conclusion is used above.

## 9. Two applications with different mathematical roles

**Application 9.1 (An actual squarefree directive hull).** Let
$\vartheta(0)=01$, $\vartheta(1)=10$, and
$t=\lim_n\vartheta^n(0)$ be the Thue–Morse word. If
$i_0<i_1<\cdots$ are its positions carrying $1$, put
$a_j=i_{j+1}-i_j-1$. For every $d\ge4$, set $L=d-2$ and

$$
\chi(b)=3\,4\,\cdots\,(d-1)\,b\quad(b\in\{0,1,2\}),\qquad
 y=\chi(a_0a_1\cdots),\qquad H_0=32(d-2).                   \tag{9.1}
$$

Then $y$ is a uniformly recurrent, strict, squarefree, nonperiodic directive
in $Y_{H_0}$. Its compact orbit closure $Y$ is minimal and contained in
$Y_{H_0}$. Thus Theorem 8.1 applies to its actual subtiles and physical
one-step cocycles. The charge-return assertion (10.1) below remains unproved
for this hull.

Here are the combinatorial details needed for the application. The relations
$t_{2n}=t_n$ and $t_{2n+1}=1-t_n$ imply that an equal adjacent pair starts
only at an odd position. To prove overlap-freeness, suppose an overlap of
length $2p+1$ and period $p$ occurs, with $p$ minimal. If $p$ is odd, its
cyclic binary period has an equal adjacent pair, since an odd binary cycle
cannot alternate everywhere. The overlap repeats that pair at distance $p$,
contradicting the parity restriction. If $p$ is even and its starting position
$s$ is odd, shift the overlap one place left. The new equality needed is

$$
t_{s-1}=1-t_s=1-t_{s+p}=t_{s+p-1};
$$

all other period equalities come from the original overlap. Its start is now
even. The final even-position bit forces its following complementary bit,
so the overlap extends to complete $\vartheta$-pairs. Desubstitution yields
an overlap of length $p+1$ and period $p/2$, contradicting minimality.
Hence $t$ is overlap-free, in particular it has neither $000$ nor $111$.
Its one-gaps therefore belong to $\{0,1,2\}$.
If $a$ had a square of $k$ gap letters, the binary segment through the
corresponding $2k+1$ ones would be $VV1$, with $V$ beginning in $1$.
Writing $V=1U$ gives the overlap $1U1U1$. Thus $a$ is squarefree.

Each factor $W$ of $t$ lies in some $\vartheta^k(0)$; both
$\vartheta^{k+1}(0)$ and $\vartheta^{k+1}(1)$ contain that block. The aligned
block decomposition of $t$ bounds the gaps of $W$, proving uniform recurrence.
A finite factor of $a$ is specified by a binary factor beginning and ending
in $1$ with exactly those intervening zero runs. Recurrence of that binary
factor gives bounded gaps in the indices of ones and hence in $a$.
Furthermore $\vartheta^3(0)=01101001$ contains $11$, $101$, and $1001$.
Each aligned length-$16$ block $\vartheta^4(b)$ contains
$\vartheta^3(0)$, so each of these three patterns has an occurrence in every
such block. Their starting ones have gaps at most $32$ in binary positions,
and therefore at most $32$ in one-indices; a first such occurrence is within
the first $16$ one-indices. It follows that every length-$32$ window of $a$
contains all three gap letters.

The constant-length morphism $\chi$ preserves uniform recurrence: any
$y$-factor lies at a fixed offset in $\chi(A)$ for a finite $a$-factor $A$,
whose returns have bounded gaps. Every length-$32L$ window of $y$ contains
exactly $32$ consecutive variable letters and all marker letters, proving
membership in $Y_{H_0}$ and strictness. Each particular $y$-letter has one
fixed residue modulo $L$. A square of period $p$ would therefore force
$L\mid p$ by comparing its first letters. Taking its variable-letter
subsequence would give a square of period $p/L$ in $a$, a contradiction.
This also proves nonperiodicity. Since $L\ge2$, marker letters separate
variable letters; in particular $01$ never occurs, and no literal directive
square $vv$ occurs for any nonempty $v$.

These are exact exclusions of literal blocks. They do not exclude every
substitution-product forcing mechanism. Specifically [BST23, Lemma 5.6]
assumes a unimodular Pisot substitution $\tau$ with geometric coincidence,
Property PRICE for the directive, an equality
$\sigma_{[n,n+\ell)}=\tau^{m_\tau(C)}$, and a $C$-balanced tail after
$n+\ell$. Its equality is an equality of morphism products; squarefreeness
alone does not decide all such equalities. No value or sign of
$\beta_{X_y}$, and no AR nonrigidity conclusion, follows from the exclusions
in this application.

**Application 9.2 (A credited non-AR boundary).** The classical two-sheet system
of [FH, Definition 9] is

$$
\alpha=\frac{\sqrt5-1}2,\qquad\beta=\frac\alpha2,\qquad
 T_\mathrm V(x,s)=(x+\alpha\pmod1,\sigma(x)s),\qquad
 \sigma(x)=
 \begin{cases}(12),&0\le x<\beta,\\ \mathrm{id},&\beta\le x<1.
 \end{cases}                                                \tag{9.2}
$$

With Lebesgue measure times uniform measure on $\{1,2\}$ it is minimal,
linearly recurrent in its natural coding, uniquely ergodic, and nonrigid.
This gives a concrete boundary on a generic finite-extension argument;
it is not an episturmian example.

To instantiate the source, $\alpha$ is irrational with continued fraction
$[0;1,1,\ldots]$. Also $\beta\notin\mathbb Z+\mathbb Z\alpha$:
$\alpha/2=j+k\alpha$ would make $(1/2-k)\alpha$ an integer, contradicting
irrationality. Equality $\beta=1-\alpha$ would give $\alpha=2/3$, also
impossible. There is only one marked point, so there are no nontrivial
pair-difference exclusions left to check. The identity and the transposition
have no common nonempty proper invariant subset. Thus [FH, Proposition 4]
gives minimality. Their product inequality is satisfied as well:
$\sigma_1\ne\sigma_0$.

The marked rotation coding by $0,\beta,1-\alpha$ satisfies the precise linear
recurrence hypothesis. For nonzero integers $k$, choose a nearest integer
$l$ to $k\alpha$. With $\alpha'=-1-\alpha$,

$$
(k\alpha-l)(k\alpha'-l)=l^2+kl-k^2\in\mathbb Z\setminus\{0\},
\qquad |k\alpha'-l|\le4|k|,
$$

so $\|k\alpha\|_{\mathbb R/\mathbb Z}\ge1/(4|k|)$.
The second inequality follows from $0<\alpha<1$,
$|\alpha'|=1+\alpha<2$, and $|l|\le |k|\alpha+1/2\le3|k|/2$.
For a length-$n$ marked coding, all partition endpoints lie among
$-j\alpha$ and $\beta-j\alpha$ modulo one, $0\le j\le n$; this includes
the preimages of $1-\alpha$. Distinct endpoints within one family are
separated by at least $1/(4n)$. Between families the difference is
$(k+1/2)\alpha$, $|k|\le n$, and

$$
\|(k+1/2)\alpha\|\ge\tfrac12\|(2k+1)\alpha\|
 \ge\frac1{8(2n+1)}\ge\frac1{24n}\quad(n\ge1).             \tag{9.3}
$$

Every nonempty cylinder contains one of the resulting half-open partition
intervals, so its measure is at least $1/(24n)$. [FH, Proposition 3] therefore
gives linear recurrence of the marked base coding, and Proposition 10 gives
linear recurrence and unique ergodicity of the extension coding.
[FH, Theorem 15 and its immediately following linearly recurrent case]
now gives nonrigidity: the minimality conditions hold, $\alpha$ has bounded
partial quotients, and the marked coding is linearly recurrent with a marked
point different from $1-\alpha$.
Thus finite sheets, finitely many interval boundaries, a bounded-type rotation
and linear recurrence together do not force rigidity. The conclusion concerns
this non-AR comparison system only; it gives no AR endpoint lower bound and
no answer to Question 9.2.

## 10. The exact unpaid return assertion and the original witnesses

**Proposition 10.1 (Charge-return dictionary).** For each individual uniformly
recurrent $y\in Y_H$, with its actual objects from §§6–7, rigidity is equivalent
to the following assertion:

$$
\begin{aligned}
&\forall\eta>0\ \forall Q\ge1\ \exists q\in\mathbb N,\ q\ge Q,\quad
 \exists\varepsilon\in V:\\
&\hspace{12mm}p(\varepsilon)=q\alpha_y,\qquad
 \|\varepsilon\|_\infty<\eta,\qquad
 \sum_{r=1}^{E-1}J_y(q,r\varepsilon)<\eta.
\end{aligned}                                                     \tag{10.1}
$$

Here $Q$ is an integer and $E=M!$ depends on $d,H$, not on $q,Q,\eta$.
In particular, proving (10.1) for every nonperiodic uniformly recurrent
strict directive on every alphabet of size at least four would settle
Question 9.2 positively. Neither that universal assertion nor (10.1) for
the squarefree models of Application 9.1 is established here.

**Proof.** Diagonal choices in (10.1) give $q_j\to\infty$ and
$\varepsilon_j\to0$ with all its finitely many charge masses tending to zero.
By (7.4), $\Omega_y(q_j)\to0$; Lemma 6.2 gives rigidity.
Conversely rigidity gives growing returns with
$F_{q_j,y}\to\mathrm{id}$ in measure and $q_j\alpha_y\to0$.
Choose lifts $\varepsilon_j\to0$. Each
$\Delta_{q_j}(r\varepsilon_j)$ is at most
$2\operatorname{Haar}\{F_{q_j,y}\ne\mathrm{id}\}$, even though its
translation depends on $j$. Equation (7.4) gives

$$
J_y(q_j,r\varepsilon_j)\le
 m\bigl(\Delta_{q_j}(r\varepsilon_j)+G_y(r\varepsilon_j)\bigr)
 \longrightarrow0.
$$

A sufficiently late index meets any prescribed $\eta,Q$, proving (10.1).

To connect the universal version to the original directive, keep the exact
language definition $\mathcal L(w)=\mathcal L(c_\Delta)$ of Definition 1.1.
If the original directive has unbounded constant runs, the pinned ordinary
result and its period-growth dictionary in Corollary 4.1 already give the
required witnesses with zero errors. If its runs are bounded, the compact
minimal subset of $\omega(\Delta)$ used in Corollaries 4.1–4.2 supplies a
uniformly recurrent model $y$ strict on its actual alphabet $B$. Its letter
gaps have some finite bound $H$; these are hypotheses on the auxiliary model,
not on the original $\Delta$. Binary, ternary and periodic models retain the
suppliers and conclusions in those corollaries. For any remaining model,
(10.1) would give rigidity. The continuous letter coboundaries and uniform
time averages in Proposition 3.1 then supply a single joint Parikh vector
and LA, with exactly its uniformity over starts and intercepts.

In the notation of Proposition 2.1, write $C_0=D+2$ for the original bounded-run
length distortion, distinct from the geometric $C$ of (6.1). Its actual decoding
and finite-template argument supplies fixed $q,S,z$ and, at increasing
occurrence positions $n$, image periods $P_n$ and comparison lengths $L_n$
with

$$
\begin{gathered}
P_n\ge q\bigl(\lfloor n/D\rfloor+1\bigr)\longrightarrow\infty,
\qquad \frac{P_n}{L_n}\le2C_0\eta,\\
\text{all mismatches lie in at most }\delta=S\text{ intervals, of total
length at most }32C_0\eta L_n.                              \tag{10.2}
\end{gathered}
$$

For a given $\rho>1$ and $\epsilon>0$ choose the fixed alignment tolerance

$$
0<\eta\le\min\left\{\frac1{4C_0},\frac{\epsilon}{64C_0},
                         \frac1{4C_0(\rho+1)}\right\}.
$$

Then $r_n=-1$, $s_n=P_n-1$, $t_n=P_n+L_n-1$ give
$-1\le r_n<s_n<t_n$, $t_n\ge\rho s_n$, growing period
$s_n-r_n=P_n$, and the prescribed interval cover with total length
at most $\epsilon L_n$. All parameters including $\delta$ are fixed before
$n$ varies. The case $\rho=1$ follows from any $\rho>1$.
This invokes the actual intercept decoding and common-vector image argument
of Proposition 2.1; language equality alone is not used to transfer prefix
witnesses. It preserves every original directive and every original intercept.
Thus the claimed implication has the exact Nguyen quantifiers. $\square$

The universal conclusion remains the full Question 9.2. Conditions (4.1) and
(10.1) give equivalent remaining routes through the auxiliary models, with
no restriction added to that question. Theorem 8.1 supplies uniform static
translation continuity on each fixed minimal hull; Theorem 7.1 supplies a
sufficient small-crossing route and an exact actual-charge comparison.
Neither controls the growing-time charge masses in (10.1).
Finite sheets, bounded charges, balance, static compactness and a positive
partial-rigidity rate below one do not supply that missing conclusion.
The squarefree example gives no sign of its endpoint lower limit. An actual
negative answer would still require an actual episturmian model with the
uniform positive endpoint bound of Boundary 5.1, or equivalently positive
$\kappa$ in Proposition 3.1. Failure of a sufficient crossing estimate or
nonrigidity of the non-AR system (9.2) does not provide one.

The geometric representation, PRICE, contraction, face-volume identities and
the non-AR comparison retain their credited suppliers. The sheet bound,
factorial calculation, joint estimates and fixed-space continuity proof here
combine those inputs; no assertion of worldwide priority is made.
Additional sources used in §§6–9 are:

- [DHS] V. Delecroix, T. Hejda and W. Steiner, *Balancedness of Arnoux–Rauzy
  and Brun words*, [arXiv:1308.6694v1](https://arxiv.org/pdf/1308.6694v1),
  equation (4), Lemma 3, Proposition 1, Lemmas 5–6 and Theorem 1.
- [BST23] V. Berthé, W. Steiner and J. M. Thuswaldner, *Multidimensional
  continued fractions and symbolic codings of toral translations*,
  [arXiv:2005.13038v3](https://arxiv.org/pdf/2005.13038v3), Lemmas 5.4 and 5.6,
  with their exact substitution-product equality and balanced-tail hypotheses.
- [FH] S. Ferenczi and P. Hubert, *Rigidity of generalized Veech 1969/Sataev
  1975 extensions of rotations*, [arXiv:2010.01860v1](https://arxiv.org/pdf/2010.01860v1),
  Definition 9, Propositions 3, 4 and 10, and Theorem 15 with its following
  linearly recurrent specialization.
- [BST] in §5 is used here in its generic left-substitution scope:
  Theorem 3.1, Lemmas 4.1, 5.9, 7.2, 7.4 and 8.3, and Propositions 5.6,
  5.12, 7.5, 7.7 and 8.4. Its degree-one clauses retain their geometric
  coincidence hypothesis; its PRICE-return convergence is distinct from
  the full assertion of Theorem 8.1.

## 追加锚（本行以下为增补区）
