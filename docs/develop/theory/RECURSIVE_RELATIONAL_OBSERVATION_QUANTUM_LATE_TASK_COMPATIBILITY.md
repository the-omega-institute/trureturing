# Recursive relational observation: sharp common recovery of two late qutrit tasks

## 1. The original erased source and the common task

**Definition 1.1 (Source, access and scalar error).** All matrix spaces and
channels are complex. A channel is completely positive and trace preserving
(CPTP). On the whole source space $S=\mathbb C^3$, use the ordered orthonormal
basis

$$
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\qquad
e=(1,1,-2)^{\mathsf T}/\sqrt6,\qquad
f=(1,-1,0)^{\mathsf T}/\sqrt2.
$$

The matrices in this basis are

$$
W=\operatorname{diag}(1,1,-1),\qquad
U_0=1\oplus\begin{pmatrix}-1/2&\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix}.
$$

For every real $\theta$, the actual chronological contacts have operators
$V_0(\theta)=U_0e^{i\theta W}$ and $V_1(\theta)=V_0(\theta)W$, with fair
independent outcome labels. Their old outcomes are inaccessible and erased
from the observer's interface. Put

$$
\Delta_W(X)=\tfrac12(X+WXW),\qquad
F=\operatorname{Ad}_{U_0}\Delta_W,\qquad N_n=F^n\quad(n\ge0).
\tag{1.1}
$$

These are exactly the source, initialization and chronological erasure of
[Environment record memory, Definition 27.1 and (27.3)](AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md#27-quantitative-sharp-tasks-after-fair-chronological-history-erasure).
In particular, $N_0=\operatorname{id}$; the notation $s=0$ below instead
denotes the limiting channel. The identity $N_n=F^n$ holds at every real
$\theta$, without estimating $\theta$ from a transcript.

Define the three orthogonal output states and task projections by

$$
|+\rangle=(\xi+e)/\sqrt2,\quad
|-\rangle=(\xi-e)/\sqrt2,\quad |0\rangle=f,\qquad
E_r=|r\rangle\langle r|\quad(r\in\{+,-,0\}).
\tag{1.2}
$$

The late task belongs to $\{E_+,E_-\}$. Thus $E_+E_-=0$ and
$E_++E_-=I-E_0$, rather than $I$. A common decoder $D:M_3\to M_3$ is
chosen for $n$ and this pair before the unknown input and before the late
choice. Its two errors and its common optimum are

$$
e_j(D;n)=\|(F^n)^\dagger D^\dagger(E_j)-E_j\|_{\rm op},\qquad
t_n=\min_{D\ {\rm CPTP}}\max_{j\in\{+,-\}}e_j(D;n).
\tag{1.3}
$$

The unknown input ranges over every complex qutrit density matrix. An
arbitrary finite reference $R$ and an arbitrary density $\rho_{SR}$ may
be physically present, but $R$ is inaccessible. The scalar error on
$\rho_{SR}$ is the error on its marginal $\rho_S$; (1.3) is not a
reference trace-norm or diamond-norm objective. There is no smaller code,
intermediate correction, postselection, reset of $S$, old-history access
or reference access. The horizon, basis, contact law, alignment and
terminal access are authentic supplied data. Neither a task outcome nor
any formula below authenticates them.

**Definition 1.2 (Supplied effect coordinates).** For $n\ge1$ set

$$
s=(-1/2)^{n-1},\qquad a=(1+s)/2,\qquad b=(1-s)/2.
$$

On $W$-commuting Hermitian matrices put

$$
G_s\!\begin{pmatrix}x&z&0\\\overline z&y&0\\0&0&d\end{pmatrix}
=\begin{pmatrix}
x&sz&0\\s\overline z&ay+bd&0\\0&0&by+ad
\end{pmatrix}.
\tag{1.4}
$$

We use literally the entire-image formula of
[Environment record memory, Proposition 27.2, (27.6)–(27.7)](AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md#27-quantitative-sharp-tasks-after-fair-chronological-history-erasure):

$$
K=\Delta_W(U_0^\dagger B U_0),\qquad
(F^n)^\dagger(B)=G_s(K),\qquad B=U_0KU_0^\dagger
\tag{1.5}
$$

in the last equality when a $W$-commuting $K$ is prescribed. Both
directions preserve positivity and the identity. In particular they
preserve joint normalization of a family of effects, not merely each
individual effect interval. The coefficients $a,b$ are qutrit population
coefficients. They have no arithmetic-generator meaning.

## 2. Joint normalization and reduction of every complex decoder

**Lemma 2.1 (Exact common-effect formulation).** For every $n\ge1$,
$t_n$ is the minimum of

$$
\max_{j\in\{+,-\}}\|G_s(K_j)-E_j\|_{\rm op}
\tag{2.1}
$$

over $W$-commuting matrices $K_+,K_-,K_0\succeq0$ with
$K_++K_-+K_0=I$. Every such triple is realized by one actual common
qutrit decoder

$$
B_r=U_0K_rU_0^\dagger,\qquad
D(X)=\sum_{r\in\{+,-,0\}}\operatorname{Tr}(B_rX)E_r.
\tag{2.2}
$$

Proof. The adjoint of an arbitrary CPTP decoder is positive and unital.
Hence $D^\dagger(E_r)$ is a normalized positive triple. Applying the
positive unital map in (1.5) gives an admissible triple $K_r$ and exactly
its two errors in (2.1). Conversely, (1.5) makes the $B_r$ a POVM.
The measure-and-prepare channel (2.2) has $D^\dagger(E_r)=B_r$ for all
three $r$, so it realizes both desired effects simultaneously.

This is the Holevo-form supplier of
[Horodecki–Shor–Ruskai, equation (1) and Theorems 2 and 4](https://arxiv.org/html/quant-ph/0302031v2),
with their prepared states $R_r=E_r$ and their POVM elements $F_r=B_r$.
Equivalently, decomposing $B_r=\sum_\ell\lambda_{r\ell}
|v_{r\ell}\rangle\langle v_{r\ell}|$ gives the Kraus matrices
$\sqrt{\lambda_{r\ell}}|r\rangle\langle v_{r\ell}|$; their adjoint
products sum to $I$. No task-specific decoder is selected after $j$.
The feasible triples form a compact set and the loss is continuous, so
the minimum is attained. $\square$

**Lemma 2.2 (A two-variable minimum without a real-input restriction).**
For every $n\ge2$, put $\tau=|s|$, so $-1/2\le s\le1/4$.
The minimum in Lemma 2.1 equals

$$
\min_{0\le u\le1,\ 0\le d\le1/2}
\max\{k(u,d),\lambda(u,d)\},
\tag{2.3}
$$

where

$$
\begin{aligned}
k(u,d)&=bu^2/2+ad,\\
h(u,d)&=1/2-au^2/2-bd,\\
c(u)&=(1-\tau u)/2,\\
\lambda(u,d)&=\frac{h(u,d)+\sqrt{h(u,d)^2+4c(u)^2}}2.
\end{aligned}
\tag{2.4}
$$

For $s\ne0$ an admissible triple giving this loss is

$$
K_\pm=
\begin{pmatrix}1/2&\pm\operatorname{sgn}(s)u/2\\
\pm\operatorname{sgn}(s)u/2&u^2/2\end{pmatrix}\oplus d,
\qquad K_0=\operatorname{diag}(0,1-u^2,1-2d).
\tag{2.5}
$$

At $s=0$ either sign of the off-diagonal entries in (2.5) is allowed.

Proof. Start with any complex triple in Lemma 2.1. Entrywise conjugation
preserves positivity, normalization and the loss, because (1.4) and the
targets have real coefficients. Averaging the triple with its conjugate
cannot increase the loss, by convexity of the norm. Set
$J=\operatorname{diag}(1,-1,1)$. Conjugation by $J$ commutes with $G_s$
and exchanges $E_+,E_-$. Average once more with the triple obtained by
this conjugation and exchange of the two labels. The resulting pair is

$$
K_\pm=\begin{pmatrix}x&\pm z\\\pm z&y\end{pmatrix}\oplus d,
\qquad
0\le x,y,d\le1/2,\quad z\in\mathbb R,\quad z^2\le xy.
\tag{2.6}
$$

Conversely these inequalities give a positive normalized triple, since
$K_0=\operatorname{diag}(1-2x,1-2y,1-2d)$. The errors of its two
members are equal. For the plus task the target-minus-image residual is

$$
\begin{pmatrix}
1/2-x&1/2-sz\\1/2-sz&1/2-ay-bd
\end{pmatrix}\oplus(-(by+ad)).
\tag{2.7}
$$

Both diagonal entries of its upper block are nonnegative. Its trace is
therefore nonnegative, so the upper block's operator norm is its larger
eigenvalue. That eigenvalue is nondecreasing in each diagonal entry and
in the absolute off-diagonal entry. Here $|z|\le1/2$ and $\tau\le1/2$,
so $1/2-sz$ is positive. Replacing $z$ by
$\operatorname{sgn}(s)|z|$, when $s\ne0$, cannot increase the loss.
Next increase $x$ to $1/2$ and increase $|z|$ to $\sqrt{y/2}$.
The new triple is feasible, the first diagonal residual decreases and
the off-diagonal residual does not increase; the other terms are fixed.
Writing $y=u^2/2$ gives (2.4)–(2.5). At $s=0$ the coherence term is
independent of $z$. This proves (2.3).

The averaging is over admissible effect triples, not over input states.
The starting decoder and its input domain were completely complex, so
the reduction proves lower bounds for every complex common CPTP
decoder. $\square$

## 3. The sharp odd-horizon value

**Theorem 3.1 (Odd finite horizons).** For every odd integer $n\ge3$,
let $s=(-1/2)^{n-1}\in(0,1/4]$ and use Definition 1.2. Then

$$
t_n=T=\frac b4\bigl(1+\sqrt{9+8s}\bigr),\qquad
d_*=(T-b/2)/a.
\tag{3.1}
$$

The inequalities are

$$
0<d_*<1/2,\qquad b<T<1/2.
\tag{3.2}
$$

An attaining common triple is

$$
K_\pm=\begin{pmatrix}1/2&\pm1/2\\\pm1/2&1/2\end{pmatrix}
\oplus d_*,\qquad
K_0=\operatorname{diag}(0,0,1-2d_*).
\tag{3.3}
$$

Proof. The number in (3.1) is the positive root of

$$
q(t)=t^2-(b/2)t-ab^2=0,
\tag{3.4}
$$

because $1+16a=9+8s$. Since $s>0$, its radical is greater than $3$,
and hence $T>b$. Moreover

$$
q(1/2)=a(1/4-b^2)>0.
$$

The other root of $q$ is negative; consequently $T<1/2$. These bounds
give $0<(T-b/2)/a<1/2$.

For the lower bound, use Lemma 2.2. Suppose its loss is $t<T$ at some
$(u,d)$, and put $y=u^2/2$. In particular $by+ad\le t$. Since
$a^2-b^2=s>0$ and $y\le1/2$,

$$
ay+bd\le (b/a)t+(s/a)y\le(b/a)t+s/(2a).
$$

Thus, for the entries of (2.4),

$$
h\ge\frac ba(1/2-t)>0,\qquad c\ge(1-s)/2=b.
\tag{3.5}
$$

The inequality $\lambda\le t$ says that
$tI_2-\left(\begin{smallmatrix}0&c\\c&h\end{smallmatrix}\right)$
is positive semidefinite, so $t(t-h)\ge c^2$. Using (3.5) gives
$q(t)\ge0$, which is impossible for $0\le t<T$. This bounds all the
complex decoders of Definition 1.1.

For (3.3), take $u=1,d=d_*$. Its scalar error is $k=T$ and its upper
residual has entries

$$
\begin{pmatrix}0&b\\b&h_*\end{pmatrix},\qquad
h_*=\frac ba(1/2-T)>0.
\tag{3.6}
$$

Equation (3.4) is exactly $T(T-h_*)=b^2$. Therefore the larger
eigenvalue is $T$. The other eigenvalue is $h_*-T$, whose absolute
value is smaller than $T$. The common loss is exactly $T$, and
Lemma 2.1 provides one common attaining decoder. $\square$

## 4. The sharp even-horizon value

**Theorem 4.1 (Even finite horizons).** For every even integer $n\ge2$,
write $\tau=-s\in(0,1/2]$, $a=(1-\tau)/2$ and $b=(1+\tau)/2$.
There is exactly one $u_*\in(0,1)$ with

$$
P(u_*):=bu_*^4+(a-\tau^2)u_*^2+2\tau u_*-1=0.
\tag{4.1}
$$

Then

$$
t_n=T=(a+bu_*^2)/2,\qquad a<T<1/2.
\tag{4.2}
$$

An attaining common triple is

$$
K_\pm=
\begin{pmatrix}1/2&\mp u_*/2\\\mp u_*/2&u_*^2/2\end{pmatrix}
\oplus1/2,\qquad K_0=\operatorname{diag}(0,1-u_*^2,0).
\tag{4.3}
$$

Proof. Since
$a-\tau^2=(1-2\tau)(1+\tau)/2\ge0$, the polynomial $P$ is strictly
increasing on $[0,1]$. Its endpoint values are $P(0)=-1$ and
$P(1)=2\tau-\tau^2>0$, proving existence and uniqueness. Put
$r=\sqrt{a/b}$. Direct substitution, using $a+b=1$ and $b-a=\tau$,
gives

$$
bP(r)=\tau\bigl(2\sqrt{ab}-1-a(1+\tau)\bigr)<0.
\tag{4.4}
$$

Here $2\sqrt{ab}\le1$ and $a>0$. Thus

$$
u_*>\sqrt{a/b}\ge1/\sqrt3>1/2,
\qquad a<T<1/2.
\tag{4.5}
$$

At $u=u_*,d=1/2$, the quantities in (2.4) are

$$
k=T,\qquad h_* = a(1-u_*^2)/2>0,\qquad
c_*=(1-\tau u_*)/2>0,\qquad T-h_*=u_*^2/2.
\tag{4.6}
$$

Equation (4.1) is precisely $T(T-h_*)=c_*^2$. As in Theorem 3.1,
the upper residual has larger eigenvalue $T$ and a second eigenvalue
of absolute value smaller than $T$. This proves the attained upper
bound with the normalized triple (4.3).

For the lower bound let $u,d$ be arbitrary in (2.3), and set
$y=u^2/2$, $y_*=u_*^2/2$. Suppose its loss is strictly less than $T$.
Then $by+ad<T$, and $T$ is strictly larger than the larger eigenvalue
of the upper residual. Its characteristic determinant consequently
satisfies

$$
\begin{aligned}
0<Q(y,d)
&:=T^2-T/2+Tay+Tbd
  -\bigl(1/2-\tau\sqrt{y/2}\bigr)^2.
\end{aligned}
\tag{4.7}
$$

If $0\le y\le y_*$, use $d\le1/2$. The function $Q(y,1/2)$ is
strictly increasing in $y$: its linear term has positive slope, and
the positive quantity $1/2-\tau\sqrt{y/2}$ decreases. Therefore

$$
Q(y,d)\le Q(y_*,1/2)=0,
$$

where the equality follows from (4.6). This contradicts (4.7).

If $y\ge y_*$, the scalar budget gives $d\le(T-by)/a$. Consequently

$$
Q(y,d)\le R(u):=
\frac{T^2}{a}-\frac T2-\frac{T\tau u^2}{2a}
-\frac{(1-\tau u)^2}{4}.
\tag{4.8}
$$

For $u\ge u_*$, (4.5) yields

$$
R'(u)=\frac\tau2\bigl(1-(2T/a+\tau)u\bigr)<0.
\tag{4.9}
$$

Indeed $T>a$ and $u\ge u_*>1/2$. Since
$T=by_*+a/2$, substitution at $u_*$ gives
$R(u_*)=Q(y_*,1/2)=0$. Again (4.7) is impossible. These two cases
exhaust (2.3), hence every complex common decoder has loss at least
$T$. $\square$

## 5. Strict individual regret and the minimum finite witness size

**Definition 5.1 (The supplied individual minima).** Write

$$
m_n=\eta_n(E_+)=\eta_n(E_-).
\tag{5.1}
$$

The exact value $\eta_n(E_+)$, including the exceptional horizons two
and three, is supplied by
[Environment record memory II, Definition 30.2 and Theorem 30.3](AURIC_FIB_ENVIRONMENT_RECORD_MEMORY_II.md#30-exact-balanced-task-errors-at-every-finite-horizon).
Their parameters are exactly the present $s,a,b,\tau$ and their task is
$E_+$. For $n\ge4$, their value is the unique root in
$((1-\tau)/2,1/2)$ of

$$
\tau^4m^4+2\tau^2(1-\tau^2)m^3+(1-\tau^2)^2m^2-m+1/4=0.
\tag{5.2}
$$

For $n=2,3$, $m_n$ means exactly their respective isolated degree-eight
branch and formula (30.10); no limiting or quartic substitution is made
at those two horizons. Equality of the two values in (5.1) follows
also directly from $K\mapsto JKJ$: this operation exchanges the two
targets and commutes with $G_s$. This argument uses the attainable-effect
covariance of (1.4), not a claimed covariance of the chronological
instrument itself. The supplied individual decoder is allowed to depend
on its single task. A common decoder in (1.3) is not.

**Theorem 5.2 (A strict gap at every later finite horizon).** For every
integer $n\ge2$,

$$
m_n<t_n,\qquad
\min_{D\ {\rm CPTP}}\max_{j\in\{+,-\}}
\bigl(e_j(D;n)-m_n\bigr)=t_n-m_n>0.
\tag{5.3}
$$

Two is the globally minimum cardinality of a finite family of tasks
with no common individual-optimum decoder at that horizon. This is a
minimum over families in the original model, not just over subsets of
one chosen triple.

Proof. We show that the plus effect of each displayed common attainer can be
strictly improved when it is used for that task alone. The individual
effect interface is precisely (27.4)–(27.5) of Environment record memory;
every effect used in this argument has a legal task-specific decoder.

First let $n\ge3$ be odd, and write $T=t_n$, $d=d_*$ and $h=h_*$ as
in Theorem 3.1. For small $\varepsilon>0$, the single-task matrix

$$
K(\varepsilon)=
\begin{pmatrix}
1/2+\varepsilon&\sqrt{1/4-\varepsilon^2}\\
\sqrt{1/4-\varepsilon^2}&1/2-\varepsilon
\end{pmatrix}\oplus d
\tag{5.4}
$$

is an effect: its upper block is a rank-one projection. Its scalar
error is $T-b\varepsilon$. At $\varepsilon=0$ its upper residual is
(3.6), with simple positive eigenvalue $T$ and eigenvector proportional
to $(b/T,1)$. Differentiating the explicit two-by-two eigenvalue formula
shows that the derivative of this eigenvalue is

$$
\frac{a-b^2/T^2}{1+b^2/T^2}<0.
\tag{5.5}
$$

To verify the sign without a numerical estimate, use
$b^2=T(T-h)$ and $h=b(1/2-T)/a$. They give

$$
a-b^2/T^2=\frac{b\{1/2-(1+a)T\}}{aT}<0,
$$

since $T>b\ge3/8$ and $1+a>3/2$. The other upper eigenvalue has
absolute value strictly below $T$ at zero and retains this strict
inequality for sufficiently small $\varepsilon$. Both active errors
therefore become strictly smaller than $T$.

Next let $n\ge2$ be even, and use $u=u_*,T,h_*,c_*$ from Theorem 4.1.
Put $\kappa=u^2/(4bT)>0$ and take

$$
K(\varepsilon)=
\begin{pmatrix}1/2+\varepsilon&-u/2\\-u/2&u^2/2\end{pmatrix}
\oplus(1/2-\kappa\varepsilon).
\tag{5.6}
$$

This is an effect for sufficiently small positive $\varepsilon$.
In fact its upper determinant is $\varepsilon u^2/2>0$, while
the determinant of its upper complement is
$(1-u^2)/2-\varepsilon(1-u^2/2)>0$; all diagonal constraints and the
scalar constraint remain strict where needed. The scalar error is
$T-a\kappa\varepsilon$. The upper residual has diagonal entries
$-\varepsilon,h_*+b\kappa\varepsilon$ and off-diagonal entry $c_*$.
Its positive eigenvalue has derivative at zero

$$
\frac{-c_*^2/T^2+b\kappa}{1+c_*^2/T^2}<0,
\tag{5.7}
$$

because (4.6) gives $c_*^2/T^2=u^2/(2T)$ and
$b\kappa=u^2/(4T)$. Again $h_*>0$ makes the other upper eigenvalue's
absolute value strictly smaller than $T$ at zero. Continuity now gives
a single-task effect with error strictly below $T$.

In both parity cases these are ordinary effects on the full qutrit,
not necessarily members of a feasible common pair. Thus their strict
improvements imply $m_n<T$. Conjugation by $J$ supplies the same
conclusion for the minus task. We use the supplied exact values of
Definition 5.1; no new individual optimum is being inferred from the
perturbations.

Since both individual minima equal $m_n$, subtracting that same constant
from (1.3) proves the equality in (5.3). A singleton task always has an
individual attainer: the finite-dimensional CPTP Choi set is compact
and each fixed task's norm loss is continuous. Hence no singleton
witnesses failure of simultaneous
individual optimality, whereas the present pair does. This proves the
global cardinality assertion. The compact-decoder interpretation of
this regret is also the supplied budget-slack framework of
[Erased terminal recovery II, §§162–164](AURIC_FIB_ACTUAL_ERASED_HISTORY_TERMINAL_RECOVERY_II.md#162-budgeted-tasks-on-the-original-recovered-channel),
with task budgets both equal to $m_n$; the new input here is its sharp
source-specific two-task value. $\square$

## 6. Empty, first and limiting horizons

**Theorem 6.1 (Endpoints and loss of the pair obstruction).** One has
$t_0=t_1=0$. At the limiting member $s=0$, the common optimum for this
pair and its two individual optima are all $1/2$. Consequently this pair
is a finite-horizon incompatibility witness at every $n\ge2$, and is
not an incompatibility witness at $s=0$. Its finite regrets satisfy
$0<t_n-m_n\le2|s|$ and tend to zero as $n\to\infty$.

Proof. At $n=0$ use $D=\operatorname{id}$. At $n=1$ use
$D=\operatorname{Ad}_{U_0^\dagger}$: then $DF=\Delta_W$, which fixes
both $E_+,E_-$. Nonnegativity of the loss proves both zero values.

At $s=0$, every $G_0(K)$ has zero $\xi,e$ off-diagonal entry. The
corresponding entry of either target has magnitude $1/2$. Since
$|\langle\xi,H e\rangle|\le\|H\|_{\rm op}$, each individual loss
is at least $1/2$. On the other hand the common triple

$$
K_\pm=\begin{pmatrix}1/2&\pm1/2\\\pm1/2&1/2\end{pmatrix}\oplus1/2,
\qquad K_0=0
\tag{6.1}
$$

is normalized and positive, and $G_0(K_\pm)=I_3/2$.
Both errors are exactly $1/2$.

For every block effect $0\le K\le I_3$, its entries in (1.4) satisfy
$|z|\le1/2$ and $|y-d|\le1$. The first bound follows by applying the
matrix-entry norm bound to $K-I_3/2$, whose norm is at most $1/2$.
Decomposing $G_s(K)-G_0(K)$ into its off-diagonal part and its diagonal
part now gives

$$
\|G_s(K)-G_0(K)\|_{\rm op}
\le |s|\bigl(|z|+|y-d|/2\bigr)\le|s|.
\tag{6.2}
$$

The feasible individual effects and normalized common triples do not
depend on $s$. Thus the triangle inequality, followed by the minimum
in either optimization, bounds the change of each optimum from its
zero-parameter value by $|s|$. Hence $|t_n-1/2|\le|s|$,
$|m_n-1/2|\le|s|$, and (5.3) gives the claimed regret bound and limit.

This result leaves unchanged the different limiting triple
$\{P_0,P_2,Q\}$ of
[Erased terminal recovery, §§103–104](AURIC_FIB_ACTUAL_ERASED_HISTORY_TERMINAL_RECOVERY.md#103-rank-one-task-optima-and-a-common-decoder).
Its basis identification is $|0\rangle=\xi$, $|1\rangle=e$,
$|2\rangle=f$, and $Q=|(\xi+f)/\sqrt2\rangle
\langle(\xi+f)/\sqrt2|$. That triple retains its positive regret
bound at $s=0$ and its own inclusion-minimality. The present pair uses
the spectator–$e$ plane, rather than that triple's erased spectator–$f$
coherence task, and supplies no assertion that all limiting pairs are
compatible. $\square$

## 7. One acquired run, its retained use and its simultaneous resources

**Definition 7.1 (Exact description and installation interface).** Fix
$n\ge2$ and a finite number $k\ge1$ of later task calls. A run has one
unknown source input $\rho_{SR}$, the actual $n$ contacts of Definition
1.1, one application of the already chosen decoder (2.2), and $k$
successive supplied choices in $\{+,-\}$. A choice requests the complete
binary projective instrument with projections $E_j,I-E_j$ on the
decoded qutrit. Its outcome and supplied choice are both retained if
the complete call transcript is retained. All those continuations are
specified here; no other quantum action is represented by them.
The errors (1.3) concern each fixed task on the unconditioned input.
An adaptive continuation identity is not an error bound for a target
selected after conditioning on earlier answers.

For exact descriptions, integers and rationals are written in binary;
positive radicals and a real polynomial with a rational isolating
interval specify algebraic numbers. Arithmetic work and traffic mean
elementary binary work and bit transfers. Source contact, installation,
decoder application and projective read are separate charged primitive
calls. The mathematical decoder interface permits the displayed finite
CPTP maps. A physical installer for their exact coefficients, its
duration, workspace, traffic, control and backing are additional supplied
resources. Physical exact-device installation is
`ASSUMED-UNVERIFIED`; an algebraic description does not establish it.
No finite digital description of an arbitrary real $\theta$ is assumed:
the actual contact device is supplied, and the decoder coefficients do
not depend on $\theta$.

**Proposition 7.2 (Five explicit decoder amplitudes).** For the attaining
decoder at every $n\ge2$ there are exactly five displayed rank-one Kraus
matrices, with no spectral search. Define $w_\pm,c,r,v$ by

$$
\begin{array}{c|c|c|c|c}
 &w_\pm&c&r&v\\\hline
n\text{ odd}&|\pm\rangle&d_*&1-2d_*&f\\
n\text{ even}&(\xi\mp u_*e)/\sqrt2&1/2&1-u_*^2&e
\end{array}
\tag{7.1}
$$

Then $K_j=|w_j\rangle\langle w_j|+c|f\rangle\langle f|$
for $j=+,-$ and $K_0=r|v\rangle\langle v|$. The Kraus matrices are

$$
L_{j,1}=|j\rangle\langle U_0w_j|,\qquad
L_{j,2}=\sqrt c\,|j\rangle\langle U_0f|\quad(j=+,-),
\qquad L_0=\sqrt r\,|0\rangle\langle U_0v|.
\tag{7.2}
$$

They obey $\sum_\ell L_\ell^\dagger L_\ell=I_3$ and give precisely
(2.2). Thus a five-dimensional decoder environment suffices for a
Stinespring isometry, on this same source qutrit.

Proof. Equations (3.3) and (4.3) give (7.1) directly. The adjoint Gram
matrices in (7.2) sum to $\sum_rB_r=I_3$, and their action prepares
exactly $E_r$ with weight $\operatorname{Tr}(B_rX)$. Therefore
$V_D\psi=\sum_\ell L_\ell\psi\otimes|\ell\rangle$ is an isometry
into $S\otimes\mathbb C^5$. The source register is used as the decoded
output; a second unknown qutrit is not supplied.

The finite Kraus/isometry implication is the standard channel
representation of [Watrous, Theorems 2.22, 2.26 and Corollary 2.27](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf).
Here its input and output dimensions are both three and its particular
environment has dimension five, as verified by (7.2), rather than by a
minimal-environment assertion. The repository's corresponding
[FiniteKrausRepresentation](../../../D5/S3/Quantum/Foundation/FiniteKrausRepresentation.lean)
and its owning
[Scribe](../../../Blueprint/D5/S3/Quantum/Foundation/FiniteKrausRepresentation.scribe.cs)
supply general finite complex Kraus representations; they do not supply
the two-task minimax or a physical installer. $\square$

**Theorem 7.3 (Actual acquisition and continued legal use on one run).**
Under Definition 7.1's exact mathematical interface, the decoder attains
$t_n$ on the one terminal qutrit acquired after the actual $n$ contacts,
for every $\rho_{SR}$ and every real $\theta$. It may write one new trit
$r\in\{+,-,0\}$ into an observer record $C$, without obtaining an old
history or a reference. After ignoring decoder scratch, the actual joint
state has the form

$$
\sum_{r\in\{+,-,0\}} E_r\otimes|r\rangle\langle r|_C
\otimes\sigma_r,
\qquad \sigma_r\succeq0,\quad\sum_r\operatorname{Tr}\sigma_r=1.
\tag{7.3}
$$

The last factor contains the inaccessible reference and any inaccessible
old source backing retained in the realization. The trit is a record
of this decoder's outcome; it is not a record of $\rho$, $\theta$, an old
word or authentic class membership. For any finite sequence of the
declared task calls, each answer is $1_{\{r=j\}}$, and the conditional
decoded state remains $E_r$. The trit and the decoded qutrit determine
the same complete law and successors for this continuation language.
Acquiring the trit from the decoded qutrit alone takes at most two of
the declared binary reads. These are counted as reads if that acquisition
is performed; they are not an inverse of the original unknown state.

Proof. Let $\omega$ be the terminal joint state on $S$ and all untouched
factors. It is produced on this very run by the actual chronological
instrument, whose $S,R$ marginal is
$(F^n\otimes\operatorname{id}_R)(\rho_{SR})$. Apply (7.2) locally.
Coherently copy the coarse label $r$ of its five Kraus indices into a
fresh three-state record $C$, and ignore the five-state environment.
The resulting state is (7.3), where explicitly

$$
\sigma_r=\operatorname{Tr}_S
\bigl[(\sqrt{B_r}\otimes I)\omega(\sqrt{B_r}\otimes I)\bigr].
\tag{7.4}
$$

The rank-one prepared factors in (7.2), and partial-trace cyclicity on
$S$, prove this equality even when $\omega$ has arbitrary correlations.
No independence of $\sigma_r$ from $r$ is asserted. Ignoring $C$ gives
exactly $D$ on $S$, so the scalar performance is exactly Theorems 3.1
and 4.1. The label copy uses only decoder scratch; it never copies an
unknown source state. It is an explicit instance of the finite
record-isometry supplier in
[Compatible predictive waves, Theorem 7.2 and its multiple-Kraus extension](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md#7-预测波怎样给出概率与观察者的记录增长).

For either $j$ and each $r$, the complete binary instrument acts as

$$
E_jE_rE_j=1_{\{r=j\}}E_r,\qquad
(I-E_j)E_r(I-E_j)=1_{\{r\ne j\}}E_r.
\tag{7.5}
$$

Consequently every legal call has the deterministic answer stated in
the theorem when $r$ is given, and leaves the same $E_r$ and the same
untouched conditional factor. Induction proves the full finite-call
law, including adaptive choices based on previous answers. The same
choices are legal on both representations at every step. Conversely,
the two legal reads $j=+$ followed by $j=-$ recover $r$ with certainty:
the yes answer identifies its corresponding sign, and two no answers
identify zero. Equation (7.5) proves that these reads preserve each
$E_r$. No additional three-outcome measurement permission is required.
Thus the two routes agree on their declared diagonal
continuation language. This concerns the decoded process only; it is
not a state-recovery identity for the original unknown input. $\square$

**Theorem 7.4 (Finite exact widths and a simultaneous resource bound).**
For every supplied $n\ge2$, the effects and the five Kraus matrices in
Theorems 3.1, 4.1 and Proposition 7.2 have exact algebraic descriptions
of $O(n)$ bits. Their coefficients have algebraic degree at most $32$
over $\mathbb Q$. There is a description construction using $O(n^2)$
binary work and bit traffic and $O(n)$ simultaneous arithmetic storage.
These bounds describe coefficients, not physical installation.

For every finite $k\ge1$ and reference dimension $d_R$, one mathematical
realization of Theorem 7.3 has, simultaneously, the following factors:

$$
\begin{array}{c|c|c}
\text{factor}&\text{dimension or binary width}&\text{access}\\\hline
S&3&\text{source, then decoded output}\\
R&d_R&\text{untouched and inaccessible}\\
H&2^n&\text{inaccessible old chronological labels}\\
Z&2^n&\text{inaccessible backing of those labels}\\
A&5&\text{decoder environment, subsequently ignored}\\
C&3&\text{one newly retained decoder trit}\\
\text{choice and answer transcript}&2k\text{ bits}&\text{observer records}\\
\text{contact and call counters}&O(\log(n+2)+\log(k+2))\text{ bits}
 &\text{observer control}\\
\text{exact coefficient backing}&O(n)\text{ bits}&\text{observer settings}\\
\text{arithmetic scratch and phase control}&O(n)+O(1)\text{ bits}
 &\text{observer control}
\end{array}
\tag{7.6}
$$

In addition, the actual source device, installer, choice-producing
selector, permissions, control descriptions and their backing have
their supplied resource costs; they are not assigned zero
by this table. With their costs kept as separate coordinates, the run
uses $n$ source-contact calls, one installation, one decoder call, $k$
late choices and $k$ complete binary reads. Local binary work and traffic
are $O(n^2+k\log(k+2))$ in addition to those primitive costs. The
six Hilbert-space factors $S,R,H,Z,A,C$ in (7.6) have joint dimension
$45\,4^n d_R$. This is an attained bound for this realization, with
coexisting factors, not a resource optimum or a horizon-independent
physical-space bound.

Proof. Put $q=2^{n-1}$. It has exactly $n$ binary digits, and
$s=\pm1/q$, $a=(q\pm1)/(2q)$, $b=(q\mp1)/(2q)$. The rational
parameters have $O(n)$-bit numerators and denominators. In the odd case,
(3.1) uses one positive square root and rational operations. In the
even case, multiply (4.1) by $2q^2$ to obtain the integer polynomial

$$
q(q+1)u^4+\{q(q-1)-2\}u^2+4qu-2q^2=0.
\tag{7.7}
$$

Its coefficients have at most $2n+O(1)$ bits. The interval $(0,1)$
isolates its unique root by Theorem 4.1, so it is a complete real
algebraic specification without an approximation table. Expressions
for $T,d_*,w_\pm,c,r$ then have fixed length apart from these binary
coefficients. The fixed basis introduces only $\sqrt2,\sqrt3$.
In the odd case the field degree is at most two before adjoining
$\sqrt c,\sqrt r$, and at most $2\cdot2\cdot2\cdot4=32$ after also
adjoining $\sqrt2,\sqrt3$. In the even case the root degree is at most
four; $\sqrt c=1/\sqrt2$, and adjoining $\sqrt r,\sqrt2,\sqrt3$ gives
degree at most $4\cdot2\cdot4=32$. Every matrix coefficient in (7.2)
belongs to these fields.

One may form $q$ by $n-1$ successive binary doublings, followed by a
fixed number of additions, multiplications and assignments of the
displayed algebraic specifications. Summing the widths during the
doublings and using schoolbook multiplication for the fixed number
of products bounds binary work and traffic by $O(n^2)$ and scratch
by $O(n)$. This is a finite exact description argument; no precision
claim about a numerical root approximation is used. The explicitly
materialized denominator $q$ and polynomial coefficients have growing
width. A compressed expression for $q$ is a different representation,
so this growth is not claimed as a representation-independent lower
bound.

For the source factors, let $h=(h_1,\ldots,h_n)$ and
$V_h=V_{h_n}\cdots V_{h_1}$. The isometry

$$
J_n\psi=2^{-n/2}\sum_{h\in\{0,1\}^n}
V_h\psi\otimes|h\rangle_H\otimes|h\rangle_Z
\tag{7.8}
$$

has $J_n^\dagger J_n=I$. Ignoring $Z$ gives the actual classical
chronological instrument with labels $h$ and weights $2^{-n}$;
ignoring $H$ too gives exactly $F^n$. It is also the product of the
$n$ chronological contact isometries with fresh label and backing
bits, so no source-history enumeration is an operation of the observer.
Equation (7.8) specifies a chosen coherent extension of the prescribed
actual branches. The erased channel does not certify that an unknown
device has this particular backing or these cross-history phases.
An actual device with different backing retains its own backing-cost
coordinate; none of the decoder bounds uses access to that backing.
Both old factors in this realization are inaccessible throughout. Apply the five-state
decoder isometry with the coarse trit copy from Theorem 7.3 to this
same $S$, leaving $R,H,Z$ untouched. Their joint dimensions multiply
to $3d_R2^n2^n5\cdot3=45\,4^n d_R$. There is no second copy of
the source, and arbitrary initial correlations with $R$ are retained
as actual joint states in this construction.

Allocate the coefficient backing, scratch, counters and records in
(7.6) on this run. Keeping them all through the final cut proves the
simultaneous bound without adding mutually exclusive peak allocations.
Authentic $n$ permits a contact counter of logarithmic width; it does
not permit an unknown duration to be inferred from $C$. The $k$ supplied
choices and their $k$ answers take $2k$ retained bits; copying and
incrementing the corresponding counters costs
$O(k\log(k+2))$ work and traffic. A finite controller also records
whether the run is configuring, contacting, decoding or serving calls.
All arithmetic and retained-record widths, and all the primitive calls
listed in the statement, therefore coexist in one realization.

Source hardware and its control of the stipulated real $\theta$,
alignment, the right to receive $S$, the right to use the decoder and
the late readout, and the installer's workspace, traffic, duration and
backing remain explicit supplied coordinates. Producing the supplied
choices has its own selector and backing costs, even when that selector
uses previous answers; the $k$ choice receipts do not construct it.
Their numerical costs
are not proved by finite Hilbert dimension. The original mathematical
CPTP interface permits (7.2); a finite exact gate synthesis over a
separately fixed physical gate alphabet is not a consequence. No
source probe, calibration sample or additional preparation of the
unknown input has been used. $\square$

## 8. Exact boundaries of the recovered information

**Proposition 8.1 (The two tasks do not determine a complete quantum
future).** At every finite $n\ge2$, the displayed optimal decoder and
its retained trit give identical accessible states for the two inputs

$$
\rho_\pm=|y_\pm\rangle\langle y_\pm|,\qquad
|y_\pm\rangle=(\xi\pm i e)/\sqrt2.
\tag{8.1}
$$

The input projection $Y=\rho_+$ has probabilities one and zero on
these inputs. Thus no procedure using only the decoded qutrit and this
trit can recover that additional input task exactly, and its worst
scalar error for that task is at least $1/2$.

Proof. Every $G_s(K_r)$ in (3.3) or (4.3), including $r=0$, is real
symmetric. The difference $\rho_+-\rho_-$ has purely imaginary
off-diagonal entries and zero diagonal, so its trace pairing with
each $G_s(K_r)$ vanishes. By (1.5), the complete accessible joint
state $\sum_r\operatorname{Tr}(G_s(K_r)\rho)E_r\otimes
|r\rangle\langle r|$ is identical on the two inputs. Any permitted
subsequent procedure receives identical states, whereas the desired
answers are one and zero. If its common output probability is $p$,
then $\max\{|1-p|,|p|\}\ge1/2$. This supplies an actual complex-state
information loss, rather than an inference from the absence of a
reconstruction formula. $\square$

**Definition 8.2 (Independent domains and supplier correspondence).**
The space in this manuscript is the specified complex qutrit factor
and its supplied tensor interfaces; time is the actual chronological
contact index; the access boundary is the terminal qutrit with old
labels and references excluded; retained memory is the new trit and,
when retained, the complete later choice/answer transcript. Their
meanings precede the recovery statements. Theorem 7.3 proves only the
record–decoded-state equivalence and successor compatibility for its
specified diagonal task language. It does not make any of these views
an unrestricted copy of a history or recover chronology from one trit.

The fixed-source result added to the individual suppliers is the exact
jointly normalized two-task threshold, its attained common decoder and
the global minimum finite incompatibility-witness size. The general
exact-observable framework in
[Bény–Kempf–Kribs, Definition 8, equation (7), and Theorem 9](https://arxiv.org/html/0705.1574v1)
has code projection $P=I_3$ here. Its single recovery channel for an
observable set, and its algebraic zero-error criterion for an observable
algebra, are intermediate frameworks; they do not give the nonzero
individual-optimum or common minimax values (3.1), (4.2), (5.3).
The positivity and principal-compression facts used in the proofs are
also the standard finite-matrix facts in the pinned upstream
[Matrix.PosSemidef](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/PosDef.lean).
All the new bounds were proved with the actual matrices and normalization,
rather than supplied by a general Kraus theorem.

[Sharp task retained environment memory, Theorem 24.1](RECURSIVE_RELATIONAL_OBSERVATION_SHARP_TASK_RETAINED_ENVIRONMENT_MEMORY.md#24-global-linear-stability-after-erasing-only-the-first-acquisition-label)
instead quantifies over maps $T:M_3\to M_5$, actual full-space acquisition
effects, and a retained second label after erasing only the first label.
Its nine-effect defect controls a full complex-matrix diamond norm.
Here the original histories are all erased, the decoder is $M_3\to M_3$,
and two scalar task errors are optimized. Neither map, output interface,
effect list nor norm is identified across these two statements.
[Compatible predictive waves, §§7 and 12](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md#7-预测波怎样给出概率与观察者的记录增长)
supplies the general record-isometry and growing-reference interfaces
used in §7, including the need to specify actual coherent backing if
future access permits it. Its five-mode conditional model does not
replace (1.1) or supply this pair's minimax value.

An unknown-law acquisition problem would require an additional procedure
to acquire and certify the law and alignment from its own allowed data;
none is an input to or consequence of (1.3). A reference-stable state
recovery problem would require a different norm and the corresponding
joint-output estimate. General task families would require all their
joint effect constraints. Recovering physical space, a common four-view
source, or a universal alpha/beta generator would require their own
initialization, acquisition, complete ports, rights, references and
continuation bridges. No such additional hypothesis is inferred from
finite contact counts, an algebraic coefficient description, the trit,
or the pair's attained scalar performance.

## 追加锚（本行以下为增补区）
