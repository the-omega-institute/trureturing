# AURIC FIB environment instruments and terminal record memory II

## 29. A finite obstruction to projective terminal task optimality

**Definition 29.1 (The actual channel and the projective-optimality assertion).**
This volume continues [Environment instruments and terminal record memory][ERM],
with the same qutrit source, actual chronological histories and terminal task
of Definition 27.1. Section numbers continue after that volume's §28.
Use its ordered orthonormal basis $(\xi,e,f)$ of $\mathbb C^3$ and its fixed matrices

$$
W=\operatorname{diag}(1,1,-1),\qquad
U_0=1\oplus\begin{pmatrix}-1/2&\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix},
\qquad
\Delta_W(X)=\frac{X+WXW}{2},\qquad
F=\operatorname{Ad}_{U_0}\circ\Delta_W.
\tag{29.1}
$$

Here $\operatorname{Ad}_U(X)=UXU^\dagger$. The actual fair independent chronological histories
are all discarded, so the terminal channel at horizon $n$ is exactly $F^n$.
In particular, the input and terminal output are both the same qutrit;
no five-dimensional transient channel is substituted for this restriction.
For every integer $n\ge2$ and every complex unit vector
$v=v_0\xi+v_1e$, put $E=|v\rangle\langle v|$ and retain the original loss

$$
\begin{aligned}
\eta_n(E)
&=\min_{\mathcal D\ {\rm CPTP}}
 \sup_{\rho\in\mathsf D(\mathbb C^3)}
 \left|\operatorname{Tr}\bigl(E\mathcal D(F^n(\rho))\bigr)
                         -\operatorname{Tr}(E\rho)\right|\\
&=\min_{0\le B\le I_3}\|(F^n)^\dagger(B)-E\|_{\rm op}.
\end{aligned}
\tag{29.2}
$$

The equality is the existing task/effect interface (27.4)–(27.5) of [ERM],
with the general calculation also given in [Purity arithmetic, (86.4)][PA]
and [the observable-correction note][BKKNOTE]. The decoder $\mathcal D$ may
depend on $E,n$ but is one input-independent CPTP map $M_3(\mathbb C)\to
M_3(\mathbb C)$ serving every qutrit input density. It has no chronological
record, source label or reference access, no smaller input code, no
intermediate correction and no postselection. The loss is the worst
absolute probability error of this prescribed binary task.

The projective-optimality assertion is

$$
\begin{gathered}
\text{for every integer }n\ge2\text{ and every }(v_0,v_1)\in\mathbb C^2,
\quad |v_0|^2+|v_1|^2=1,\\
\text{there exists }P\in M_3(\mathbb C),\quad P=P^\dagger=P^2,
\quad
\|(F^n)^\dagger(P)-|v\rangle\langle v|\|_{\rm op}
       =\eta_n(|v\rangle\langle v|),\quad v=v_0\xi+v_1e.
\end{gathered}
\tag{29.3}
$$

All four projection ranks are permitted, and $P$ need not commute with $W$.
The restriction is on the binary output effect itself, before pullback by
$F^n$. The general effect $B$ in (29.2) has no such idempotence restriction.

**Theorem 29.2 (A sixth-horizon trace obstruction).** For the fixed actual
channel (29.1), take

$$
n=6,\qquad v_*=\frac{\xi+e}{\sqrt2},\qquad
E_*=|v_*\rangle\langle v_*|
 =\begin{pmatrix}1/2&1/2&0\\1/2&1/2&0\\0&0&0\end{pmatrix}.
\tag{29.4}
$$

Then $\eta_6(E_*)\le1/2$, whereas every complex orthogonal projection
$P$ on the same qutrit, of any rank and without any commutation assumption,
satisfies

$$
\|(F^6)^\dagger(P)-E_*\|_{\rm op}>\frac12\ge\eta_6(E_*).
\tag{29.5}
$$

Consequently the universal assertion (29.3) is false.

Proof. First apply the existing interface (29.2) with its full input
and decoder domains. Its realization can be made explicit here without
adding a measurement resource to those permissions: for any effect $B$,

$$
\mathcal D_B(X)=\operatorname{Tr}(BX)E_*
             +\operatorname{Tr}((I_3-B)X)\frac{I_3-E_*}{2}.
\tag{29.6}
$$

This is the measure-and-prepare decoder (27.5), with output states $E_*$
and $(I_3-E_*)/2$. To check its CPTP property, write a spectral decomposition
$B=\sum_{j=1}^3b_j|u_j\rangle\langle u_j|$, where the $u_j$ are orthonormal
and $0\le b_j\le1$, and choose an orthonormal basis $w_1,w_2$ of $\ker E_*$.
Kraus operators for (29.6) are

$$
L_j=\sqrt{b_j}\,|v_*\rangle\langle u_j|,\qquad
M_{kj}=\sqrt{(1-b_j)/2}\,|w_k\rangle\langle u_j|
\quad(1\le j\le3,\ 1\le k\le2).
$$

Their adjoint products sum to $I_3$, and direct substitution gives
$\mathcal D_B^\dagger(E_*)=B$. Conversely every allowed decoder gives
an effect $B=\mathcal D^\dagger(E_*)$, since its adjoint is positive and
unital. For a Hermitian residual $A$, the spectral theorem gives
$\sup_{\rho\in\mathsf D(\mathbb C^3)}|\operatorname{Tr}(A\rho)|
=\max_j|\lambda_j(A)|=\|A\|_{\rm op}$: all expectations lie between
its extreme eigenvalues, and an eigenstate attains the largest absolute
value. Thus this comparison really includes every input and every allowed
decoder, as in the cited interface.

Since $F$ is trace preserving, its adjoint is unital. The permitted effect
$B=I_3/2$ therefore has residual $I_3/2-E_*$ at horizon six. This residual
has eigenvalues $-1/2,1/2,1/2$, so

$$
\eta_6(E_*)\le\|(F^6)^\dagger(I_3/2)-E_*\|_{\rm op}=\frac12.
\tag{29.7}
$$

The corresponding decoder (29.6) is a same-qutrit constant preparation,
$\mathcal D_{I_3/2}(X)=\operatorname{Tr}(X)
\bigl(E_*/2+(I_3-E_*)/4\bigr)$.
This only supplies an upper bound, not the exact unrestricted optimum.

Now let $P=P^\dagger=P^2$ be an arbitrary projection on $\mathbb C^3$.
Put

$$
Q=U_0^\dagger P U_0,\qquad
K=\Delta_W(Q)=K_2\oplus d,\qquad
K_2=\begin{pmatrix}x&z\\\overline z&y\end{pmatrix}.
\tag{29.8}
$$

Conjugation preserves the effect interval, and $\Delta_W$ averages two
unitary conjugations. Hence $0\le K\le I_3$, which gives

$$
0\le K_2\le I_2,\qquad 0\le d\le1,\qquad
0\le x,y\le1,\qquad |z|\le\frac12.
\tag{29.9}
$$

For the last inequality, the spectrum of $K_2-I_2/2$ lies in
$[-1/2,1/2]$, so its operator norm is at most $1/2$ and the modulus
of its off-diagonal matrix entry is at most that norm. In particular
$z$ is allowed to be any complex number satisfying the necessary effect
constraints; no reality or phase restriction has been placed on $P$.
Trace preservation of conjugation and pinching also gives

$$
x+y+d=\operatorname{Tr}K=\operatorname{Tr}P
       =m,\qquad m\in\{0,1,2,3\}.
\tag{29.10}
$$

There is no claim that $K$ is a projection. The facts retained from
projectivity are the effect inequalities and the integer trace of the
original $P$.

By (29.1), $F^\dagger=\Delta_W\circ\operatorname{Ad}_{U_0^\dagger}$,
so its first application to $P$ is exactly $K$. The calculation of
Proposition 27.2 of [ERM] then applies to each subsequent step. Explicitly,
on the block matrix in (29.8) one further step is

$$
(x,z,y,d)\longmapsto
\left(x,-\frac z2,\frac{y+3d}{4},\frac{3y+d}{4}\right).
\tag{29.11}
$$

This follows by multiplying the displayed $U_0$ on both sides and
pinching the $f$ cross entries. It fixes $x$ and $y+d$, and multiplies
both $z$ and $y-d$ by $-1/2$. There are five such steps after the
first, so $s=(-1/2)^5=-1/32$ and

$$
\begin{gathered}
C:=(F^6)^\dagger(P)=
 \begin{pmatrix}x&sz&0\\s\overline z&h&0\\0&0&g\end{pmatrix},\\
h=\frac{31y+33d}{64},\qquad
 g=\frac{33y+31d}{64},\qquad
 |g-h|=\frac{|y-d|}{32}\le\frac1{32},\\
\operatorname{Tr}C=x+h+g=x+y+d=m.
\end{gathered}
\tag{29.12}
$$

Thus the finite horizon, the signed coherence factor and both population
coefficients are fixed by the actual channel. In particular no
infinite-horizon limit or alternative channel enters this computation.

Suppose, for a contradiction, that $\|C-E_*\|_{\rm op}\le1/2$.
Write $b=sz-1/2$. The reverse triangle inequality and (29.9) give,
for complex $z$ as well as real $z$,

$$
|b|\ge\frac12-|s|\,|z|\ge\frac12-\frac1{64}
       =\frac{31}{64}.
\tag{29.13}
$$

The squared Euclidean norms of the $\xi$ and $e$ columns of $C-E_*$
are each at most $\|C-E_*\|_{\rm op}^2\le1/4$. Since $x,h$ are real,

$$
\begin{aligned}
(x-1/2)^2+|b|^2&\le\frac14,\\
(h-1/2)^2+|b|^2&\le\frac14,\\
(x-1/2)^2,\ (h-1/2)^2
 &\le\frac14-\left(\frac{31}{64}\right)^2
   =\frac{63}{4096}<\frac1{64}.
\end{aligned}
\tag{29.14}
$$

In particular $x,h\in[3/8,5/8]$. Combining this with the bound on
$|g-h|$ in (29.12) gives $g\in[11/32,21/32]$, and therefore

$$
\operatorname{Tr}C=x+h+g\in
\left[\frac{35}{32},\frac{61}{32}\right]\subset(1,2).
\tag{29.15}
$$

This contradicts (29.10)–(29.12), which make the same trace the integer
rank $m$ of $P$. The contradiction treats ranks zero through three at
once, without requiring $[P,W]=0$ or a projective lift of $K$.
Thus every allowed $P$ has error strictly greater than $1/2$.
Together with (29.7) this proves (29.5). Finally $6\ge2$ and
$v_*=(1,1,0)^{\mathsf T}/\sqrt2$ in the ordered basis is a complex unit
vector of the form required in (29.3). This single member of the
quantified family has no optimal projection, so it negates the universal
assertion without changing any of its quantifiers. $\square$

**Definition 29.3 (Measurement classes, suppliers and quantitative scope).**
The projection class in (29.3) consists of binary effects $P$ for which
$P=P^\dagger=P^2$ on $\mathbb C^3$. Measuring an arbitrary projective
measurement and then randomly assigning a binary answer is a larger
class: if its projections are $P_j$ and the answer-one probabilities are
$t_j\in[0,1]$, its binary effect is $\sum_jt_jP_j$, which need not be
idempotent. For example $t_j=1/2$ for every $j$ gives $I_3/2$ because
$\sum_jP_j=I_3$. This is precisely the comparison effect in (29.7).
Theorem 29.2 therefore does not exclude projective measurements with
such random postprocessing or extra outcomes, or projection dilations
on a larger space. A projection on a larger space is not a $P\in M_3$
in (29.3), and no dimension or ancillary-resource lower bound follows
from (29.5).

The fixed-channel and effect-iteration suppliers are [ERM, Definition 27.1
and Proposition 27.2, (27.1)–(27.7)][ERM]; the corresponding qutrit
restriction and iteration context are [Five-window quantum memory,
§§18–20, especially (19.4)][QM]. Only that $M_3$ restriction is used here.
Neither the full $M_5$ transient nor its reset or reference-entanglement
statements replace the channel or loss in (29.1)–(29.2).
The task/effect reduction and measure-and-prepare decoder are reused from
[ERM, (27.4)–(27.5)][ERM], [Purity arithmetic, Definitions 86.1/86.3
and (86.4)][PA], and [the existing note][BKKNOTE]. The record-conditioned
errors $1/4$ and $3/16$ from that source concern other channels and tasks;
no access to their retained record is supplied here.

Bény–Kempf–Kribs, *Quantum Error Correction of Observables*,
[DOI:10.1103/PhysRevA.76.042303][BKKDOI], Definition 8 and equation (7),
is the literature-attested Heisenberg observable-correction framework;
Theorem 9 and Corollary 10 concern exact correction of algebras. The
operator-norm reduction and positive effect lift used here have the
elementary scope stated in [BKKNOTE]. These suppliers are intermediates,
not an assertion by that paper of projective optimality for the finite
minimax problem (29.2). The repository-derived deduction in Theorem 29.2
is the finite trace obstruction for the actual matrices; no exhaustive
literature-novelty or priority assertion is attached to it.

The witness has task populations $p=q=1/2$ and $r=0$ in [ERM, (27.1)][ERM].
It belongs to the spectator–$e$ boundary of the complex task family.
At this boundary the relevant norm condition is [ERM, (27.28)][ERM],
not the interior Schur fractions in (27.27). The proof above uses direct
column-norm bounds and has no division by $r$ or by a vanishing horizon
parameter. It determines neither the exact $\eta_6(E_*)$ nor a minimizing
general effect, and it imposes no conclusion on the other vectors or
horizons in (29.3). The full quantitative optimization specified in
[ERM, Definition 27.10][ERM], including the $r=0,pq>0$ family and the
interior outside (27.24), is a separate problem. A common decoder for
several tasks and recovery uniform over unbounded horizons are also
outside the single-task finite-horizon conclusion (29.5).

[ERM]: AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md
[QM]: AURIC_FIB_FIVE_WINDOW_QUANTUM_MEMORY.md
[PA]: AURIC_FIB_ACTUAL_WORD_PURITY_ARITHMETIC.md
[BKKNOTE]: ../../../Library/Quantum/benykempfkribs2007observables.md#task-readout-statistical-sufficiency-and-physical-correction
[BKKDOI]: https://doi.org/10.1103/PhysRevA.76.042303

## 追加锚（本行以下为增补区）
