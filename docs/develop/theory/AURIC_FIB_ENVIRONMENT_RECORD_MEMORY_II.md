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

## 30. Exact balanced-task errors at every finite horizon

**Definition 30.1 (Balanced task, complex domains and reused suppliers).**
Use exactly the ordered orthonormal basis $(\xi,e,f)$, the matrices
$W,U_0$, the pinching $\Delta_W$ and the actual channel
$F=\operatorname{Ad}_{U_0}\circ\Delta_W$ of (29.1).
The actual fair independent chronological histories of [ERM, Definition
27.1 and (27.1)–(27.3)][ERM] are entirely erased. At every real instrument
angle their terminal qutrit channel is this same $F^n$. Fix only

$$
v_*=(\xi+e)/\sqrt2,\qquad
E_*=|v_*\rangle\langle v_*|
 =\begin{pmatrix}1/2&1/2&0\\1/2&1/2&0\\0&0&0\end{pmatrix}.
\tag{30.1}
$$

For each finite integer $n\ge2$ retain the full optimization

$$
\eta_n(E_*)=
\min_{\substack{\mathcal D:M_3(\mathbb C)\to M_3(\mathbb C)\\
                 \mathcal D\ {\rm CPTP}}}
\sup_{\rho\in\mathsf D(\mathbb C^3)}
\left|\operatorname{Tr}\bigl(E_*\mathcal D(F^n(\rho))\bigr)
                 -\operatorname{Tr}(E_*\rho)\right|.
\tag{30.2}
$$

The decoder may depend on $E_*,n$ and is independent of the input.
It acts once on the same terminal qutrit, without a chronological record,
source label, reference access, a smaller input code, intermediate
correction or postselection. Every complex qutrit density matrix remains
in the supremum. The output effect is allowed to be any complex effect
on $\mathbb C^3$; no projection restriction or enlarged projection
dilation is part of (30.2).

Write

$$
s=(-1/2)^{n-1},\quad \tau=|s|,\quad
\epsilon=\operatorname{sgn}(s),\quad
a=(1+s)/2,\quad b=(1-s)/2,\quad L=(1-\tau)/2.
\tag{30.3}
$$

Thus $a,b$ are the signed coefficients $\alpha,\beta$ of [ERM, (27.2)][ERM],
not the coefficients ordered by $\tau$ in [ERM, Theorem 27.5][ERM].
All radicals below denote positive real radicals. The symbol $\varrho$
below is a residual parameter; the task populations in [ERM, (27.1)][ERM]
are fixed at $p=q=1/2,r=0$.

Use the existing task/effect and support formulas [ERM, (27.4)][ERM],
the decoder [ERM, (27.5)][ERM], and the entire image and forward formulas
[ERM, Proposition 27.2, (27.6)–(27.7)][ERM]. In the present notation,
for a block Hermitian matrix,

$$
G_s\!\left(\begin{pmatrix}x&z&0\\\overline z&y&0\\0&0&d\end{pmatrix}\right)
 =\begin{pmatrix}x&sz&0\\s\overline z&ay+bd&0\\0&0&by+ad\end{pmatrix}.
\tag{30.4}
$$

For an arbitrary physical effect $B$, set
$K=\Delta_W(U_0^\dagger B U_0)$. The reused formulas read

$$
\begin{gathered}
(F^n)^\dagger(B)=G_s(K),\qquad
F^n(Y)=U_0G_s(\Delta_W(Y))U_0^\dagger,\\
\eta_n(E_*)=\min_{0\le B\le I_3}\|(F^n)^\dagger(B)-E_*\|_{\rm op},\\
\eta_n(E_*)\ge\operatorname{Tr}(YE_*)
              -\operatorname{Tr}\bigl((F^n(Y))_+\bigr)
\quad(Y=Y^\dagger,\ \|Y\|_1\le1).
\end{gathered}
\tag{30.5}
$$

The task/effect and preparation interface is also [PA, Definitions
86.1/86.3 and (86.4)][PA] and [BKKNOTE]. The qutrit iteration supplier is
[QM, §§18–20, especially (19.4)][QM]; its full five-dimensional transient
is outside (30.2). Bény–Kempf–Kribs [BKKDOI], Definition 8, equation (7),
Theorem 9 and Corollary 10, supplies the literature-attested exact
observable-correction framework described in [BKKNOTE]. The norm,
support, decoder and entire-image results just cited are intermediate
tools here. The source-specific optimum in Theorem 30.3 is repo-derived
relative to these suppliers; no approximate minimax formula for (30.2)
is attributed to the exact observable-algebra correction results.

**Definition 30.2 (Three algebraic branches and their certificates).**
For $n\ge4$, specify $t$ as the unique real root in $(L,1/2)$ of

$$
\tau^4t^4+2\tau^2(1-\tau^2)t^3+(1-\tau^2)^2t^2-t+1/4=0.
\tag{30.6}
$$

Put

$$
\begin{gathered}
w=\sqrt{t(1-t)},\quad \varrho=1/2-t,\quad \ell=1/2-\tau w,\quad
A=\begin{pmatrix}-\varrho&\ell\\\ell&\varrho\end{pmatrix},\\
K_n=\begin{pmatrix}1-t&\epsilon w&0\\\epsilon w&t&0\\0&0&t\end{pmatrix},\\
h=\frac{\varrho\bigl(a+s+2a\tau\ell/w\bigr)}{bt},\qquad
c=\frac1{2+(b/a)(h+\varrho/t)},\qquad
\mu=(b/a)c(h+\varrho/t),\\
Y_n=c(hI_2+A/t)\oplus(-\mu).
\end{gathered}
\tag{30.7}
$$

For the two exceptional horizons define polynomials, with numerical
parameters $(k,A_0,B_0)$, by

$$
\begin{aligned}
P(u)&=-2u^2+ku+1,\\
Q(u)&=4u^4+A_0u^2+B_0,\\
H(u)&=-8ku^4-(4A_0+16)u^3-(8B_0+2A_0)u+2kB_0,\\
\mathcal P(u)&=H(u)^2-36(k-4u)^2Q(u).
\end{aligned}
\tag{30.8}
$$

At $n=2$ take $(k,A_0,B_0)=(8,68,1)$ and the unique root
$u\in(1/2,3/4)$ of $\mathcal P(u)=0$. At $n=3$ take
$(k,A_0,B_0)=(16,236,25)$ and the unique root
$u\in(1,17/16)$ of $\mathcal P(u)=0$. Equivalently the respective
polynomials $\mathcal P/64$ are explicitly

$$
\begin{aligned}
p_2(u)={}&64u^8+576u^7+1260u^6+432u^5+508u^4\\
         &\quad+2304u^3-2133u^2-36u-32,\\
p_3(u)={}&256u^8+3840u^7+14364u^6+2976u^5+14260u^4\\
         &\quad-7008u^3-27153u^2-15000u+6400.
\end{aligned}
\tag{30.9}
$$

For either exceptional horizon set

$$
R=\sqrt{Q(u)},\qquad t=\frac{P(u)}{2(R+3)}.
\tag{30.10}
$$

For $n=2$ put

$$
\begin{gathered}
x=\frac12+\frac{t(2u^2+1)}R,\qquad H_0=1-x,\qquad
v=\frac12-\frac{8tu}R,\\
y=\frac{3t-H_0}2,\qquad z=-2v,\qquad d=\frac{3H_0-t}2,\\
K_2=\begin{pmatrix}x&z&0\\z&y&0\\0&0&d\end{pmatrix},\qquad
Y_{\rm raw}=\begin{pmatrix}-u^2&2u&0\\2u&1/2&0\\0&0&-3/2\end{pmatrix},
\qquad Y_2=\frac{2Y_{\rm raw}}{R+3}.
\end{gathered}
\tag{30.11}
$$

Here $K_2$ denotes the full qutrit effect at horizon two; its upper
$2\times2$ block will be written $(K_2)_{\xi e}$.
For $n=3$ put

$$
\begin{gathered}
x=\frac12+\frac{t(5-2u^2)}R,\qquad H_0=1-x,\qquad
v=\frac12-\frac{16tu}R,\\
y=\frac{5H_0-3t}2,\qquad z=4v,\qquad d=\frac{5t-3H_0}2,\\
K_3=\begin{pmatrix}x&z&0\\z&y&0\\0&0&d\end{pmatrix},\qquad
Y_{\rm raw}=\begin{pmatrix}u^2&4u&0\\4u&5/2&0\\0&0&-3/2\end{pmatrix},
\qquad Y_3=\frac{2Y_{\rm raw}}{R+3}.
\end{gathered}
\tag{30.12}
$$

In every branch the physical output effect and the terminal decoder are

$$
\begin{gathered}
B_n=U_0K_nU_0^\dagger,\\
\mathcal D_n(X)=\operatorname{Tr}(B_nX)E_*
              +\operatorname{Tr}((I_3-B_n)X)\frac{I_3-E_*}{2}.
\end{gathered}
\tag{30.13}
$$

The existence, uniqueness, effect inequalities and denominator conditions
in these prescriptions are included in Theorem 30.3.

**Theorem 30.3 (Exact balanced optimum with matching full-qutrit certificates).**
For the fixed channel and task of Definition 30.1, at every finite integer
$n\ge2$, Definition 30.2 is well-defined and

$$
\begin{gathered}
\eta_n(E_*)=t,\qquad
0\le K_n\le I_3,\qquad 0\le B_n\le I_3,\qquad
Y_n=Y_n^\dagger,\quad \|Y_n\|_1=1,\\
\|E_*-G_s(K_n)\|_{\rm op}=t
 =\operatorname{Tr}(Y_nE_*)-
          \operatorname{Tr}\bigl((F^n(Y_n))_+\bigr).
\end{gathered}
\tag{30.14}
$$

Thus (30.6) gives the value at every $n\ge4$, while (30.8)–(30.12)
give the degree-eight branches at exactly $n=2,3$. The map (30.13)
is one input-independent CPTP map $M_3(\mathbb C)\to M_3(\mathbb C)$
attaining (30.2) in each case. The lower equality in (30.14) bounds every
complex effect and every decoder allowed in (30.2).

This theorem concerns the balanced slice $p=q=1/2,r=0$ of [ERM,
Definition 27.10][ERM]. It supplies no value for the other $r=0,pq>0$
tasks or the unresolved interior outside [ERM, (27.24)][ERM]. Horizons
below two retain [ERM, Theorem 27.3][ERM]. Separate terminal decoders
for different tasks or horizons do not assert a common decoder for
several tasks or uniform recovery over unbounded horizons. Uniqueness
of the selected algebraic root does not assert uniqueness of an
optimizing effect or decoder. No classification of projective optimizers
at all horizons is part of (30.14).

Proof. The map $G_s$ is self-adjoint on block Hermitian matrices for the
trace pairing: the coherence multiplier $s$ is real and its population
matrix $\left(\begin{smallmatrix}a&b\\b&a\end{smallmatrix}\right)$
is symmetric. Hence every displayed witness, which commutes with $W$,
satisfies

$$
\operatorname{Tr}(YG_s(K))=\operatorname{Tr}(G_s(Y)K),\qquad
\operatorname{Tr}\bigl((F^n(Y))_+\bigr)
 =\operatorname{Tr}\bigl((G_s(Y))_+\bigr).
\tag{30.15}
$$

The second equality uses the physical conjugation in (27.7).
For an arbitrary physical effect the associated
$K=\Delta_W(U_0^\dagger BU_0)$ is an effect. Conversely every block
effect $K$ is attained by $B=U_0KU_0^\dagger$, as in (27.6).
Thus a support equality for $G_s(Y)$ and $K$ is exactly the physical
support equality for $F^n(Y)$ and $B$, including comparison with effects
that do not commute with $W$.

First establish the quartic root and an auxiliary feasible construction
for every $0<\tau\le1/2$. Define on $(L,1/2)$

$$
f_\tau(t)=t-\frac14-
 \left(\frac12-\tau\sqrt{t(1-t)}\right)^2.
\tag{30.16}
$$

Here $t>0$, $t<1/2$ and $w=\sqrt{t(1-t)}>0$. Differentiation gives

$$
f_\tau'(t)=1+
 \frac{\tau(1/2-\tau w)(1-2t)}w>0.
\tag{30.17}
$$

Writing $q_0=\sqrt{1-\tau^2}$, the endpoint values are

$$
f_\tau(L)=\frac{\tau(q_0-1)}2-
                 \frac{\tau^2q_0^2}4<0,\qquad
f_\tau(1/2)=\frac{\tau(2-\tau)}4>0.
\tag{30.18}
$$

There is exactly one zero $t_0\in(L,1/2)$. The equation $f_\tau(t)=0$
is equivalent to

$$
\tau\sqrt{t(1-t)}=\frac12-t+\tau^2t(1-t).
\tag{30.19}
$$

Both sides are positive throughout this interval, so squaring is
reversible there and gives precisely (30.6). This proves the stated
quartic root isolation without extra roots. For either sign of $s$,
the auxiliary effect

$$
K^{(0)}=\begin{pmatrix}
1-t_0&\epsilon\sqrt{t_0(1-t_0)}&0\\
\epsilon\sqrt{t_0(1-t_0)}&t_0&0\\0&0&t_0
\end{pmatrix}
\tag{30.20}
$$

has a rank-one orthogonal projection as its upper block and a scalar
$t_0\in(0,1)$ as its last block. It is an effect. Its residual is
$A_0'\oplus(-t_0)$, with

$$
A_0'=\begin{pmatrix}
t_0-1/2&1/2-\tau\sqrt{t_0(1-t_0)}\\
1/2-\tau\sqrt{t_0(1-t_0)}&1/2-t_0
\end{pmatrix},\qquad (A_0')^2=t_0^2I_2.
\tag{30.21}
$$

The last identity is (30.16). Thus $\eta_n(E_*)\le t_0<1/2$
independently of any exceptional construction. At $\tau=1/2$,

$$
f_{1/2}(1/3)=\frac{6\sqrt2-8}{36}>0,
\tag{30.22}
$$

so the auxiliary bound is strictly below $1/3$ at horizon two.

Next isolate the exceptional roots. On each interval in Definition
30.2, $P>0$, $P'=k-4u>0$ and $Q>0$. The polynomial $H$ is strictly
decreasing for $u>0$; it already has values $-96$ at $u=1/2$ for
$n=2$ and $-960$ at $u=1$ for $n=3$. In particular $H<0$ on the
respective intervals. Consequently $\mathcal P(u)=0$ is equivalent there to

$$
H(u)+6P'(u)\sqrt{Q(u)}=0.
\tag{30.23}
$$

Let $D=\sqrt Q+3$ and $N=P'D-PD'$. Direct differentiation gives

$$
\begin{gathered}
2\sqrt Q\,N=H+6P'\sqrt Q,\qquad N'=-4D-PD'',\\
2QQ''-(Q')^2
 =128u^6+48A_0u^4+96B_0u^2+4A_0B_0>0.
\end{gathered}
\tag{30.24}
$$

Since $D''=(2QQ''-(Q')^2)/(4Q^{3/2})>0$, one has $N'<0$.
The endpoint values of the numerator $2\sqrt Q\,N$ are, respectively,

$$
\begin{array}{ll}
n=2:&-96+18\sqrt{73}>0,\qquad
       (-935+15\sqrt{2593})/4<0,\\
n=3:&-960+72\sqrt{265}>0,\qquad
       (-629049+282\sqrt{4858177})/512<0.
\end{array}
\tag{30.25}
$$

These strict signs follow by squaring the compared positive quantities.
They prove existence and uniqueness of a zero of $N$, and hence of
(30.23) and the specified degree-eight polynomial, in each interval.
Also $t(u)=P/(2D)$ has derivative $N/(2D^2)$: it increases from the
left endpoint to the selected root and is stationary there. The sign
conditions in (30.23) make the squared polynomial reversible; root
selection is not based on stationarity alone.

For $n\ge4$, take $t=t_0$ and the effect (30.7), which equals (30.20).
Its image and residual are

$$
G_s(K_n)=\begin{pmatrix}1-t&\tau w&0\\\tau w&t&0\\0&0&t\end{pmatrix},
\qquad E_*-G_s(K_n)=A\oplus(-t),\qquad A^2=t^2I_2.
\tag{30.26}
$$

This proves the upper bound and the effect inequalities. The upper
block of $K_n$ is a rank-one projection, and its remaining eigenvalue
is $t\in(0,1/2)$, so the full qutrit effect is nonprojective.
It remains to prove that the witness in (30.7) attains the support.
For these horizons,

$$
0<\tau\le\frac18,\quad L\ge\frac7{16},\quad
0<\varrho<\frac\tau2,\quad
\frac7{16}<w\le\frac12,\quad \frac7{16}\le\ell<\frac12,\quad
a,b\in[7/16,9/16].
\tag{30.27}
$$

In particular $a+s\ge5/16>0$, and

$$
\frac{\varrho}{bt}<\frac{16}{49},\qquad
a+s+\frac{2a\tau\ell}{w}
 <\frac{11}{16}+\frac9{56}=\frac{95}{112},\qquad
0<h<\frac{95}{343}<1.
\tag{30.28}
$$

Thus $c,\mu>0$. Since $A/t$ has eigenvalues $1,-1$,
$\|Y_n\|_1=2c+\mu=1$.
The scalar block of $G_s(Y_n)$ is zero by the formula for $\mu$.
Write its upper block as $M$ and put $J_\epsilon=\operatorname{diag}(1,\epsilon)$.
Then

$$
\frac{J_\epsilon M J_\epsilon}{c}
 =\begin{pmatrix}
h-\varrho/t&\tau\ell/t\\
\tau\ell/t&(s/a)(h+\varrho/t)
\end{pmatrix}.
\tag{30.29}
$$

The definition of $h$ makes $(\sqrt{1-t},\sqrt t)^{\mathsf T}$
an eigenvector of this matrix. For completeness, the condition for this
eigenvector is that the difference of the diagonal entries be
$2\varrho\tau\ell/(tw)$; substituting $a-s=b$ yields exactly (30.7).
The eigenvalue on this vector exceeds the perpendicular eigenvalue by

$$
\delta=\frac{c\tau\ell}{tw}>0,\qquad
\frac{\operatorname{Tr}M}{\delta}
 =\frac{2\varrho}{b}
   \left(a+s+\frac{2\epsilon w}{\ell}\right).
\tag{30.30}
$$

The bounds in (30.27) imply, for both signs of $s$,

$$
\left|\frac{\operatorname{Tr}M}{\delta}\right|
 \le\frac{1/8}{7/16}\left(\frac{11}{16}+\frac{16}{7}\right)
 =\frac{333}{392}<1.
\tag{30.31}
$$

Therefore the two eigenvalues of $M$ have opposite signs. Undoing
$J_\epsilon$, the upper block of $K_n$ is precisely the positive
spectral projection of $M$. Its scalar population $t$ is permitted
on the zero scalar block. It follows that

$$
\operatorname{Tr}(G_s(Y_n)K_n)
 =\operatorname{Tr}((G_s(Y_n))_+),\qquad
\operatorname{Tr}\bigl(Y_n(E_*-G_s(K_n))\bigr)
 =2ct+\mu t=t.
\tag{30.32}
$$

Together with (30.5) and (30.15), these are the matching lower bound
and equality (30.14) for every $n\ge4$.

For the exceptional horizons first compute the lower witnesses without
assuming feasibility of $K_n$. Their upper block determinants are
$-9u^2/2$ at $n=2$ and $-27u^2/2$ at $n=3$, hence negative.
In either case the upper block has trace norm $R/2$, and its negative
scalar block has magnitude $3/2$. Consequently

$$
\|Y_{\rm raw}\|_1=(R+3)/2,\qquad \|Y_n\|_1=1.
\tag{30.33}
$$

Propagation gives, respectively,

$$
\begin{aligned}
n=2:\quad G_s(Y_{\rm raw})
 &=-\begin{pmatrix}u^2&u\\u&1\end{pmatrix}\oplus0,
 &\operatorname{Tr}((G_s(Y_{\rm raw}))_+)&=0,\\
n=3:\quad G_s(Y_{\rm raw})
 &=\begin{pmatrix}u^2&u\\u&1\end{pmatrix}\oplus0,
 &\operatorname{Tr}((G_s(Y_{\rm raw}))_+)&=u^2+1.
\end{aligned}
\tag{30.34}
$$

Subtracting these support values from $\operatorname{Tr}(Y_{\rm raw}E_*)$
gives $P(u)/4$ in both cases. Normalization therefore gives lower
value $P/(2(R+3))=t>0$. In particular $t\le\eta_n(E_*)\le t_0$
already follows before exceptional primal feasibility. By (30.22),
$0<t<1/3$ at $n=2$; at $n=3$ the auxiliary bound gives $t<1/2$.
The increase of $P/(2D)$ up to the selected root also gives

$$
t>\frac{15}{2(\sqrt{265}+3)}>\frac38\qquad(n=3).
\tag{30.35}
$$

Thus the preliminary bounds used below do not assume the exceptional
effects are feasible.

Let $S$ denote the sign of the nonsingular upper block of $Y_{\rm raw}$.
The spectral formula gives

$$
\begin{aligned}
n=2:\quad S&=\begin{pmatrix}
-(2u^2+1)/R&8u/R\\8u/R&(2u^2+1)/R
\end{pmatrix},\\
n=3:\quad S&=\begin{pmatrix}
(2u^2-5)/R&16u/R\\16u/R&(5-2u^2)/R
\end{pmatrix}.
\end{aligned}
\tag{30.36}
$$

In both cases $S^2=I_2$. Form
$C=( (E_*)_{\xi e}-tS)\oplus t$.
The exact finite-$s$ inverse in [ERM, (27.28), with the inverse-effect
constraints of (27.27)][ERM] reads, for this $C$,

$$
x=C_{\xi\xi},\qquad z=C_{\xi e}/s,\qquad
y=\frac{aC_{ee}-bt}{s},\qquad d=\frac{at-bC_{ee}}s.
\tag{30.37}
$$

At $s=-1/2$ this is exactly (30.11); at $s=1/4$ it is (30.12).
In particular both prescribed matrices satisfy

$$
G_s(K_n)=\begin{pmatrix}x&v&0\\v&H_0&0\\0&0&t\end{pmatrix},
\qquad E_*-G_s(K_n)=tS\oplus(-t).
\tag{30.38}
$$

These are explicit finite inverses of the boundary condition (27.28);
no interior Schur denominator is introduced at task population $r=0$.

To prove the block identities needed for effect positivity, put

$$
J(u,t)=\operatorname{Tr}(Y_{\rm raw}(u)E_*)
 -\operatorname{Tr}((G_s(Y_{\rm raw}(u)))_+)
 -t\|Y_{\rm raw}(u)\|_1.
\tag{30.39}
$$

The quotient formula gives $J=0$ at the selected $u,t$, and (30.24)
gives $\partial_uJ=0$ with $t$ held fixed. The differentiability
identity for the trace norm of the nonsingular upper block is
$\partial_u\|Y_{\rm raw}\|_1=\operatorname{Tr}(S(Y_{\rm raw}')_{\xi e})$;
the scalar block is constant. Using (30.38) in $J=0$ and
$\partial_uJ=0$, then applying (30.15), gives

$$
\begin{aligned}
\operatorname{Tr}(G_s(Y_{\rm raw})K_n)
 &=\operatorname{Tr}((G_s(Y_{\rm raw}))_+),\\
\operatorname{Tr}(G_s(Y_{\rm raw}')K_n)
 &=\frac{d}{du}\operatorname{Tr}((G_s(Y_{\rm raw}))_+).
\end{aligned}
\tag{30.40}
$$

Here every entry of $K_n$ was already specified in (30.11) or (30.12).
At $n=2$, (30.34) turns these two scalar equalities into

$$
u^2x+2uz+y=0,\qquad ux+z=0,
\qquad z=-ux,\quad y=u^2x,
\qquad (K_2)_{\xi e}=x\begin{pmatrix}1&-u\\-u&u^2\end{pmatrix}.
\tag{30.41}
$$

At $n=3$ they become

$$
\begin{gathered}
u^2(1-x)-2uz+1-y=0,\qquad u(1-x)-z=0,\\
z=uH_0,\qquad 1-y=u^2H_0,\qquad
I_2-(K_3)_{\xi e}=H_0\begin{pmatrix}1&-u\\-u&u^2\end{pmatrix}.
\end{gathered}
\tag{30.42}
$$

Thus the root condition supplies the stated algebraic block identities;
the ensuing inequalities and support equalities, rather than the
stationary equation alone, supply optimality.

At $n=2$, on $1/2<u<3/4$,

$$
\frac{2u^2+1}{R}<\frac38.
\tag{30.43}
$$

After squaring positive sides this is
$-220u^4+356u^2-55>0$. As a concave quadratic in $u^2$ on
$[1/4,9/16]$, this expression is bounded below by the lesser endpoint
value, and both endpoint values are positive. Since $0<t<1/3$,

$$
\frac12<x<\frac58,\qquad \frac38<H_0<\frac12,\qquad
0<x(1+u^2)<\frac{125}{128}<1,\qquad
\frac{19}{48}<d<\frac34.
\tag{30.44}
$$

The block identity (30.41) has eigenvalues $0,x(1+u^2)$;
together with the last inequality this proves $0\le K_2\le I_3$.
Equation (30.38) proves its residual norm is $t$. Equation (30.40),
normalized by $2/(R+3)$, makes its support equality exact.

At $n=3$ the root interval gives $16<R<18$ and
$351/128<5-2u^2<3$. Combining these with $3/8<t<1/2$ gives

$$
\begin{gathered}
\frac{13}{32}<H_0<\frac{907}{2048},\qquad
0<H_0(1+u^2)<\frac{494315}{524288}<1,\\
\frac3{16}<d<\frac{41}{64}.
\end{gathered}
\tag{30.45}
$$

By (30.42), the complement of the upper block has eigenvalues
$0,H_0(1+u^2)$. Thus $0\le(K_3)_{\xi e}\le I_2$, and the scalar
bound proves $0\le K_3\le I_3$. Again (30.38) gives residual norm $t$
and (30.40) gives the support equality. In either exceptional case,

$$
\operatorname{Tr}\bigl(Y_n(E_*-G_s(K_n))\bigr)
 =t\|Y_n\|_1=t.
\tag{30.46}
$$

Using the normalized support equality and (30.15) identifies (30.46)
with the lower expression in (30.5). This proves (30.14) for both
exceptions against the entire complex effect interval.

Finally conjugation by $U_0$ preserves all effect inequalities, so
$0\le B_n\le I_3$ in every branch. Formula (30.13) is exactly the
same-qutrit decoder (27.5), with output states $E_*$ and $(I_3-E_*)/2$.
Explicitly, choose a spectral decomposition
$B_n=\sum_j b_j|u_j\rangle\langle u_j|$ with $0\le b_j\le1$
and an orthonormal basis $w_1,w_2$ of $\ker E_*$. Kraus matrices are

$$
L_j=\sqrt{b_j}|v_*\rangle\langle u_j|,\qquad
M_{kj}=\sqrt{(1-b_j)/2}|w_k\rangle\langle u_j|,
\qquad 1\le j\le3,\quad 1\le k\le2.
\tag{30.47}
$$

They are all maps on $\mathbb C^3$, and their adjoint products sum to
$I_3$. They implement (30.13), proving it is CPTP, and direct substitution
gives $\mathcal D_n^\dagger(E_*)=B_n$. For every Hermitian residual $T$,

$$
\sup_{\rho\in\mathsf D(\mathbb C^3)}|\operatorname{Tr}(T\rho)|
 =\max_j|\lambda_j(T)|=\|T\|_{\rm op}.
\tag{30.48}
$$

The extreme eigenstates attain this supremum. Therefore the decoder
attains error $t$ over all complex inputs. Conversely, every allowed
CPTP decoder has an effect $\mathcal D^\dagger(E_*)$, so the Hermitian
trace-norm-one witnesses in (30.14) bound that full decoder class.
No restriction to real inputs was used: real entries of an attaining
certificate do not restrict the quantified input or effect domains.

There is no omitted finite-horizon degeneracy. At $n=2,3$ the isolated
roots have $P,Q,R,R+3,t>0$. At every $n\ge4$, (30.27) gives
$a,b,t,w,\ell>0$, and (30.28) makes the denominator defining $c$
strictly positive. Every finite horizon has $s\ne0$; (30.37) is used
only at $s=-1/2,1/4$. The formulas never evaluate $s=0$, an infinite
horizon inverse, or a vanishing task-population Schur denominator.
The two exceptional branches and $n\ge4$ exhaust the scope of (30.2).
$\square$

## 追加锚（本行以下为增补区）

## 31. The all-population spectator–e task and a conditional quartic

**Definition 31.1 (Fixed task, signed coordinates and source correspondence).**
Use the ordered orthonormal basis $(\xi,e,f)$ and exactly $W,U_0,F$ of
(29.1). The chronological histories are fair and independently sampled
and every record is erased, as in [ERM, Definition 27.1][ERM]. Fix

$$
\begin{gathered}
0<p<1,\qquad q=1-p,\qquad c=\sqrt{pq},\qquad
v_p=\sqrt p\,\xi+\sqrt q\,e,\qquad E_p=|v_p\rangle\langle v_p|,
\\
E_2=\begin{pmatrix}p&c\\c&q\end{pmatrix},\qquad E_p=E_2\oplus0,
\qquad n\in\mathbb Z,\quad n\ge2,
\\
s=(-1/2)^{n-1},\qquad \tau=|s|,\qquad
\epsilon=\operatorname{sgn}(s),\qquad a=(1+s)/2,\quad b=(1-s)/2.
\end{gathered}
\tag{31.1}
$$

All square roots of strictly positive quantities denote their positive
real roots. In particular $a,b,c,\tau>0$, $s\ne0$, and

$$
a+b=1,\quad a-b=a^2-b^2=s,\quad
-1/2\le s\le1/4,\quad a-s^2=b(1+2s)\ge0.
\tag{31.2}
$$

The last equality can vanish only at $n=2$, when $s=-1/2$.
For a block Hermitian matrix define, using the already established
image map [ERM, (27.6)–(27.7)][ERM],

$$
G_s\!\left(\begin{pmatrix}x&z\\\overline z&y\end{pmatrix}\oplus d\right)
 =\begin{pmatrix}x&sz\\s\overline z&ay+bd\end{pmatrix}\oplus(by+ad).
\tag{31.3}
$$

The quantity to be determined is exactly

$$
\eta_n(E_p)=\min_{0\le B\le I_3}
 \|(F^n)^\dagger(B)-E_p\|_{\rm op}
 =\min_{\substack{0\le K_2\le I_2\\0\le d\le1}}
 \|E_p-G_s(K_2\oplus d)\|_{\rm op}.
\tag{31.4}
$$

The first minimum is over all complex qutrit effects. Each block effect
$K$ in the second minimum is realized by the physical effect
$B=U_0KU_0^\dagger$. The witness below is an input functional $Y$ itself;
it is not conjugated by $U_0$. These statements reuse exactly
[ERM, (27.4)–(27.7)][ERM]. When an inverse is used, it is only the
finite-$s$, $r=0$ boundary inverse with the effect constraints of
[ERM, (27.28)][ERM]; no interior Schur fraction is used.

The task in (31.4) retains all complex input density matrices and one
input-independent terminal CPTP decoder on the same qutrit. It grants
no history, reference, smaller code, intermediate correction,
postselection or larger output. At $p=1/2$ use Definition 30.2 and
Theorem 30.3 verbatim, including their $n=2$, $n=3$ and $n\ge4$
branches; none of their balanced formulas is redefined here.

The Heisenberg correction framework is literature-attested in
Bény–Kempf–Kribs, Definition 8, equation (7), Theorem 9 and Corollary 10
[BKKDOI]. Its exact algebra-correction criterion and the elementary
single-task interface in [BKKNOTE] are intermediate tools. The
fixed-effect loss (31.4) is distinct from the worst-case entanglement
fidelity in Bény–Oreshkov, *General conditions for approximate quantum
error correction and near-optimal recovery channels*, Theorem 1,
[arXiv:0907.5391v4](https://arxiv.org/html/0907.5391v4).
No equality with that fidelity optimization is assumed. The additional
branch formulas and spectral classification below are repo-derived
from (31.3) and finite-dimensional norm duality, relative to the
supplied conditional and branch arguments. No global literature
novelty or priority assertion is made.

**Definition 31.2 (The conditional root and pair).**
For $0<y<1$ put

$$
\begin{gathered}
w(y)=\sqrt{y(1-y)},\qquad \ell(y)=c-\tau w(y),\qquad
D(y)=2(1-\tau^2)y+\tau^2-2q,\\
\mathcal C(y)=D(y)^2y(1-y)-pq\tau^2(1-2y)^2.
\end{gathered}
\tag{31.5}
$$

Let $y_0$ be a real root in $(0,1)$ retained by the exact scalar filter

$$
\mathcal C(y_0)=0,\qquad D(y_0)(1-2y_0)\ge0.
\tag{31.6}
$$

Set $w_0=w(y_0)$, $\ell_0=\ell(y_0)$, $\Delta=y_0-q$ and
$t_0=\sqrt{\Delta^2+\ell_0^2}$. The conditional pair is retained exactly
when $y_0\le t_0$; it is then

$$
K^{\rm C}=\begin{pmatrix}1-y_0&\epsilon w_0\\
                    \epsilon w_0&y_0\end{pmatrix}\oplus y_0,
\qquad
Y^{\rm C}=\frac1{2t_0}
             \begin{pmatrix}2\Delta&\ell_0\\\ell_0&0\end{pmatrix}\oplus0.
\tag{31.7}
$$

For explicit coefficients, let $d_1=2(1-\tau^2)$ and
$d_0=\tau^2-2q$. The coefficients of $\mathcal C$ in descending powers
$y^4,y^3,y^2,y,1$ are

$$
\bigl(-d_1^2,\ d_1^2-2d_1d_0,\
2d_1d_0-d_0^2-4pq\tau^2,\ d_0^2+4pq\tau^2,\ -pq\tau^2\bigr).
\tag{31.8}
$$

**Theorem 31.3 (Existence, uniqueness and exact scope of the conditional pair).**
The retained root (31.6) exists and is unique. Its $w_0,\ell_0,t_0$ are
strictly positive and $t_0<1/2$. If $y_0\le t_0$, the pair (31.7)
satisfies $0\le K^{\rm C}\le I_3$, $\|Y^{\rm C}\|_1=1$, and

$$
\|E_p-G_s(K^{\rm C})\|_{\rm op}=t_0
 =\operatorname{Tr}(Y^{\rm C}E_p)
       -\operatorname{Tr}((G_s(Y^{\rm C}))_+)=\eta_n(E_p).
\tag{31.9}
$$

Proof. Define
$g(y)=(y-q)^2+(c-\tau w(y))^2$. Expanding the squares, using
$q^2+c^2=q$, and differentiating gives

$$
\begin{aligned}
g(y)&=(1-\tau^2)y^2+(\tau^2-2q)y+q-2c\tau w(y),\\
g'(y)&=D(y)-\frac{c\tau(1-2y)}{w(y)},\\
g''(y)&=2(1-\tau^2)+\frac{c\tau}{2w(y)^3}>0.
\end{aligned}
\tag{31.10}
$$

The derivative tends to $-\infty$ at zero and $+\infty$ at one.
There is exactly one stationary point in $(0,1)$. Squaring
$D(y)w(y)=c\tau(1-2y)$ gives $\mathcal C(y)=0$.
Conversely, equality of the squares and the sign filter in (31.6)
give this unsquared equality, including when both sides vanish.
Thus (31.6) specifies precisely that unique stationary point.

If $q<1/2$, then $g'(q)=-\tau(1-\tau)(1-2q)<0$ and
$g'(1/2)=1-2q>0$, so $q<y_0<1/2$. If $q>1/2$, the same expressions
give $1/2<y_0<q$. At $q=1/2$ the root is $y_0=1/2$.
Rewriting stationarity gives

$$
2(y_0-q)w_0=\tau\ell_0(1-2y_0).
\tag{31.11}
$$

In the two unbalanced cases the two factors $y_0-q$ and $1-2y_0$
have the same nonzero sign, so $\ell_0>0$. In the balanced case
$\ell_0=(1-\tau)/2>0$. Also $w_0>0$ and $t_0>0$.
Minimality of $g(y_0)$ gives
$t_0^2\le g(q)=(1-\tau)^2pq<1/4$.

The upper block of $K^{\rm C}$ is a rank-one projection, so it and its
scalar block are effects. Its residual is

$$
E_p-G_s(K^{\rm C})=
 \begin{pmatrix}\Delta&\ell_0\\\ell_0&-\Delta\end{pmatrix}\oplus(-y_0).
\tag{31.12}
$$

The upper block has eigenvalues $t_0,-t_0$; the assumed filter gives
residual norm $t_0$. The upper block of $Y^{\rm C}$ has determinant
$-\ell_0^2/(4t_0^2)<0$ and trace norm
$\sqrt{4\Delta^2+4\ell_0^2}/(2t_0)=1$.
Its propagated scalar vanishes. If $M$ denotes its propagated upper
block, then

$$
M=\begin{pmatrix}\Delta/t_0&s\ell_0/(2t_0)\\
                 s\ell_0/(2t_0)&0\end{pmatrix},\qquad
\delta=\frac{\tau\ell_0}{2t_0w_0}>0.
\tag{31.13}
$$

Equation (31.11) says that the diagonal difference of $M$ is
$\delta(1-2y_0)$. Its off-diagonal is
$\epsilon\delta w_0$. Therefore
$(\sqrt{1-y_0},\epsilon\sqrt{y_0})^{\mathsf T}$ is its eigenvector for
the larger eigenvalue, the eigenvalue gap is $\delta$, and
$\operatorname{Tr}M/\delta=1-2y_0\in(-1,1)$. Its eigenvalues have
opposite signs, so $K^{\rm C}$ attains its effect support. Finally
pairing (31.12) with (31.7) gives $t_0$.
Self-adjointness of $G_s$ for the trace pairing and [ERM, (27.4)][ERM]
give (31.9) against the entire complex effect interval. Equality
$y_0=t_0$ requires no strict inequality in this argument. $\square$

## 32. Four finite algebraic families

**Definition 32.1 (Contact convention).**
All matrices in this section are in $(\xi,e,f)$. The symbol
$S=\left(\begin{smallmatrix}k&\ell/t\\\ell/t&-k\end{smallmatrix}\right)$
in a contact family is required by its root equation to satisfy
$S^2=I_2$. For $-1\le h\le1$ and $\mu\ge0$, put

$$
Y_{\rm raw}=(hI_2+S)\oplus(-\mu),\qquad
Y=Y_{\rm raw}/(2+\mu).
\tag{32.1}
$$

Then $\|Y_{\rm raw}\|_1=2+\mu$ and its pairing with
$tS\oplus(-t)$ is $t(2+\mu)$. A real root is retained only if it
satisfies every interval, sign and scalar filter stated for its family.
The symbols defined within each family are local to that family.

**Definition 32.2 (Family P).**
For $0<t<1/2$ set

$$
V(t)=q+(\tau^2-2q)t-\tau^2t^2,\qquad
\mathcal P_{\rm P}(t)=V(t)^2-4pq\tau^2t(1-t).
\tag{32.2}
$$

Require $\mathcal P_{\rm P}(t)=0$ and $V(t)>0$. Define

$$
\begin{gathered}
w=\sqrt{t(1-t)},\quad \ell=c-\tau w>0,\quad
k=(t-q)/t,\quad
S=\begin{pmatrix}k&\ell/t\\\ell/t&-k\end{pmatrix},\\
\delta=\frac{\tau\ell}{tw},\qquad
h=\frac{a\delta(1-2t)-(a+s)k}{b},\qquad
\mu=\frac ba(h-k),\qquad
T=h+k+\frac sa(h-k).
\end{gathered}
\tag{32.3}
$$

In addition to $\ell>0$, require

$$
-1\le h\le1,\qquad \mu\ge0,\qquad |T|\le\delta.
\tag{32.4}
$$

The pair is

$$
K=\begin{pmatrix}1-t&\epsilon w\\\epsilon w&t\end{pmatrix}\oplus t,
\qquad Y=\frac{(hI_2+S)\oplus(-\mu)}{2+\mu}.
\tag{32.5}
$$

The descending quartic coefficients are

$$
\begin{gathered}
\tau^4,\quad -2\tau^2(\tau^2-2q),\quad
(\tau^2-2q)^2-2q\tau^2+4pq\tau^2,\\
2q(\tau^2-2q)-4pq\tau^2,\quad q^2.
\end{gathered}
\tag{32.6}
$$

**Definition 32.3 (Family M).**
Let $u>0$, and put

$$
\begin{gathered}
\chi=(1+\epsilon)/2,\qquad
A=\epsilon p-\chi,\quad B=2c/\tau,\quad C=aq/\tau-\chi,\\
D=4/\tau^2-2\epsilon a/\tau,\quad E=a^2/\tau^2,\quad m=b/\tau,\\
P(u)=Au^2+Bu+C,\qquad Q(u)=u^4+Du^2+E,\\
J(u)=-2Bu^4+(2AD-4C)u^3+(4AE-2CD)u+2BE,\\
\mathcal P_{\rm M}(u)=J(u)^2-4m^2(2Au+B)^2Q(u).
\end{gathered}
\tag{32.7}
$$

Require $\mathcal P_{\rm M}(u)=0$ and the unsquared filter

$$
J(u)+2m(2Au+B)\sqrt{Q(u)}=0,\qquad P(u)>0.
\tag{32.8}
$$

Define

$$
\begin{gathered}
R=\sqrt{Q(u)},\quad t=P(u)/(R+m),\qquad 0<t<1/2,\\
A_{\rm raw}=\begin{pmatrix}\epsilon u^2&u/\tau\\u/\tau&a/\tau\end{pmatrix},
\qquad
S=\frac1R\begin{pmatrix}\epsilon u^2-a/\tau&2u/\tau\\
                          2u/\tau&a/\tau-\epsilon u^2\end{pmatrix},\\
H=E_2-tS,\qquad x=H_{00},\quad z=H_{01}/s,\qquad
 y=(aH_{11}-bt)/s,\quad d=(at-bH_{11})/s.
\end{gathered}
\tag{32.9}
$$

The residual indices $0,1$ mean $\xi,e$. The remaining filters are

$$
0\le d\le1,\qquad
\begin{cases}
0\le x(1+u^2)\le1,&s<0,\\
0\le(1-x)(1+u^2)\le1,&s>0.
\end{cases}
\tag{32.10}
$$

Take

$$
K=\begin{pmatrix}x&z\\z&y\end{pmatrix}\oplus d,\qquad
Y=\frac{A_{\rm raw}\oplus(-m)}{R+m}.
\tag{32.11}
$$

For fully explicit degree-eight coefficients, write
$j_4=-2B$, $j_3=2AD-4C$, $j_1=4AE-2CD$, $j_0=2BE$.
Then $\mathcal P_{\rm M}(u)=\sum_{i=0}^8 e_i u^i$, where

$$
\begin{aligned}
e_8&=j_4^2,&e_7&=2j_4j_3,\\
e_6&=j_3^2-16m^2A^2,&
e_5&=2j_4j_1-16m^2AB,\\
e_4&=2j_4j_0+2j_3j_1-4m^2(B^2+4A^2D),&
e_3&=2j_3j_0-16m^2ABD,\\
e_2&=j_1^2-4m^2(B^2D+4A^2E),&
e_1&=2j_1j_0-16m^2ABE,\\
e_0&=j_0^2-4m^2B^2E.
\end{aligned}
\tag{32.12}
$$

**Definition 32.4 (Family D and its two signed branches).**
Use D+ only if $s>0$. Its root variable satisfies $0<t<b$. Put

$$
\begin{gathered}
R_0(t)=at(b-t),\\
L_0(t)=(s-as^2)t^2+ab(s^2-2q)t+b^2q,\\
\mathcal P_{{\rm D}+}(t)=L_0(t)^2-4b^2pq\tau^2R_0(t),\\
d=0,\qquad x=1-at/b,\quad y=t/b,\quad
z=\epsilon\sqrt{R_0(t)}/b.
\end{gathered}
\tag{32.13}
$$

Require $\mathcal P_{{\rm D}+}(t)=0$ and $L_0(t)>0$.
Use D− only if $s<0$. Its root variable satisfies $a<t<1/2$. Put

$$
\begin{gathered}
R_1(t)=a(1-t)(t-a),\qquad h_0=s+bq,\\
L_1(t)=(s-as^2)t^2+a\bigl(s^2(1+a)-2h_0\bigr)t
          +h_0^2+b^2pq-s^2a^2,\\
\mathcal P_{{\rm D}-}(t)=L_1(t)^2-4b^2pq\tau^2R_1(t),\\
d=1,\qquad x=a(1-t)/b,\quad y=(t-a)/b,\quad
z=\epsilon\sqrt{R_1(t)}/b.
\end{gathered}
\tag{32.14}
$$

Require $\mathcal P_{{\rm D}-}(t)=0$ and $L_1(t)>0$.
For either branch set

$$
\begin{gathered}
K_2=\begin{pmatrix}x&z\\z&y\end{pmatrix},\quad
\ell=c-sz>0,\quad k=(ay+bd-q)/t,\quad
S=\begin{pmatrix}k&\ell/t\\\ell/t&-k\end{pmatrix},\\
Q=\begin{cases}(K_2-tI_2)/(1-t),&\mathrm{D+},\\
                I_2-K_2/t,&\mathrm{D-},\end{cases}\\
\kappa=\frac{s\ell}{tQ_{01}},\qquad h=\kappa Q_{00}-k,\qquad
\mu=\frac{a(h-k)-\kappa Q_{11}}b,\qquad
\zeta=b(h-k)-a\mu.
\end{gathered}
\tag{32.15}
$$

In addition to $\ell>0$, require

$$
-1\le h\le1,\qquad \mu\ge0,\qquad
\begin{cases}\zeta\le0,&\mathrm{D+},\\\zeta\ge0,&\mathrm{D-}.
\end{cases}
\tag{32.16}
$$

Take $K=K_2\oplus d$ and $Y$ from (32.1).
For either quartic, write $L_i=l_2t^2+l_1t+l_0$ and
$R_i=r_2t^2+r_1t+r_0$, with

$$
\begin{array}{c|ccc|ccc}
 &l_2&l_1&l_0&r_2&r_1&r_0\\ \hline
\mathrm{D+}&s-as^2&ab(s^2-2q)&b^2q&-a&ab&0\\
\mathrm{D-}&s-as^2&a(s^2(1+a)-2h_0)&h_0^2+b^2pq-s^2a^2
 &-a&a(1+a)&-a^2
\end{array}
\tag{32.17}
$$

The descending coefficients of $\mathcal P_{{\rm D}\pm}$ are

$$
\bigl(l_2^2,\ 2l_2l_1,\ l_1^2+2l_2l_0-4b^2pq\tau^2r_2,\
2l_1l_0-4b^2pq\tau^2r_1,\ l_0^2-4b^2pq\tau^2r_0\bigr).
\tag{32.18}
$$

**Definition 32.5 (Family R−).**
Use this family only if $s<0$. For $u>0$ define

$$
\begin{gathered}
A=2p-1,\quad B=4c,\quad C=2q-s/a,\quad d_*=1/a,\\
D=4s^2-2s/a,\quad E=s^2/a^2,\quad
P(u)=Au^2+Bu+C,\quad Q(u)=u^4+Du^2+E,\\
L(u)=-Bu^2+2(Ad_*-C)u+Bd_*,\\
J(u)=(4d_*-2D)u^3+(2Dd_*-4E)u,\\
\mathcal P_{{\rm R}-}(u)=4Q(u)L(u)^2-J(u)^2.
\end{gathered}
\tag{32.19}
$$

Require $\mathcal P_{{\rm R}-}(u)=0$ and the unsquared filter

$$
2\sqrt{Q(u)}\,L(u)=J(u).
\tag{32.20}
$$

Set

$$
\begin{gathered}
R=\sqrt{Q(u)},\qquad N=u^2+1/a,\qquad
 t=\frac{P(u)-R}{2N},\qquad 0<t<1/2,\\
x=\frac{1+(u^2-s/a)/R}{2},\qquad y=1-x,\qquad z=su/R,\\
d=(t-by)/a,\qquad 0\le d\le t,\\
K=\begin{pmatrix}x&z\\z&y\end{pmatrix}\oplus d,\qquad
Y=\frac{\begin{pmatrix}u^2&u\\u&1\end{pmatrix}\oplus(-b/a)}N.
\end{gathered}
\tag{32.21}
$$

For its explicit coefficients put $l_2=-B$, $l_1=2(Ad_*-C)$,
$l_0=Bd_*$, $j_3=4d_*-2D$, $j_1=2Dd_*-4E$.
Then $\mathcal P_{{\rm R}-}(u)=\sum_{i=0}^8 f_i u^i$, where

$$
\begin{aligned}
f_8&=4l_2^2,&f_7&=8l_2l_1,\\
f_6&=4(l_1^2+2l_2l_0+Dl_2^2)-j_3^2,&
f_5&=8(l_1l_0+Dl_2l_1),\\
f_4&=4\bigl(l_0^2+D(l_1^2+2l_2l_0)+El_2^2\bigr)-2j_3j_1,&
f_3&=8(Dl_1l_0+El_2l_1),\\
f_2&=4\bigl(Dl_0^2+E(l_1^2+2l_2l_0)\bigr)-j_1^2,&
f_1&=8El_1l_0,\\
f_0&=4El_0^2.
\end{aligned}
\tag{32.22}
$$

**Definition 32.6 (Family R+).**
Use this family only if $s>0$. Define

$$
\alpha=(1-s^2)/b=4a,\qquad \beta=q(\alpha-1)+s^2.
\tag{32.23}
$$

Let $t$ be the positive root of the explicitly specified quadratic

$$
\alpha t^2+\beta t-q(1-s^2)=0,\qquad
 t=\frac{-\beta+\sqrt{\beta^2+4\alpha q(1-s^2)}}{2\alpha}.
\tag{32.24}
$$

Put

$$
\begin{gathered}
u=(t+q)/c,\qquad y=t/b,\quad z=su(1-y),\quad
x=1-s^2u^2(1-y),\quad \lambda=x+y-1,\\
\mu=(a-s^2)u^2/b,\quad N=1+\alpha u^2,\quad d=0.
\end{gathered}
\tag{32.25}
$$

Retain this root exactly when $0<t<1/2$ and $0\le\lambda\le t$.
Take

$$
K=\begin{pmatrix}x&z\\z&y\end{pmatrix}\oplus0,\qquad
Y=\frac{\begin{pmatrix}1&u\\u&u^2\end{pmatrix}\oplus(-\mu)}N.
\tag{32.26}
$$

**Definition 32.7 (Finite prescription and boundary conventions).**
If $p=1/2$, select the pair and value of Definition 30.2. Otherwise
first form the conditional root of Definition 31.2. If $y_0\le t_0$,
select (31.7). If this filter fails, examine the ordered families
P, M, D, R, with the signed D and R branches prescribed above.
In each family take all real roots in its stated open interval and
retain exactly those satisfying every stated scalar filter. In the
first family with a retained root select its least retained root.
Distinct repeated roots are counted once. The chosen root determines
$t,K,Y$ by that family's formulas. Theorem 34.1 below establishes
that this prescription is nonempty; nonemptiness is not an assumption
in this definition.

All admissibility inequalities are non-strict unless expressly written
strictly. In particular the prescription retains $h=\pm1$, $\mu=0$,
a zero propagated-support eigenvalue, $d=0,1$ in M, $d=t$ in R−,
$\lambda=0,t$ in R+, and cross-family transition equalities.
At a multiple root, the same unsquared equations and scalar filters
apply without alteration. No formula divides by a polynomial
derivative, by $P'$, by $J$ or by $L$; the unsquared equations are
used even when their individual factors vanish.

After the conditional quartic there are at most $4+8+4+8=24$ roots
if $s<0$, or $4+8+4+2=18$ if $s>0$. The leading coefficients are
$\tau^4>0$ for P, $4B^2>0$ for each degree-eight polynomial in its
own notation, and $(s-as^2)^2>0$ for either D quartic. Here
$s-as^2=s(1-as)\ne0$ by (31.2). The R+ quadratic has positive
leading coefficient and negative constant, so has exactly one positive
root. Thus every selected root is a member of an explicitly finite
set of univariate algebraic roots. No further optimization parameter
or implicit effect-feasibility problem is included in the prescription.

## 追加锚（本行以下为增补区）

## 33. Certificates for every retained root

**Theorem 33.1 (Each retained candidate is a full complex optimum).**
Every root retained in any family P, M, D or R defines an effect
$0\le K\le I_3$ and a Hermitian matrix $Y$ of trace norm one. All its
formulas have nonzero denominators. For its stated $t$,

$$
\begin{gathered}
0<t<1/2,\qquad \|E_p-G_s(K)\|_{\rm op}=t,\\
\operatorname{Tr}(G_s(Y)K)=\operatorname{Tr}((G_s(Y))_+),\qquad
\operatorname{Tr}(Y(E_p-G_s(K)))=t,\\
\eta_n(E_p)=t.
\end{gathered}
\tag{33.1}
$$

Consequently all retained candidates, including roots in different
families, have the same value. Their ordering selects a single pair,
not different possible values of the optimum.

Proof. The general certificate implication is the following application
of the reused interface. Self-adjointness of (31.3) gives
$\operatorname{Tr}(YG_s(K))=\operatorname{Tr}(G_s(Y)K)$.
For block $Y$, [ERM, (27.7)][ERM] gives

$$
\operatorname{Tr}((F^n(Y))_+)=\operatorname{Tr}((G_s(Y))_+).
\tag{33.2}
$$

Thus the two equalities in the middle of (33.1) make the support
lower bound [ERM, (27.4)][ERM] equal $t$. Effect feasibility and the
residual norm give the opposite bound. This compares with all complex
effects, since [ERM, (27.6)][ERM] describes their entire image.
It remains to prove each certificate's identities and feasibility.

For P, expanding the desired upper residual identity gives

$$
(t-q)^2+(c-\tau w)^2-t^2
   =V(t)-2c\tau w.
\tag{33.3}
$$

The quartic and $V>0$ give $V=2c\tau w$; this reverses the only
squaring. Hence $S^2=I_2$. The upper block of (32.5) is a rank-one
projection, and the third eigenvalue is $t\in(0,1)$.
Its residual is $tS\oplus(-t)$. For the raw witness (32.1), its
propagated scalar is zero, and its upper block is

$$
M=\begin{pmatrix}h+k&s\ell/t\\s\ell/t&(s/a)(h-k)\end{pmatrix}.
\tag{33.4}
$$

Here the lower diagonal uses
$a(h-k)-b\mu=(a^2-b^2)(h-k)/a$.
The definition of $h$ makes its diagonal difference
$\delta(1-2t)$, while its off-diagonal is
$\epsilon\delta w$. It follows that the eigenvalue gap is $\delta>0$
and its larger-eigenvalue direction is
$(\sqrt{1-t},\epsilon\sqrt t)^{\mathsf T}$.
Indeed, the squared gap is
$\delta^2((1-2t)^2+4t(1-t))=\delta^2$ and substitution into either
row verifies the direction. Its trace is $T$, so $|T|\le\delta$
is exactly the condition that the larger eigenvalue be nonnegative
and the smaller one nonpositive. The upper projection in $K$ then
attains the support, including either zero-eigenvalue boundary.
Its scalar block lies on a zero propagated scalar. Equation (32.1)
normalizes the witness and pairs it with the residual as $t$.
This proves every assertion for P, with $w,t,a,b,\delta>0$ and
$2+\mu\ge2$ proving all denominator claims.

For M, first compute the raw upper determinant and its spectral gap:

$$
\det A_{\rm raw}=\frac{(as-1)u^2}{\tau^2}<0,\qquad
\|A_{\rm raw}\|_1^2
 = (\epsilon u^2-a/\tau)^2+4u^2/\tau^2=Q(u)>0.
\tag{33.5}
$$

The inequality $as<1$ follows from (31.2). A real symmetric
indefinite $2\times2$ matrix has one positive and one negative
eigenvalue; its trace norm is their gap. Its sign is its traceless
part divided by half this gap. This proves that $R=\|A_{\rm raw}\|_1$
and $S=\operatorname{sign}(A_{\rm raw})$ are exactly (32.9).
In particular $S^2=I_2$.
Propagation and the raw support are

$$
G_s(A_{\rm raw}\oplus(-m))
 =\epsilon\begin{pmatrix}u^2&u\\u&1\end{pmatrix}\oplus0,
\qquad
\operatorname{Tr}((G_s(A_{\rm raw}\oplus(-m)))_+)
 =\chi(1+u^2).
\tag{33.6}
$$

The raw objective minus support is therefore exactly $P(u)$.
Its normalized dual quotient is $P(u)/(R+m)$.
The identity

$$
2P'Q-PQ'=J
\tag{33.7}
$$

follows by multiplying $P=Au^2+Bu+C$ and $Q=u^4+Du^2+E$:
the degree-five terms cancel, the degree-four term is $-2Bu^4$,
the degree-three term is $(2AD-4C)u^3$, the degree-two term
cancels, and the remaining terms are $(4AE-2CD)u+2BE$.
Thus the unsquared filter (32.8) says exactly that this quotient is
stationary. The inverse in (32.9), using $a^2-b^2=s$, gives

$$
G_s(K)=H\oplus t,qquad E_p-G_s(K)=tS\oplus(-t).
\tag{33.8}
$$

These identities are algebraic and do not assume that $K$ is an effect.
To obtain that fact without a hidden determinant test, let
$Z(u)=A_{\rm raw}(u)\oplus(-m)$ and $\sigma(u)=\chi(1+u^2)$.
At the retained root the value identity and stationarity read

$$
\operatorname{Tr}(Z E_p)-\sigma-t\|Z\|_1=0,\qquad
\operatorname{Tr}(Z'E_p)-\sigma'-t(\|Z\|_1)'=0,
\tag{33.9}
$$

where $t$ is held fixed in the second expression. For an invertible
Hermitian matrix with one eigenvalue of each sign,
$(\|A\|_1)'=\operatorname{Tr}(\operatorname{sign}(A)A')$.
One can obtain this formula by differentiating each simple eigenvalue:
if $Av=\lambda v$ and $v^\dagger v=1$, differentiation and left
multiplication by $v^\dagger$ give $\lambda'=v^\dagger A'v$;
subtract the negative eigenvalue derivative from the positive one.
Using this formula, (33.8), and self-adjointness of $G_s$, (33.9)
becomes

$$
\operatorname{Tr}(G_s(Z)K)=\sigma,qquad
\operatorname{Tr}(G_s(Z')K)=\sigma'.
\tag{33.10}
$$

For $s<0$, substitute (33.6) and its derivative to obtain

$$
u^2x+2uz+y=0,qquad ux+z=0,qquad
z=-ux,qquad y=u^2x.
\tag{33.11}
$$

Thus $K_2=x\left(\begin{smallmatrix}1&-u\\-u&u^2\end{smallmatrix}\right)$
has eigenvalues $0,x(1+u^2)$. For $s>0$, the same substitution gives

$$
u^2(1-x)-2uz+1-y=0,qquad u(1-x)-z=0,qquad
z=u(1-x),\quad 1-y=u^2(1-x).
\tag{33.12}
$$

The complement $I_2-K_2$ then has eigenvalues
$0,(1-x)(1+u^2)$. These are precisely the scalar filters (32.10)
needed for effect feasibility; the scalar $d$ is also filtered there.
Equation (33.10) is already the raw support equality.
The norm of $Z$ is $R+m$, and (33.8) pairs with it as $t(R+m)$.
This proves (33.1). Here $Q>0$, $R+m>0$, $u>0$ and $s\ne0$
prove every denominator assertion. Squaring the stationary equation
produces exactly $\mathcal P_{\rm M}$, but (32.8) retains the
unsquared equation, so no implication used the squared equation alone.

For D+, the explicit upper block has trace $1+t$ and determinant $t$.
Indeed its determinant is

$$
(1-at/b)t/b-at(b-t)/b^2=t.
\tag{33.13}
$$

Its eigenvalues are therefore $1,t$. For D− the trace is $t$ and
its determinant is zero, since $xy=z^2=a(1-t)(t-a)/b^2$.
Its eigenvalues are $0,t$. Thus both prescribed $K$ are effects,
and their matrices $Q$ in (32.15) are rank-one projections: the
one-eigenspace projection for D+, the kernel projection for D−.
The radicands are positive on the stated open intervals, so $z\ne0$
and $Q_{01}\ne0$. In D+ it has the sign of $z$, namely positive;
in D− it has the sign of $-z$, also positive. Consequently
$\kappa>0$ in D+ and $\kappa<0$ in D−.

In both branches the bottom image is $t$ and the upper image has trace
one. Put $h_e=ay+bd$. The upper residual is
$\left(\begin{smallmatrix}h_e-q&\ell\\\ell&q-h_e\end{smallmatrix}\right)$.
In D+, $h_e=at/b$, and expansion gives

$$
 b^2\bigl((h_e-q)^2+c^2-t^2\bigr)+s^2R_0(t)=L_0(t).
\tag{33.14}
$$

In D−, $h_e=(at-s)/b$ and $h_e-q=(at-h_0)/b$; the corresponding
expansion is

$$
 b^2\bigl((h_e-q)^2+c^2-t^2\bigr)+s^2R_1(t)=L_1(t).
\tag{33.15}
$$

For clarity the first expansion has quadratic coefficient
$a^2-b^2-as^2=s-as^2$, linear coefficient
$ab(s^2-2q)$, and constant $b^2(q^2+c^2)=b^2q$.
The second has the same quadratic coefficient, linear coefficient
$a(s^2(1+a)-2h_0)$, and constant
$h_0^2+b^2pq-s^2a^2$. These are the displayed $L_i$.
The quartic and $L_i>0$ are equivalent to
$L_i=2bc\tau\sqrt{R_i}$. Since $sz=\tau\sqrt{R_i}/b$,
(33.14) or (33.15) then gives
$(h_e-q)^2+(c-sz)^2=t^2$. This proves $S^2=I_2$ and the residual
$tS\oplus(-t)$ without an irreversible squaring.

The definitions of $h$ and $\mu$ make the propagated raw upper block
exactly $\kappa Q$: the $00$ and $11$ entries are specified by those
two equations, and its off-diagonal is $s\ell/t=\kappa Q_{01}$.
The propagated scalar is $\zeta$. For D+, the positive upper
support is attained because $K_2Q=Q$ and $\kappa>0$, and $d=0$
attains the scalar support because $\zeta\le0$. For D− the upper
support is zero and attained because $K_2Q=0$ and $\kappa<0$;
$d=1$ attains the scalar support because $\zeta\ge0$.
The contact normalization (32.1) completes (33.1).
All denominators are nonzero: $a,b,s,t,Q_{01}$ are nonzero,
$1-t>0$, and $2+\mu\ge2$.

For R−, let $v=(u,1)^{\mathsf T}$ and
$Z=vv^{\mathsf T}\oplus(-b/a)$. Its trace norm is
$u^2+1+b/a=u^2+1/a=N$. Its propagation is

$$
G_s(Z)=M\oplus0,qquad
M=\begin{pmatrix}u^2&su\\su&s/a\end{pmatrix},qquad
\det M=s(1/a-s)u^2<0.
\tag{33.16}
$$

The eigenvalue gap of $M$ is $R=\sqrt Q>0$. The upper block in
(32.21) is exactly its positive spectral projection: for a symmetric
matrix with diagonal difference $d_0$ and off-diagonal $z_0$, this
projection is
$\frac12\left(I_2+\left(\begin{smallmatrix}d_0&2z_0\\2z_0&-d_0\end{smallmatrix}\right)/
\sqrt{d_0^2+4z_0^2}\right)$, which here gives $d_0=u^2-s/a$
and $z_0=su$.
Thus $K_2$ is an effect independently of the scalar filter.
Its propagated upper support is $(u^2+s/a+R)/2$. Subtracting that
from $v^{\mathsf T}E_2v$ gives $(P-R)/2$, so the raw value identity
is exactly $\operatorname{Tr}(ZE_p)-\operatorname{Tr}(M_+)=tN$.
Also $by+ad=t$ by definition of $d$.

The derivative of $(P-R)/(2N)$ vanishes exactly when (32.20) holds.
In detail,

$$
P'N-2uP=L,qquad Q'N-4uQ=J,qquad
2R\bigl((P-R)'N-(P-R)N'\bigr)=2RL-J.
\tag{33.17}
$$

The first two identities follow by multiplying the polynomials in
(32.19). In the last identity the left side uses $N'=2u$ and
$R'=Q'/(2R)$. Differentiate the raw value identity with $t$ held
fixed, using the positive eigenvalue derivative formula just proved.
If $T_2=E_2-(G_s(K))_2$, the value and derivative identities give

$$
v^{\mathsf T}T_2v=t(u^2+1),qquad
(1,0)T_2v=tu.
\tag{33.18}
$$

Here the first equality subtracts the scalar contribution $(b/a)t$
from $tN$. For the second, $Z'$ has upper block
$e_0v^{\mathsf T}+ve_0^{\mathsf T}$, where $e_0=(1,0)^{\mathsf T}$,
and no scalar derivative, while $N'=2u$.
Since $v_1=1$, these two equalities imply $T_2v=tv$.
Trace preservation of $G_s$, $\operatorname{Tr}K_2=1$ and bottom
image $t$ give $\operatorname{Tr}T_2=t-d$. Its other eigenvalue
is therefore $-d$. The filter $0\le d\le t$ gives both effect
feasibility and residual norm $t$, including $d=t$.
The support is attained by the positive projection and zero scalar
propagation; pairing with $Z/N$ gives $t$. This proves (33.1) for
R−. Its denominators $R,N,a$ are strictly positive.

For R+, $\alpha=4a>0$, and $q(1-s^2)>0$.
The quadratic in (32.24) has roots of opposite signs, and its
discriminant is strictly positive. Its positive root is exactly the
one displayed there. Substituting $u=(t+q)/c$ into this quadratic
and using $c^2=pq$ gives the two identities

$$
t=cu-q,qquad \alpha tu=c+(q-s^2)u.
\tag{33.19}
$$

For example, after multiplying the second by $c$, its difference
from zero is
$\alpha t(t+q)-c^2-(q-s^2)(t+q)$, precisely the quadratic.
The upper $K_2$ in (32.25) fixes $(1,su)^{\mathsf T}$:
its first row gives $1$ on that vector and its second gives $su$.
Its other eigenvalue is its trace minus one, namely $\lambda$.
The filter $0\le\lambda\le t<1/2$ therefore proves it is an effect.
Since $d=0$ and $by=t$, the bottom residual is $-t$.
Writing $T_2=E_2-(G_s(K))_2$, its entries are

$$
\begin{aligned}
(T_2)_{00}&=-q+s^2u^2(1-y),\\
(T_2)_{01}&=c-s^2u(1-y),\\
(T_2)_{11}&=q-ay.
\end{aligned}
\tag{33.20}
$$

The first row applied to $(1,u)^{\mathsf T}$ is $cu-q=t$.
The second row applied to it is
$c+(q-s^2)u-(a-s^2)uy$. Since $y=t/b$ and
$\alpha=1+(a-s^2)/b$, (33.19) makes this $tu$.
Thus $t$ is an upper residual eigenvalue. Its trace is
$1-x-ay=t-\lambda$, so its other eigenvalue is $-\lambda$.
The scalar filter proves the full residual norm is $t$.

Let $Z=\left(\begin{smallmatrix}1&u\\u&u^2\end{smallmatrix}\right)
\oplus(-\mu)$. Here $\mu\ge0$ by (31.2), and
$\|Z\|_1=1+u^2+\mu=1+\alpha u^2=N$.
Its propagation is

$$
G_s(Z)=\begin{pmatrix}1&su\\su&s^2u^2\end{pmatrix}
 \oplus\left(-\frac{s(1-as)u^2}{b}\right).
\tag{33.21}
$$

The upper block is positive rank one and its range is fixed by $K_2$.
The scalar is strictly negative, and $d=0$ attains its support.
The upper input witness is positive rank one on the residual
eigenvector $(1,u)^{\mathsf T}$; the negative scalar pairs with
$-t$. The raw pairing is consequently $t(1+u^2+\mu)=tN$.
Normalization gives (33.1). All denominators $a,b,c,\alpha,N$
are strictly positive.

The coefficient formulas (31.8), (32.6), (32.12), (32.18) and (32.22)
are obtained by the displayed finite polynomial products; their
nonzero leading coefficients and the intervals of the definitions
establish the asserted finite degree and root counts. None of the
certificate arguments differentiated an algebraic root or divided
by a derivative. They therefore apply to every retained multiple root
and to every non-strict boundary filter in Definition 32.7.
The conditional case is Theorem 31.3 and the balanced case is
Theorem 30.3. This completes the certificate proof. $\square$

## 追加锚（本行以下为增补区）
