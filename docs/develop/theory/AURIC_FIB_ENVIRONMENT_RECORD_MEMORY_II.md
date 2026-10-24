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
