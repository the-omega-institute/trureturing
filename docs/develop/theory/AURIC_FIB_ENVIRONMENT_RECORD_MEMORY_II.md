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
[BKKDOI]. Its exact algebra-correction criterion has a different objective from
(31.4). The elementary single-task interface used here is the one in
[BKKNOTE]. The fixed-effect loss (31.4) is also distinct from the
worst-case entanglement
fidelity in Bény–Oreshkov, *General conditions for approximate quantum
error correction and near-optimal recovery channels*, Theorem 1,
[arXiv:0907.5391v4](https://arxiv.org/html/0907.5391v4).
The approximate algebra-correction estimates in Bény, *Conditions for
the approximate correction of algebras*, Theorem 3.2,
[arXiv:0907.4207v1](https://arxiv.org/html/0907.4207v1), use a diamond
and completely bounded norm criterion with an auxiliary identity factor.
No equality of (31.4) with either of these different objectives is
assumed. The additional
branch formulas and spectral classification below are repo-derived
from (31.3) and finite-dimensional norm duality. No global literature
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
G_s(K)=H\oplus t,\qquad E_p-G_s(K)=tS\oplus(-t).
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
\operatorname{Tr}(G_s(Z)K)=\sigma,\qquad
\operatorname{Tr}(G_s(Z')K)=\sigma'.
\tag{33.10}
$$

For $s<0$, substitute (33.6) and its derivative to obtain

$$
u^2x+2uz+y=0,\qquad ux+z=0,\qquad
z=-ux,\qquad y=u^2x.
\tag{33.11}
$$

Thus $K_2=x\left(\begin{smallmatrix}1&-u\\-u&u^2\end{smallmatrix}\right)$
has eigenvalues $0,x(1+u^2)$. For $s>0$, the same substitution gives

$$
u^2(1-x)-2uz+1-y=0,\qquad u(1-x)-z=0,\qquad
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
G_s(Z)=M\oplus0,\qquad
M=\begin{pmatrix}u^2&su\\su&s/a\end{pmatrix},\qquad
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
P'N-2uP=L,\qquad Q'N-4uQ=J,\qquad
2R\bigl((P-R)'N-(P-R)N'\bigr)=2RL-J.
\tag{33.17}
$$

The first two identities follow by multiplying the polynomials in
(32.19). In the last identity the left side uses $N'=2u$ and
$R'=Q'/(2R)$. Differentiate the raw value identity with $t$ held
fixed, using the positive eigenvalue derivative formula just proved.
If $T_2=E_2-(G_s(K))_2$, the value and derivative identities give

$$
v^{\mathsf T}T_2v=t(u^2+1),\qquad
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
t=cu-q,\qquad \alpha tu=c+(q-s^2)u.
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

## 34. Nonemptiness and exhaustion of the algebraic prescription

**Theorem 34.1 (No missing populations, witness ranks or endpoint branches).**
For every $0<p<1$ and every finite integer $n\ge2$, either the conditional
filter $y_0\le t_0$ holds or at least one family P, M, D or R has a
retained root. This includes the exceptional value $s=-1/2$, scalar
endpoints and all cross-family transition cases. Consequently Definition
32.7 is well-defined on its whole stipulated domain.

Proof. First produce a primal optimum and a supporting functional
without any spectral-rank assumption. The real block effect interval
is compact convex, and $G_s$ is linear, so its image is compact convex.
The same value as the complex problem is attained there: entrywise
conjugation preserves the effect interval and $G_s$, fixes $E_p$, and
averaging a matrix with its conjugate cannot increase the operator norm
of its residual. Pinching removes the other two coherences by the
entire-image identity (31.3).

Write $t$ for this distance and $K=K_2\oplus d$ for a real attaining
effect, with $K_2=\left(\begin{smallmatrix}x&z\\z&y\end{smallmatrix}\right)$.
Then

$$
0<t<1/2.
\tag{34.1}
$$

For strict positivity, distance zero would give $by+ad=0$.
Since $a,b>0$ and $y,d\ge0$, this forces $y=d=0$.
Positivity of $K_2$ then forces $z=0$, contradicting the target
coherence $c>0$.
For the strict upper bound, choose any $0<\delta<1$.
The map $G_s$ is invertible on the real block vector space:
its coherence factor is $s\ne0$ and the population determinant
is $a^2-b^2=s\ne0$. Let $L=G_s^{-1}(E_p-\delta I_3)$.
For sufficiently small $\lambda>0$, the finite Hermitian matrix
$I_3/2+\lambda L$ is an effect. Its image is
$I_3/2+\lambda(E_p-\delta I_3)$, since $G_s(I_3)=I_3$.
The residual eigenvalues are
$1/2-\lambda(1-\delta)$ on $v_p$ and
$-1/2+\lambda\delta$ on its orthogonal complement.
All absolute values are strictly less than $1/2$ for sufficiently
small positive $\lambda$. This inverse proves (34.1) only and is
not a candidate in the finite prescription.

Finite-dimensional separation of the attainable image from the open
operator-norm ball of radius $t$ about $E_p$ supplies a nonzero
Hermitian supporting functional. Dividing by its dual norm gives
$Y$ with $\|Y\|_1=1$ and

$$
\begin{aligned}
t&=\operatorname{Tr}(YE_p)-\operatorname{Tr}((G_s(Y))_+),\\
\operatorname{Tr}(G_s(Y)K)&=\operatorname{Tr}((G_s(Y))_+),\\
\operatorname{Tr}(Y(E_p-G_s(K)))&=t.
\end{aligned}
\tag{34.2}
$$

One may see the first equality directly from separation: the infimum
of $\operatorname{Tr}(YX)$ on that open ball is
$\operatorname{Tr}(YE_p)-t\|Y\|_1$, and it bounds the support of the
attainable image from above. The reverse inequality is the elementary
norm bound evaluated at an attaining $K$, so both bounds are equal.
The last two equalities follow because each inequality in
$\operatorname{Tr}(YE_p)-\operatorname{Tr}((G_s(Y))_+)
\le\operatorname{Tr}(Y(E_p-G_s(K)))\le t$
is then an equality.

The support function is convex and the trace norm is convex. Averaging
with the $W$ pinching and then with entrywise conjugation preserves
$\operatorname{Tr}(YE_p)$ and cannot increase the support or norm.
The resulting real block witness has dual value at least $t$ and
norm at most one. The universal dual bound and $t>0$ force its norm
to be one and its value to be $t$; otherwise rescaling improves that
bound beyond the optimum. Thus such a witness can be chosen real block.
If its third scalar were positive, replacing that scalar by zero would
subtract a positive semidefinite matrix from its propagation and hence
not increase its support, while strictly reducing its trace norm and
leaving its target pairing fixed. Rescaling would again contradict
optimality. We can therefore write

$$
Y=A\oplus(-\mu),\qquad A=A^{\mathsf T}\in M_2(\mathbb R),\quad \mu\ge0.
\tag{34.3}
$$

Changing $A_{01}$ to its negative preserves its trace norm and its
propagated support, by conjugation with $\operatorname{diag}(1,-1)$
on the upper block. It increases its target pairing if $A_{01}<0$.
We may and do take $A_{01}\ge0$.

In fact

$$
A_{01}>0.
\tag{34.4}
$$

Here is the full exclusion of zero coherence. If $A$ is diagonal,
write $A_{00}=r_0$, $A_{11}=v_0$. Its unnormalized dual numerator is

$$
r_0p-(r_0)_++v_0q-(av_0-b\mu)_+-(bv_0-a\mu)_+.
\tag{34.5}
$$

For $r_0\ne0$, the first two terms have strictly negative sum:
it is $-qr_0$ if $r_0>0$ and $pr_0$ if $r_0<0$.
Removing this entry increases the positive numerator and reduces the
norm $|r_0|+|v_0|+\mu$, contradicting optimality. Thus $r_0=0$.
A positive value also forces $v_0>0$, since otherwise the remaining
target pairing is nonpositive. Scale $v_0=1$ and write the rescaled
negative scalar as $-\nu$, $\nu\ge0$. Its quotient is

$$
f(\nu)=\frac{q-(a-b\nu)_+-(b-a\nu)_+}{1+\nu}.
\tag{34.6}
$$

For $s<0$ the breakpoints are $a/b<b/a$. On the first interval the
numerator is $-p+\nu$, with positive quotient derivative
$(1+p)/(1+\nu)^2$. On the middle interval the numerator is
$q-b+a\nu$, with derivative $p/(1+\nu)^2>0$.
Beyond $b/a$ the quotient is $q/(1+\nu)$, strictly decreasing.
The unique maximizer is $\nu=b/a$, with value $aq$.
For $s>0$, the breakpoints are $b/a<a/b$; the first derivative is
the same, the middle numerator is $q-a+b\nu$ with derivative
$p/(1+\nu)^2>0$, and the final derivative is negative.
The unique maximizer is $\nu=a/b$, with value $bq$.

If a zero-coherence witness were optimal, (34.6) would have to be
at its unique maximum: every diagonal competitor is also a permitted
dual witness. For $s<0$ this propagation has upper $ee$ entry
$s/a<0$, upper $00$ entry zero, and scalar zero.
Support at $K$ forces $y=0$, hence $z=0$. Equality in the
trace/operator-norm bound forces $e$ to be an upper residual
eigenvector for eigenvalue $t$, since the upper witness is
$|e\rangle\langle e|$. Its off-diagonal residual entry would have
to vanish, contradicting $c>0$.
For $s>0$, its propagated upper block is zero and its scalar is
$-s/b<0$, so support forces $d=0$. The same residual eigenvector
condition, with $t=bq$, requires $ay=q-t=aq$ and $sz=c$;
thus $y=q$ and $z=c/s$. Positivity of $K_2$ and $I_2-K_2$ gives

$$
x\ge z^2/q=p/s^2,\qquad 1-x\ge z^2/p=q/s^2.
\tag{34.7}
$$

Their sum says $1\ge1/s^2$, impossible since $|s|<1$.
This proves (34.4).

The upper block $A$ cannot be negative semidefinite: its target
pairing would be nonpositive and its support nonnegative, whereas
$t>0$. It cannot be positive definite either. To justify the relevant
norm-equality implication, diagonalize $A$. For a positive eigenvector
with weight $\lambda>0$, its contribution to
$\operatorname{Tr}(A T_2)\le t\operatorname{Tr}|A|$ is bounded by
$\lambda t$, where $T_2$ is the upper residual and
$-tI_2\le T_2\le tI_2$. Equality of the total sum forces equality
for every nonzero weight. A positive semidefinite matrix with zero
quadratic form on a vector annihilates that vector; apply this to
$tI_2-T_2$. Negative weights similarly force eigenvalue $-t$.
If $A$ were positive definite, both upper residual eigenvalues would
be $t$, and the upper image would be $E_2-tI_2$, which is not positive
semidefinite. Thus the only possibilities are

$$
\begin{cases}
A\text{ indefinite},& T_2=t\operatorname{sign}(A),\\
A\text{ positive of rank one},&T_2v=tv\text{ on }\operatorname{ran}A.
\end{cases}
\tag{34.8}
$$

In the second case both components of its range vector are nonzero
by (34.4), and they have the same sign. Put

$$
r=by+ad\ge0,\qquad
M=\begin{pmatrix}A_{00}&sA_{01}\\sA_{01}&aA_{11}-b\mu\end{pmatrix},\qquad
\zeta=bA_{11}-a\mu.
\tag{34.9}
$$

These are the bottom image and the upper and scalar parts of $G_s(Y)$.
If $\mu>0$, norm equality in the scalar coordinate forces $r=t$.
If $A$ is indefinite, $T_2$ has trace zero, so trace preservation gives

$$
\operatorname{Tr}K_2+d=1+r.
\tag{34.10}
$$

The off-diagonal of $M$ is nonzero. Support equality says that $K_2$
is one on its positive eigenspaces, zero on its negative eigenspaces,
and is an effect on its kernel. Indeed in an eigenbasis of $M$,
$\operatorname{Tr}(MK_2)\le\sum_{\lambda_j(M)>0}\lambda_j(M)$;
equality forces the corresponding diagonal entries of $K_2$ to be
one or zero, respectively. Positivity of $K_2$ and $I_2-K_2$ then
annihilates their cross entries to such a coordinate, so this is also
a statement about their whole eigenspaces.

The upper effect is neither zero nor $I_2$. In the indefinite case,
$K_2=0$ would give $d=1+r$ by (34.10), incompatible with $d\le1$
and $r=ad>0$ when $d=1$. The case $K_2=I_2$ gives
$2+d=1+r$, impossible since $r\le t<1/2$.
For rank-one positive $A$, necessarily $\mu>0$: if $\mu=0$, the
whole witness is positive, so its support is at least its pairing with
$G_s(I_3)=I_3$, namely $\operatorname{Tr}Y$, and
$\operatorname{Tr}(YE_p)\le\operatorname{Tr}Y$, giving no positive
dual value. Then $r=t$. The case $K_2=0$ contradicts $M_{00}=A_{00}>0$.
If $K_2=I_2$, the upper residual trace is $t-1-d$, so its eigenvalue
other than $t$ is $-1-d$, outside the permitted interval.

It follows that $K_2$ is either a rank-one projection, or has
eigenvalues $0,\lambda$ with $0<\lambda<1$, or has eigenvalues
$1,\lambda$ with $0<\lambda<1$. In the latter two cases $M$ is
respectively negative rank one or positive rank one. The projection
case selects the larger-eigenvalue direction of $M$, including a
zero larger eigenvalue when $M$ is negative rank one. Its
coherence has the sign of $M_{01}$, namely $\epsilon$, and is nonzero:
the projection's off-diagonal equals $M_{01}$ divided by the
strictly positive eigenvalue gap.

Suppose first that $A$ is indefinite and $\mu=0$.
A negative-rank-one $M$ has $aA_{11}<0$, hence $\zeta=bA_{11}<0$
and $d=0$. But (34.10) would then give
$\operatorname{Tr}K_2=1+r\ge1$, excluding eigenvalues $0,\lambda$
with $\lambda<1$. A positive-rank-one $M$ has $A_{11}>0$,
so $\zeta>0$ and $d=1$. It would give
$\operatorname{Tr}K_2=r\le t<1/2$, excluding eigenvalues $1,\lambda$.
Therefore $K_2$ is a projection. Its trace in (34.10) yields $d=r$,
and $r=by+ad$ then yields $d=y$. Nonzero projection coherence gives
$0<y<1$, so scalar support forces $\zeta=0$, hence $A_{11}=0$.

Write $w=\sqrt{y(1-y)}$, $\ell=c-\tau w$ and $\Delta=y-q$.
The upper residual is
$\left(\begin{smallmatrix}\Delta&\ell\\\ell&-\Delta\end{smallmatrix}\right)$.
Its sign equals $\operatorname{sign}(A)$; since $A_{01}>0$,
this implies $\ell>0$. The equation $A_{11}=0$ and equality in
(34.8) give, up to a positive scalar,

$$
A=\begin{pmatrix}2\Delta&\ell\\\ell&0\end{pmatrix}.
\tag{34.11}
$$

For its propagation to support the projection with direction
$(\sqrt{1-y},\epsilon\sqrt y)^{\mathsf T}$, the diagonal difference
must equal its off-diagonal divided by $\epsilon w$ times $1-2y$.
This is $2\Delta w=\tau\ell(1-2y)$, precisely the unsquared
stationarity equation (31.11). Theorem 31.3 therefore makes $y=y_0$
and the upper norm $t=t_0$. The bottom residual has magnitude $y$,
so feasibility of the actual optimum gives $y_0\le t_0$.
This is exactly the conditional pair, with the equality boundary retained.

Next suppose $A$ is indefinite and $\mu>0$; then $r=t$.
If $K_2$ is a projection, (34.10) yields $d=t$ and the bottom
image equation yields $y=t$. Thus
$x=1-t$ and $z=\epsilon\sqrt{t(1-t)}$.
Its upper residual square is $t^2I_2$, which by (33.3) gives
$V=2c\tau\sqrt{t(1-t)}>0$, the P quartic and its unsquared filter.
Scale the raw witness so $A=hI_2+S$ with $S=T_2/t$;
indefiniteness gives $-1<h<1$.
Since $0<d=t<1$, scalar support forces $\zeta=0$ and
$\mu=(b/a)(h-k)$. The projection's eigenvector condition for the
upper propagation is the diagonal-difference equation in (33.4).
Solving its coefficient $b/a>0$ for $h$ gives exactly (32.3).
The support signs give $|T|\le\delta$. Thus this optimum is a
retained P root, including when one support eigenvalue is zero.

Continue with indefinite $A$, $\mu>0$ and a free upper eigenvalue.
If $0<d<1$, scalar support gives $\zeta=0$ and
$\mu=(b/a)A_{11}>0$, so $A_{11}>0$.
Consequently $M_{11}=(s/a)A_{11}$, and the sign of the rank-one
matrix $M$ is $\epsilon$. Put
$\kappa_0=\tau A_{11}/a>0$ and $u=aA_{01}/A_{11}>0$.
Dividing the entire raw witness by $\kappa_0$ gives

$$
M=\epsilon\begin{pmatrix}u^2&u\\u&1\end{pmatrix},\qquad
A=\begin{pmatrix}\epsilon u^2&u/\tau\\u/\tau&a/\tau\end{pmatrix},\qquad
\mu=b/\tau
\tag{34.12}
$$

in this rescaled notation. These are exactly M's raw matrices.
The normalized dual quotient along this family is $P(u)/(\sqrt Q+m)$
by (33.5)–(33.6). It is a smooth function of $u>0$, and the actual
optimum maximizes it there because every member is a legitimate
normalized dual witness. Its derivative vanishes at the actual finite
$u$, so (33.7) gives the unsquared equation (32.8).
The value is positive and below $1/2$ by (34.1), and the inverse of
its residual is exactly (32.9). Actual feasibility implies the scalar
filters (32.10), by the identities (33.11)–(33.12).
Thus this optimum is a retained M root.

If the free-upper-eigenvalue case has a scalar endpoint, (34.10)
leaves only $d=0$ with upper eigenvalues $1,t$, or $d=1$ with
upper eigenvalues $0,t$. For eigenvalues $1,\lambda$ it says
$\lambda=t-d$, so the endpoint $d=1$ is impossible.
For eigenvalues $0,\lambda$ it says $\lambda=1+t-d$, so the
endpoint $d=0$ is impossible.
In the first remaining case $M$ is positive rank one, hence
$M_{11}>0$. From $d=0$ its scalar satisfies $\zeta\le0$, which
implies $\mu\ge(b/a)A_{11}$. Positivity of $M_{11}$ forces
$A_{11}>0$, and then
$M_{11}\le(s/a)A_{11}$ excludes $s<0$.
Thus this is D+. The bottom equation gives $y=t/b$ and the trace
gives $x=1-at/b$; the determinant $t$ gives
$z=\epsilon\sqrt{at(b-t)}/b$. Nonzero coherence forces $t<b$.
In the second case $M$ is negative rank one, so $M_{11}<0$.
From $d=1$, $\zeta\ge0$ gives $\mu\le(b/a)A_{11}$ and
$A_{11}>0$, whence $M_{11}\ge(s/a)A_{11}$ excludes $s>0$.
Thus this is D−. The bottom and trace equations give
$y=(t-a)/b$, $x=a(1-t)/b$, and determinant zero gives the
stated $z$; its nonzero coherence forces $t>a$.
In either case the residual gives $\ell>0$, (33.14)–(33.15) give
the quartic with $L_i>0$, and writing $A=hI_2+S$ reconstructs
$\kappa,h,\mu,\zeta$ exactly as (32.15). Actual witness and support
conditions are precisely (32.16). These endpoint optima are retained D
roots. This exhausts the indefinite case.

It remains to treat rank-one positive $A$; we already know $\mu>0$
and $r=t$. First suppose $K_2$ is a projection. Its trace is one,
so the upper residual trace is $t-d$. Its eigenvalue on
$\operatorname{ran}A$ is $t$, hence its other eigenvalue is $-d$.
Thus $0\le d\le t<1/2$.
The possibility $d=0$ requires special attention. It would make the
upper residual positive semidefinite, so the positive upper image $H$
would satisfy $0\le H\le E_2$ and therefore have rank at most one.
For a projection upper effect with nonzero coherence and $d=0$,

$$
\det H=(a-s^2)y(1-y).
\tag{34.13}
$$

Here $0<y<1$, so (31.2) forces $s=-1/2$ and $a=1/4$.
At that value put $T=q+ap>0$. Since $H$ has range equal to that of
$E_2$, its entries give the unique projection direction and image

$$
v_K=\frac{(\sqrt{ap},-\sqrt q)^{\mathsf T}}{\sqrt T},\qquad
K_2=v_Kv_K^{\mathsf T},\qquad H=(a/T)E_2.
\tag{34.14}
$$

To verify the coefficients, $x=1-y$ and $ay$ must be in ratio $p:q$,
so $y=q/T$, $x=ap/T$; the projection coherence has negative sign
and magnitude $\sqrt{apq}/T$. Multiplying by $s=-1/2$ gives
$a c/T$, as required. The scalar image and nonzero residual eigenvalue
are both $bq/T$, so the positive residual direction forces
$A$ to be a positive multiple of $E_2$. Scale $A=E_2$.
Then
$M=\left(\begin{smallmatrix}p&-c/2\\-c/2&aq-b\mu\end{smallmatrix}\right)$.
For the vector in (34.14) to be its supporting projection direction,
it must be an eigenvector of $M$. The first row gives eigenvalue
$p+q=1$. In the second row, divide by $\sqrt q$ and use
$s\sqrt a=-a$ to obtain
$-ap-aq+b\mu=-1$, that is $b\mu=-b$ and $\mu=-1$.
This contradicts $\mu\ge0$. Thus $d=0$ is impossible even at the
exceptional value, and

$$
0<d\le t<1/2.
\tag{34.15}
$$

The scalar is now interior, so $\zeta=0$ and
$\mu=(b/a)A_{11}$. Since $A$ is positive rank one with nonzero
coherence, $A_{01}^2=A_{00}A_{11}$ and $A_{00},A_{11}>0$.
It follows that

$$
\det M=s(1/a-s)A_{00}A_{11}.
\tag{34.16}
$$

The factor $1/a-s$ is positive. If $s>0$, $M_{00}>0$ and this
positive determinant make $M$ positive definite, forcing $K_2=I_2$,
already excluded. Hence $s<0$, and $M$ is indefinite.
Scale $A_{11}=1$ and put $u=\sqrt{A_{00}}>0$.
Then $A=\left(\begin{smallmatrix}u^2&u\\u&1\end{smallmatrix}\right)$,
$\mu=b/a$, and its propagation and support are exactly (33.16).
The normalized quotient is $(P-\sqrt Q)/(2(u^2+1/a))$ of R−.
This smooth dual family has an interior stationary point at the actual
finite $u$, giving (32.20) by (33.17). Its supporting projection is
uniquely (32.21), and $r=t$ fixes the scalar $d$ there.
The actual norm bound gives $0\le d\le t$, so every R− filter holds.
This is a retained R− root; the argument also covers $d=t$.

Finally suppose $A$ is positive rank one and the upper effect has a
free eigenvalue. Since $M_{00}=A_{00}>0$, a negative-rank-one $M$
is impossible, so $M$ is positive rank one and $K_2$ has eigenvalues
$1,\lambda$ with $0<\lambda<1$.
The upper residual trace is $t-d-\lambda$ and its other eigenvalue
is $-(d+\lambda)$. Thus $d+\lambda\le t<1/2$.
If $0<d<1$, scalar support would force
$\mu=(b/a)A_{11}$ and then (34.16) would be nonzero, contradicting
rank-one $M$. Therefore $d=0$.
Scale $A_{00}=1$, put $A_{11}=u^2$ and $A_{01}=u>0$.
The equation $\det M=0$ gives
$\mu=(a-s^2)u^2/b$. The scalar support condition for $d=0$ is

$$
\zeta=-s(1-as)u^2/b\le0.
\tag{34.17}
$$

Since $s\ne0$ and $1-as>0$, this forces $s>0$.
The normalized dual quotient of this family is

$$
f(u)=\frac{-q+2cu+(q-s^2)u^2}{1+\alpha u^2},\qquad \alpha=4a.
\tag{34.18}
$$

At its actual interior maximizing $u$, the equations $f(u)=t$ and
$f'(u)=0$ give
$c+(q-s^2)u=\alpha tu$ and then $t=cu-q$:
multiply the first equation by $u$ and subtract it from the value
identity to obtain the latter. Eliminating $u$ gives exactly
(32.24), whose unique positive root must therefore be this $t$.
Support fixes the vector $(1,su)^{\mathsf T}$ in the upper effect,
and $by=t$ fixes $y=t/b$. The two row equations then uniquely give
$z=su(1-y)$ and $x=1-s^2u^2(1-y)$. Thus these are exactly R+'s
entries. The residual bound gives $0\le\lambda\le t$, so it is a
retained R+ candidate.

The cases above exhaust (34.8) and the full spectral classification of
$M$. The exceptional scalar endpoint was excluded explicitly in
(34.13)–(34.15), rather than discarded by a division by $a-s^2$.
Every parameter $u$ obtained from an actual witness is finite and
strictly positive: the defining upper diagonal entries and coherence
are nonzero in its case. Thus $u=0$ or an infinite parameter cannot
represent an omitted optimal witness.

If the conditional filter fails, the first case cannot occur, so one
of P, M, D or R must have a retained root. At $p=1/2$, the separately
reused Theorem 30.3 already supplies the prioritized pair.
The classification used strict inequalities only for structural ranks
and for root intervals. When a free eigenvalue reaches zero or one,
it enters the projection case; when the scalar reaches zero or one,
it enters D; semidefinite upper-witness limits are the rank-one positive
case. All actual support and norm equalities in these cases obey the
non-strict filters, including multiple roots and support eigenvalues
zero. Consequently no transition is excluded by choosing an open
structural case, and nonemptiness holds on the entire domain. $\square$

## 追加锚（本行以下为增补区）

## 35. Exact all-density value and a same-qutrit decoder

**Theorem 35.1 (Total algebraic value for every population and finite horizon).**
For the fixed actual channel, task and resources of Definition 31.1,
Definition 32.7 selects a value $t$ and a pair $K,Y$ for every real
$0<p<1$ and finite integer $n\ge2$. With

$$
B=U_0KU_0^\dagger,\qquad
\mathcal D_B(X)=\operatorname{Tr}(BX)E_p
       +\operatorname{Tr}((I_3-B)X)\frac{I_3-E_p}{2},
\tag{35.1}
$$

one has

$$
\begin{gathered}
0\le K\le I_3,\quad 0\le B\le I_3,\quad Y=Y^\dagger,\quad
\|Y\|_1=1,\\
\eta_n(E_p)=t=\|(F^n)^\dagger(B)-E_p\|_{\rm op}
 =\operatorname{Tr}(YE_p)-\operatorname{Tr}((F^n(Y))_+),\\
\eta_n(E_p)=
\min_{\substack{\mathcal D:M_3(\mathbb C)\to M_3(\mathbb C)\\
                 \mathcal D\ {\rm CPTP}}}
\sup_{\rho\in\mathsf D(\mathbb C^3)}
\left|\operatorname{Tr}(E_p\mathcal D(F^n(\rho)))
             -\operatorname{Tr}(E_p\rho)\right|,\\
\sup_{\rho\in\mathsf D(\mathbb C^3)}
\left|\operatorname{Tr}(E_p\mathcal D_B(F^n(\rho)))
             -\operatorname{Tr}(E_p\rho)\right|=t.
\end{gathered}
\tag{35.2}
$$

All root choices and retained-root filters are exact as stated in
Definitions 31.2 and 32.2–32.7. At $p=1/2$ the selected statement is
exactly Definition 30.2 and Theorem 30.3. Otherwise it is the conditional
quartic when its filter holds, or a root in P, M, D or R as ordered in
Definition 32.7. Thus (35.2) is an existence and exactness theorem for
the finite prescription, not an assumption embedded in a definition.

The complementary projection $I_3-E_p$ has this same algebraic value,
by [ERM, Proposition 27.8][ERM], and the same decoder serves this
complementary binary pair. No common decoder for arbitrary collections
of prescribed tasks or different horizons is asserted. This supplies
the whole $r=0,pq>0$ quantitative boundary of [ERM, Definition 27.10][ERM];
the $p,q,r>0$ interior, retained-memory recovery and uniform recovery
over unbounded horizons remain outside the statement.

Proof. The balanced assertion is Theorem 30.3. The conditional assertion
is Theorem 31.3, including equality $y_0=t_0$. In all remaining cases
Theorem 34.1 supplies a retained root and Theorem 33.1 proves (33.1)
for every such root. The sets of roots are finite and nonempty in the
first selected family, so their least member exists. If several
families or several retained roots apply, each is bounded above and
below by its own matching global certificate, hence each value is
$\eta_n(E_p)$. This proves deterministic selection without relying on
uniqueness of the optimizer or on a numerical choice among roots.

For clarity, every denominator in the prescription has its own domain
justification. The common $a,b,c,\tau,s$ are nonzero by (31.1)–(31.2).
The conditional root has $w_0,\ell_0,t_0>0$ by Theorem 31.3.
For P, $0<t<1/2$ gives $w>0$, and its strict $\ell$ filter gives
$\delta>0$. For M, (33.5) gives $Q>0$ and $R+m>0$; its inverse uses
only the finite nonzero $s$. For D, the stated open interval makes its
radicand positive and $Q_{01}\ne0$, as proved following (33.13);
$t>0$ and $1-t>0$ justify the two projection denominators.
For R−, (33.16) gives $Q>0$, while $N=u^2+1/a>0$.
For R+, $\alpha,c,N>0$ and the discriminant in (32.24) is strictly
positive. Contact witnesses use $2+\mu\ge2$.
The balanced denominators and root isolation are exactly those of
Theorem 30.3. No root formula divides by $a-s^2$, a derivative, a
vanishing population, or an infinite-horizon parameter. The
exception $a-s^2=0$ was included in (34.13)–(34.15).
Neither $s=0$ nor the excluded population endpoints $p=0,1$ is evaluated.
These statements justify all finite formulas even at multiple roots,
zero support eigenvalues and the retained transition equalities.

Conjugation by $U_0$ preserves effect inequalities. Formula (35.1) is
exactly the reused decoder [ERM, (27.5)][ERM], with the two prepared
states $E_p$ and $(I_3-E_p)/2$. Its same-qutrit complete positivity and
trace preservation can also be verified explicitly. Write
$B=\sum_{j=1}^3 b_j|u_j\rangle\langle u_j|$ with orthonormal $u_j$
and $0\le b_j\le1$, and let $w_1,w_2$ be an orthonormal basis of
$\ker E_p$. The matrices

$$
L_j=\sqrt{b_j}\,|v_p\rangle\langle u_j|,\qquad
M_{kj}=\sqrt{(1-b_j)/2}\,|w_k\rangle\langle u_j|,\qquad
1\le j\le3,\quad 1\le k\le2
\tag{35.3}
$$

all act from $\mathbb C^3$ to $\mathbb C^3$.
Their adjoint products sum to
$\sum_j(b_j+1-b_j)|u_j\rangle\langle u_j|=I_3$.
Their Kraus sum is (35.1), since the first family prepares $E_p$
and the second prepares $(I_3-E_p)/2$ with the complementary
measurement weight. Thus $\mathcal D_B$ is CPTP on the same input
and output qutrit. The orthogonality of $v_p,w_1,w_2$ gives
$\mathcal D_B^\dagger(E_p)=B$.
Conversely, the adjoint of every permitted CPTP decoder is positive
and unital, so its image of $E_p$ is an effect.

For any Hermitian $T$ on the complex qutrit,

$$
\sup_{\rho\in\mathsf D(\mathbb C^3)}|\operatorname{Tr}(T\rho)|
   =\max_j|\lambda_j(T)|=\|T\|_{\rm op}.
\tag{35.4}
$$

The spectral theorem bounds every expectation between the two extreme
eigenvalues, and an eigenstate attains the largest absolute value.
Apply this to $T=(F^n)^\dagger(\mathcal D^\dagger(E_p))-E_p$.
The converse effect statement and the explicit realization of every
$B$ give the exact operational equality in (35.2). By (33.2) the
normalized input witness $Y$ supplies the same lower bound through
$F^n(Y)$, without any conjugation of the input functional.
These arguments retain all complex inputs and all complex effects;
real entries of the attaining pair are not an input-domain restriction.
The decoder is one fixed channel for the chosen $p,n$ and is independent
of the density matrix. Its unital adjoint also sends $I_3-E_p$ to
$I_3-B$, so [ERM, Proposition 27.8][ERM] gives the asserted
complementary value with this same channel. The parameter and resource
domains remain exactly those of (31.1) and (35.2). $\square$

## 追加锚（本行以下为增补区）

## 36. Interior residuals and real supporting functionals

**Definition 36.1 (Interior task and signed coordinates).**
Use the ordered orthonormal basis $(\xi,e,f)$, the actual channel
$F=\operatorname{Ad}_{U_0}\circ\Delta_W$, and the fair independent,
entirely erased chronological histories of [ERM, Definition 27.1][ERM].
For a finite integer $n\ge2$ put

$$
\begin{gathered}
s=(-1/2)^{n-1},\quad \alpha=(1+s)/2,\quad \beta=(1-s)/2,\\
p,q,r>0,\quad p+q+r=1,\quad m=1-r,\quad k=\sqrt{rm},\\
v=(\sqrt p,\sqrt q,\sqrt r)^{\mathsf T},\quad E=vv^{\mathsf T},\quad
u=p/m,\quad \nu=q/m,\quad c=\sqrt{pq},\\
a=(\sqrt p,\sqrt q)^{\mathsf T}/\sqrt m,\qquad
b=(-\sqrt q,\sqrt p)^{\mathsf T}/\sqrt m.
\end{gathered}
\tag{36.1}
$$

Here $u+\nu=1$; $a,b$ are orthonormal vectors in the fixed upper
plane. Their use to analyze a residual does not change the basis of
$G_s$. Throughout §§36–43, assume that the floor criterion
[ERM, (27.24)][ERM] fails. In particular $r\ne1/2$ and $k<\eta_n(E)$.
All radicals of positive quantities mean positive real radicals.
The original signed $s$, including $s=-1/2$ at $n=2$, is retained.
For a real block effect the existing image and forward identities are

$$
\begin{gathered}
K=K_2\oplus d,\quad K_2=\begin{pmatrix}x&z\\z&y\end{pmatrix},\quad
0\le K_2\le I_2,\quad 0\le d\le1,\\
G_s(K)=\begin{pmatrix}x&sz\\sz&\alpha y+\beta d\end{pmatrix}
                  \oplus(\beta y+\alpha d),\\
B=U_0KU_0^\dagger,\qquad
F^n(Y)=U_0G_s(\Delta_W(Y))U_0^\dagger.
\end{gathered}
\tag{36.2}
$$

These are [ERM, Proposition 27.2, (27.6)–(27.7)][ERM].
The optimization and its lower functional remain [ERM, (27.4)][ERM],
over all complex effects and all complex input density matrices.
The positive and negative parts of a Hermitian matrix are denoted by
$Y_+,Y_-$, so $Y=Y_+-Y_-$ and both parts are positive semidefinite.

**Theorem 36.2 (Extreme contacts and the real support bridge).**
A real minimizing block effect exists. Every such optimum has residual
$R=G_s(K)-E$ with spectrum

$$
(-t,h,t),\qquad t=\eta_n(E),\qquad k<t<1/2,\qquad 0\le h\le t.
\tag{36.3}
$$

There is a real symmetric $Y$ with $\|Y\|_1=1$ such that, writing
$H=G_s(\Delta_W(Y))$,

$$
\begin{gathered}
\operatorname{Tr}(HK)=\operatorname{Tr}(H_+),\qquad
-\operatorname{Tr}(YR)=t,\\
t=\operatorname{Tr}(YE)-\operatorname{Tr}((F^n(Y))_+).
\end{gathered}
\tag{36.4}
$$

Its positive part is supported on the $-t$ residual eigenspace and its
negative part on the $+t$ eigenspace. Both parts are nonzero. The
propagated block $H$ is nonzero.
If $h=t$, the image is, for one of the two signs of $e_0$,

$$
\begin{gathered}
e_0=\pm\sqrt{t^2-k^2}\ne0,\\
C_2=(m-e_0)aa^{\mathsf T}+tbb^{\mathsf T},\qquad C_{ff}=r+e_0,\\
w=A_0a+B_0f,\quad A_0=\sqrt{(t+e_0)/(2t)},\quad
B_0=\sqrt{(t-e_0)/(2t)},\quad R=tI_3-2tww^{\mathsf T}.
\end{gathered}
\tag{36.5}
$$

Conversely the displayed image has residual spectrum $(-t,t,t)$.

Proof. The real block effect interval is compact convex. Conjugation
averaging preserves its image and cannot increase distance to the real
$E$, giving the same minimum as the complex problem. At a positive
optimum both norm extremes must be active. If only the positive
extreme is active, replace $C=G_s(K)$ by $(1-\lambda)C$. Then
$R_{\rm new}=(1-\lambda)R-\lambda E$ has positive extreme at most
$(1-\lambda)t<t$, and its negative bound remains strict for small
$\lambda>0$. If only the negative extreme is active, use
$(1-\lambda)C+\lambda I_3$ and
$R_{\rm new}=(1-\lambda)R+\lambda(I_3-E)$. Both are feasible images.
Since $C\ge0$ and $E$ has rank one, a two-dimensional negative
subspace of $R$ would meet $v^\perp$, where its quadratic form is
nonnegative. Thus at most one eigenvalue is negative and $h\ge0$.

For the strict upper bound put $A=1-2r\ne0$ and
$D=A(aa^{\mathsf T}\oplus(-1))-bb^{\mathsf T}$.
The finite block inverse $L=G_s^{-1}(D)$ exists because $s\ne0$.
For sufficiently small $0<\varepsilon<1/2$, $I_3/2+\varepsilon L$
is an effect. In the orthonormal basis
$(v,\sqrt r\,a-\sqrt m\,f,b)$ its residual eigenvalues are

$$
\pm\sqrt{1/4-A^2\varepsilon(1-\varepsilon)},\qquad 1/2-\varepsilon,
\tag{36.6}
$$

all strictly within $(-1/2,1/2)$. The floor theorem supplies $t>k$.

Separate the compact convex attainable image from the open operator
norm ball of radius $t$ about $E$ in the real vector space of all
Hermitian matrices. Normalize the nonzero separating functional by
its dual trace norm. The infimum of $\operatorname{Tr}(YX)$ on this
ball is $\operatorname{Tr}(YE)-t\|Y\|_1$. Separation bounds the
attainable support above by this quantity; the norm bound evaluated
at an attaining $C$ gives the reverse inequality. Consequently both
inequalities in

$$
\operatorname{Tr}(YE)-\operatorname{Tr}(H_+)
 \le\operatorname{Tr}(Y(E-C))\le\|Y\|_1\|E-C\|_{\rm op}=t
\tag{36.7}
$$

are equalities. Here the support identity follows from (36.2) and
self-adjointness of $G_s$ on blocks for the trace pairing, or directly
from [ERM, (27.4)][ERM]. Averaging $Y$ with its entrywise conjugate
preserves the target pairing and does not increase its norm or
propagated support. Its value remains $t$ and its norm remains one:
a smaller positive norm would, after rescaling, give a lower bound
strictly larger than $t$. This gives a real $Y$ and (36.4).

Diagonalize $Y$. Equality in the last inequality of (36.7) forces
every positive-weight eigenvector into $\ker(R+tI_3)$ and every
negative-weight eigenvector into $\ker(R-tI_3)$: the positive
matrices $tI_3\pm R$ annihilate vectors on which their quadratic
forms vanish. A positive semidefinite $Y$ has dual value at most
$\operatorname{Tr}(Y(E-I_3))\le0$, since $G_s(I_3)=I_3$; a negative
semidefinite $Y$ has value at most $\operatorname{Tr}(YE)\le0$.
Both signs are therefore nonzero. If $H=0$, invertibility of $G_s$
on blocks forces $\Delta_W(Y)=0$. Such a cross-only matrix satisfies
$\operatorname{Tr}(YE)\le k\|Y\|_1=k$, contradicting $t>k$.
Indeed its trace norm is twice the Euclidean norm of its cross vector,
and its pairing is bounded by twice that norm times $\sqrt{rm}$.

If $h=t$, write $R=tI_3-2tww^{\mathsf T}$. Its fixed upper-to-$f$
entries are $-\sqrt r(\sqrt p,\sqrt q)^{\mathsf T}$. Hence, changing
the overall sign of $w$ if needed, $w=A_0a+B_0f$ with $A_0,B_0>0$,
$A_0^2+B_0^2=1$ and $2tA_0B_0=k$. Setting
$e_0=t(A_0^2-B_0^2)$ gives (36.5), including $e_0^2=t^2-k^2$.
Substitution proves the converse. $\square$

## 37. The finite repeated-contact prescription

**Definition 37.1 (Repeated-contact roots and primal filters).**
In the domain of Definition 36.1 define

$$
\begin{gathered}
U(t)=p+\nu t,\quad
V(t)=(\alpha q-\beta r+\alpha ut)/s,\quad
Z(t)=(c/s)(1-t/m),\\
W_0=(\alpha\nu+\beta)/s,\quad L_0=c/(ms),\\
D_0=(\alpha r-\beta q)/s,\quad D_1=-\beta u/s,\quad
D_2=(\alpha+\beta\nu)/s,\\
f_0(t)=U(t)V(t)-Z(t)^2+(uW_0-L_0^2)(t^2-k^2),\\
g_0(t)=-uV(t)-W_0U(t)+2L_0Z(t).
\end{gathered}
\tag{37.1}
$$

The degrees of $f_0,g_0$ are at most two and one. Use the four pairs

$$
\begin{aligned}
(f_1,g_1)&=(D_0+D_1t,D_2),\\
(f_2,g_2)&=(D_0-1+D_1t,D_2),\\
(f_3,g_3)&=(f_0,g_0),\\
(f_4,g_4)&=(f_0+D_0+(D_1-1)t,g_0+D_2),\\
P_j(t)&=f_j(t)^2-g_j(t)^2(t^2-k^2).
\end{aligned}
\tag{37.2}
$$

Discard identically zero $P_j$ from root generation. For each other
$P_j$, take every distinct real root $k<t<1/2$ and both values
$e_0=\pm\sqrt{t^2-k^2}$, retaining the unsquared equation
$f_j(t)+g_j(t)e_0=0$. Define

$$
\begin{gathered}
x=U(t)-ue_0,\quad y=V(t)-W_0e_0,\quad
z=Z(t)-L_0e_0,\quad d=D_0+D_1t+D_2e_0,\\
0\le d\le1,\qquad f_0(t)+g_0(t)e_0\ge0,\\
f_0(t)+D_0+(D_1-1)t+(g_0(t)+D_2)e_0\ge0.
\end{gathered}
\tag{37.3}
$$

Only candidates satisfying all these filters proceed. They have
$K_2=\left(\begin{smallmatrix}x&z\\z&y\end{smallmatrix}\right)$,
$K=K_2\oplus d$ and $T_0=x+y=1+t-d$.

**Definition 37.2 (Repeated-contact witness sampler).**
For a candidate of Definition 37.1 list its active normal generators
in the following order:

$$
\begin{array}{c|c}
\text{condition}&\text{generator }H=M\oplus\zeta\\ \hline
d=0&0_2\oplus(-1)\\
d=1&0_2\oplus1\\
\det K_2=0&-(I_2-K_2/T_0)\oplus0\\
\det(I_2-K_2)=0&[K_2-(T_0-1)I_2]/(2-T_0)\oplus0
\end{array}
\tag{37.4}
$$

There are at most two generators. With one generator use it as $H$;
with two put $H(\theta)=(1-\theta)H_1+\theta H_2$, $0\le\theta\le1$.
With no generator there is no witness candidate. For each such $H$ put

$$
\begin{gathered}
A=\begin{pmatrix}M_{00}&M_{01}/s\\
M_{01}/s&(\alpha M_{11}-\beta\zeta)/s\end{pmatrix},\qquad
c_0=(\alpha\zeta-\beta M_{11})/s,\\
A_0=\sqrt{(t+e_0)/(2t)},\quad B_0=\sqrt{(t-e_0)/(2t)},\\
\ell=\frac{(t+e_0)a^{\mathsf T}Aa-(t-e_0)c_0}{2e_0},\quad
g=(A_0/B_0)(\ell I_2-A)a,\\
Y_{\rm raw}=\begin{pmatrix}A&g\\g^{\mathsf T}&c_0\end{pmatrix},\qquad
Q=\begin{pmatrix}
-b^{\mathsf T}Ab&-b^{\mathsf T}Aa/B_0\\
-b^{\mathsf T}Aa/B_0&\ell-a^{\mathsf T}Aa-c_0
\end{pmatrix}.
\end{gathered}
\tag{37.5}
$$

Require

$$
\ell>0,\quad Q_{00}\ge0,\quad Q_{11}\ge0,\quad\det Q\ge0.
\tag{37.6}
$$

For two generators the first three polynomials in (37.6) are affine
in $\theta$, and $\det Q$ has degree at most two. Partition $[0,1]$
by its endpoints and all real roots there of these nonzero polynomials.
Test all partition points and all adjacent midpoints against every
original inequality. Identically zero polynomials are omitted only
from the partition. There are at most thirteen samples. For one
generator test (37.6) directly. A passing sample defines

$$
N=\ell+\operatorname{Tr}Q>0,\qquad Y=Y_{\rm raw}/N.
\tag{37.7}
$$

A repeated-contact entry is accepted exactly when its primal and
witness filters both pass.

**Theorem 37.3 (Global equality and conditional nonemptiness).**
Every accepted entry of Definitions 37.1–37.2 satisfies

$$
0\le K\le I_3,\quad\|Y\|_1=1,\quad
\|G_s(K)-E\|_{\rm op}=t
=\operatorname{Tr}(YE)-\operatorname{Tr}((F^n(Y))_+)=\eta_n(E).
\tag{37.8}
$$

Whenever an optimum has repeated positive contact $h=t$ in (36.3),
the accepted repeated-contact set is nonempty. Its root generation uses
at most twelve roots, of degrees at most $2,2,4,4$, each with two signs.
If its accepted set is empty, every optimum has $0\le h<t$.

Proof. Inverting (36.5) through the original $G_s$ gives (37.1)–(37.3).
The determinants of $K_2$ and $I_2-K_2$ are respectively the last two
expressions filtered in (37.3). Since
$T_0=1+t-d\in[t,1+t]\subset(0,3/2)$, both $T_0$ and
$2-T_0$ are positive. Nonnegative determinant and positive trace of
each real symmetric block prove $0\le K_2\le I_2$.
The residual is (36.5).

If $K_2$ has both endpoint eigenvalues, then $T_0=1$ and $d=t$ is
interior. If $d=0$, then $T_0=1+t>1$ excludes a zero upper eigenvalue;
if $d=1$, then $T_0=t<1$ excludes a unit upper eigenvalue. Hence at
most two generators in (37.4) occur, and all its denominators are
positive. The generators span precisely the active real block normal
cone of the effect interval at $K$; each and every nonnegative
combination attains its support at $K$.

Direct multiplication gives $Y_{\rm raw}w=\ell w$ for the $w$ of
(36.5). On its orthogonal complement with orthonormal basis
$(b,B_0a-A_0f)$, the restriction of $Y_{\rm raw}$ is $-Q$.
Its off-diagonal there is $b^{\mathsf T}Aa/B_0$, and its second
diagonal is $a^{\mathsf T}Aa+c_0-\ell$. Thus (37.6) gives
$\|Y_{\rm raw}\|_1=N$ and $-\operatorname{Tr}(Y_{\rm raw}R)=tN$.
Also $G_s(\Delta_W(Y_{\rm raw}))=H$ and
$\operatorname{Tr}(HK)=\operatorname{Tr}(H_+)$. The trace-pairing
identity (36.2) therefore gives (37.8) by (36.7), against the whole
complex effect interval.

For conditional exhaustion take a repeated-contact optimum and the
supporting $Y$ of Theorem 36.2. Its positive eigenspace is the line
spanned by $w$, with positive eigenvalue $\ell$; its negative part is
on $w^\perp$. Its nonzero $H$ is a nonnegative combination of the
one or two active normals. Rescale their coefficients to sum to one.
The block data $A,c_0$ and $Yw=\ell w$ uniquely recover $\ell,g$
by (37.5), since $e_0\ne0$. Its negative restriction is $-Q\le0$.
Thus an admissible $\theta$ exists. The signs and zero tests of all
polynomials in (37.6) are constant on each open partition interval,
so a partition point or midpoint passes.

At least one nonzero $P_j$ must bind at this optimum. Otherwise every
active constraint would be an identity along
$e_0=\operatorname{sgn}(e_0)\sqrt{t^2-k^2}$, and all other constraints
would stay strict as $t$ decreases slightly, contradicting minimality.
Indeed $P_j\equiv0$ implies $f_j=g_j=0$: $t^2-k^2$ has two distinct
roots and is not a rational-function square, so
$f_j^2=g_j^2(t^2-k^2)$ with $g_j\ne0$ is impossible. Such a constraint
vanishes on the entire branch. This argument includes exceptional
coefficient degeneracies. The sum of the four degree bounds is twelve;
multiple roots are retained once. Zero normal eigenvalues, determinant
transitions, scalar endpoints and $n=2$ obey the same filters.
The denominators $m,s,t,e_0,B_0,T_0,2-T_0$ are nonzero on the stated
domain; no derivative or $\alpha-s^2$ is inverted. $\square$

## 38. A quadratic interior family and a simple-contact obstruction

**Theorem 38.1 (An explicit positive-interior quadratic family).**
Suppose $s>0$, equivalently odd finite $n\ge3$. In the notation of
(36.1), put

$$
\begin{gathered}
A=1-\beta u,\quad B=\beta u,\quad J=1-2B>0,\quad
C_0=r-\alpha+\beta p,\\
t=\frac{A\sqrt{C_0^2+Jk^2}-BC_0}{J},\quad
e_0=(Bt-C_0)/A,\quad \omega=(t-\beta)/A.
\end{gathered}
\tag{38.1}
$$

If $e_0<0$, $t<1/2$ and $\omega\le t/(u+\nu/s^2)$, then
$\eta_n(E)=t$, attained by

$$
K_2=\begin{pmatrix}
t-u\omega&-\omega\sqrt{u\nu}/s\\
-\omega\sqrt{u\nu}/s&u\omega
\end{pmatrix},\qquad d=1.
\tag{38.2}
$$

The image is (36.5); in particular $C_{01}=-\omega\sqrt{u\nu}<0$.
A matching witness is $Y=Y_{\rm raw}/N$, where

$$
\begin{gathered}
\ell=-\frac{\nu(t+e_0)+(\alpha/\beta)(t-e_0)}{2e_0}>0,
\qquad N=2\ell-s/\beta,\\
Y_{\rm raw}=\begin{pmatrix}
0&0&\ell\sqrt{pr}/(t-e_0)\\
0&-1&(\ell+1)\sqrt{qr}/(t-e_0)\\
\ell\sqrt{pr}/(t-e_0)&(\ell+1)\sqrt{qr}/(t-e_0)&\alpha/\beta
\end{pmatrix}.
\end{gathered}
\tag{38.3}
$$

Proof. Since $A+B=1$ and $A^2-B^2=J>0$, the value in (38.1)
is the unique positive root of

$$
Jt^2+2BC_0t-C_0^2-A^2k^2=0.
\tag{38.4}
$$

The leading coefficient is positive and the constant is negative.
The equation gives $e_0^2=t^2-k^2$. Its value at $t=\beta$ is
$-A^2sm<0$, so $t>\beta$, $\omega>0$. Substitution gives
$\omega=t+e_0-m$ and $d=1$. In (38.2),
$x=t-u\omega=(m-e_0)u+t\nu>0$, its trace is $t<1/2$, and

$$
\det K_2=u\omega\,[t-\omega(u+\nu/s^2)]\ge0.
\tag{38.5}
$$

Thus $0\le K_2<I_2$, with residual eigenvalues $-t,t,t$.
The $w$ of (36.5) satisfies $Y_{\rm raw}w=\ell w$.
Moreover $\det Y_{\rm raw}=(Y_{{\rm raw},02})^2>0$, while its
$0,f$ principal determinant is negative. With $\ell>0$ these facts
force both other eigenvalues to be negative, and
$N=\|Y_{\rm raw}\|_1>0$. Its propagation is
$G_s(\Delta_W(Y_{\rm raw}))=0_2\oplus(s/\beta)$, whose support is
attained at $d=1$. Pairing with $R=tI_3-2tww^{\mathsf T}$ gives
the matching global equality as in (37.8). $\square$

**Proposition 38.2 (An exact strict interior example).**
For $n=3$, $s=1/4$, $p=q=1/32$, $r=15/16$, and arbitrary task
phases, Theorem 38.1 applies strictly, with

$$
\begin{gathered}
t=(\sqrt{1569841}-249)/2560,\qquad
2560t^2+498t-589=0,\\
K_2=\frac1{13}\begin{pmatrix}5t+3&12-32t\\12-32t&8t-3\end{pmatrix},
\quad d=1,\quad e_0=(48t-83)/208.
\end{gathered}
\tag{38.6}
$$

There is a nonempty open neighborhood of these populations, within
the positive simplex at $n=3$, on which the same quadratic rule holds.

Proof. The polynomial in (38.6) is negative at $3/8$ and positive at
$2/5$, so $3/8<t<2/5<17/41$. Hence $e_0<0$ and

$$
\det K_2=3(8t-3)(17-41t)/169>0.
\tag{38.7}
$$

Its trace is $t<1/2$, and $t>k=\sqrt{15}/16$.
All inequalities of Theorem 38.1 are strict. Continuity of its
positive-root formula and these inequalities supplies the open
neighborhood. The phase transfer is that of Proposition 27.2. $\square$

**Proposition 38.3 (A positive-interior family with only simple positive contacts).**
At $n=3$ let $q_*$ be the unique root in $(1/16,1/12)$ of

$$
123904q_*^2-43264q_*+2527=0.
\tag{38.8}
$$

Set $p_*=1-q_*$, $y_*=1/8$, $w_*=\sqrt7/8$,
$\ell_*=\sqrt{p_*q_*}-\sqrt7/32$, $\Delta=y_*-q_*$, and
$t_*=\sqrt{\Delta^2+\ell_*^2}$. For every sufficiently small
$\rho>0$, the populations

$$
p=(1-\rho)p_*,\quad q=(1-\rho)q_*,\quad r=\rho
\tag{38.9}
$$

are outside the floor region, and every optimum has $h<t$ in (36.3).

Proof. The polynomial in (38.8) has values $307$ and $-1961/9$ at
the two interval endpoints, and its derivative is negative there and
throughout the interval. Its equation and $19-128q_*>0$ give the
unsquared identity

$$
(19/64-2q_*)\sqrt7/8=(3/16)\sqrt{q_*(1-q_*)}.
\tag{38.10}
$$

This is exactly (31.5)–(31.7)'s stationarity equation for $y_*=1/8$.
Since $q_*>1/16$ and $q_*<1/2$,
$\ell_*>(2\sqrt{15}-\sqrt7)/32>1/8$, so $t_*>y_*$.
Theorem 31.3 therefore gives the boundary optimum

$$
K_{2,*}=\begin{pmatrix}7/8&\sqrt7/8\\\sqrt7/8&1/8\end{pmatrix},
\quad d_*=1/8,\quad\operatorname{spec}(G_s(K_*)-E_*)=(-t_*,y_*,t_*).
\tag{38.11}
$$

This boundary optimizer is unique. Its propagated dual upper block
from (31.13) is
$\left(\begin{smallmatrix}\Delta/t_*&s\ell_*/(2t_*)\\
s\ell_*/(2t_*)&0\end{smallmatrix}\right)$, strictly indefinite, so
support equality fixes $K_2=K_{2,*}$. If $d$ differs from $d_*$,
the upper residual changes by $\beta(d-d_*)|e\rangle\langle e|$.
Both extreme eigenvectors have nonzero $e$ component since $\ell_*>0$.
A positive change increases the $+t_*$ Rayleigh quotient; a negative
change decreases the $-t_*$ quotient. Either makes the norm exceed $t_*$.

Distance to the fixed compact attainable set is one-Lipschitz in $E$.
Along (38.9), $E_\rho\to E_*$ and $\eta_n(E_\rho)\to t_*>0$,
whereas $k_\rho\to0$. Thus these tasks are outside the floor for
all sufficiently small positive $\rho$. If arbitrarily small $\rho$
admitted a repeated-contact optimum, compactness would give a
subsequence of its effects converging to a boundary optimum, necessarily
$K_*$. Eigenvalue continuity would force its limiting residual spectrum
to be $(-t_*,t_*,t_*)$, contradicting $y_*<t_*$. $\square$

## 39. Exact algebraic operations for the simple-contact families

**Definition 39.1 (Coefficient field, factors and root conventions).**
For §§39–43 retain Definition 36.1 and assume that the accepted set of
Definitions 37.1–37.2 is empty. Put

$$
\ell_0=1-\alpha s>0,\qquad
\gamma=\sqrt{\frac{\beta\ell_0}{\alpha s^2}}>0,\qquad
L=\mathbb Q(p,q,r,s,\sqrt p,\sqrt q,\sqrt r,\gamma).
\tag{39.1}
$$

In §§39–43 the symbols $u,w,j$ are algebraic chart variables; the
population ratio $u$ of (36.1) is used only in §§36–38.
Work in the real closure $\mathbb K\subset\mathbb R$ of the ordered
field $L$. Factorization means irreducible factorization over
$\mathbb K$, normalized to leading coefficient one in a fixed monomial
order. Discard units and retain repeated factors once. Absolute
irreducibility is determined by factorization over $\mathbb K(i)$.
A real irreducible factor which splits there has two distinct conjugate
factors. Every real-root list retains distinct repeated roots once.
All operations below use exact arithmetic, factors, determinants and
real roots; every original equality and inequality is reimposed after
squaring, factorization, resultants or sampling.
For a symmetric $3\times3$ matrix write

$$
\sigma_2(A)=A_{00}A_{11}+A_{00}A_{22}+A_{11}A_{22}
             -A_{01}^2-A_{02}^2-A_{12}^2.
\tag{39.2}
$$

Thus $\det(\lambda I_3-A)=\lambda^3-\operatorname{Tr}(A)\lambda^2+
\sigma_2(A)\lambda-\det A$.

**Definition 39.2 (Coprime intersections and nonabsolute real zeros).**
For nonzero coprime $A,B\in\mathbb K[u,w]$ define
$\mathcal I(A,B)$ as follows. If both are independent of $w$, return
no points. Otherwise form the ordinary Sylvester determinant
$R(u)=\operatorname{Res}_w(A,B)$, take all its real roots $u_0$, and
then all common real roots $w_0$ of $A(u_0,w),B(u_0,w)$.
Use $\gcd(0,P)=P$; a nonzero constant has no roots.
Coprimeness makes $R$ nonzero. Both specializations cannot vanish
identically, since that would give their common factor $u-u_0$.
This is a finite enumeration containing every real common zero.
The case of two polynomials independent of $w$ has no common zero,
as coprime univariate polynomials have none.

For a real irreducible nonabsolute $C(u,w)$ depending on both
variables, define its finite real-zero operation to be
$\mathcal I(C,C_u)$. They are coprime in characteristic zero.
Every real zero of $C$ is singular: if $C$ is a nonzero real
constant times $D\overline D$, a real zero forces both factors to
vanish, and therefore both partial derivatives vanish. The distinct
complex curves have no common component, so these real zeros are
finite. If $C$ depends on just one variable, return no points: such
a nonabsolute irreducible univariate polynomial over a real closed
field is quadratic without real roots. Returned points are still
subject to all original filters.

**Definition 39.3 (Two exact curve samplers).**
Let $C(u,w)$ be absolutely irreducible and real. For a bounded open
horizontal strip $a<w<b$, with no further restrictions, use the
following strip sampler. If $C$ depends on $u$, form the nonzero
polynomial

$$
S(w)=\operatorname{lc}_u(C)\operatorname{Res}_u(C,C_u).
\tag{39.3}
$$

Partition $[a,b]$ by $a,b$ and all real roots of $S$ inside it.
Test every partition point strictly within the strip and every
adjacent midpoint. At each selected $w$, take all real $u$-roots of
$C(u,w)$. If $C$ is independent of $u$, it is linear in $w$; at its
root in the strip use $u=0$.

The open-domain sampler uses

$$
u\ne0,\qquad d_0(w)\ne0,\qquad V(u,w)d_0(w)>0,
\tag{39.4}
$$

where $d_0,V$ will be the explicit polynomials of §41. First discard
$C$ if it divides $u$, $d_0$ or $V$. If it depends on $u$, form

$$
S(w)=\operatorname{lc}_u(C)\operatorname{Res}_u(C,C_u)
       C(0,w)d_0(w)\operatorname{Res}_u(C,V).
\tag{39.5}
$$

All factors are nonzero after those discards. Partition the real line
by the real roots of $S$. Test every root and one point of every
complementary interval: adjacent midpoints, the extreme root minus
one or plus one in the two tails, and zero if there are no roots.
At each selected $w$, take all real $u$-roots of $C(u,w)$ and retain
exactly those in (39.4). If $C$ is independent of $u$, use its linear
$w$-root, discard it if $d_0(w)=0$, and partition the $u$-line by zero
and all real roots of $V(u,w)$; use the same point, midpoint and tail
rule and the same open-domain tests.

These samplers are finite and nonempty whenever the respective curve
domain is nonempty. Off the roots of $S$, degree in $u$ stays constant
and the distinct real roots vary continuously without collisions.
Their number and, for (39.5), their signs relative to $u=0$ and $V=0$
are constant on each complementary interval. Every fiber over a root
of $S$ is tested directly. If $C$ depends on $u$, $C(u,w_0)$ cannot
vanish identically, since this would give the factor $w-w_0$.
Thus its fibers are finite. These facts also include vertical
components; horizontal components are the explicitly treated linear
$w$-factors.

**Definition 39.4 (Evaluation on a constant-value component).**
If $C$ is absolutely irreducible, $C\nmid B$, and $A/B$ is constant
on $C$, divide $A,B$ by $C$ in the fixed monomial order. Select the
first nonzero coefficient of $\operatorname{rem}_C B$, obtain $c$
by the ratio to the corresponding coefficient of
$\operatorname{rem}_C A$, and verify the entire identity

$$
\operatorname{rem}_C A=c\operatorname{rem}_C B.
\tag{39.6}
$$

This evaluates the constant exactly. The constant assertions below
follow from vanishing tangential differentiation, or from both
ambient partial derivatives vanishing on the curve. In characteristic
zero a nonconstant rational function on an irreducible curve has
nonzero differential: use that function as a transcendence coordinate
and extend differentiation through the finite separable function-field
extension. Absolute irreducibility makes its algebraic constant field
$\mathbb K$. Thus zero differential implies a constant in $\mathbb K$,
which (39.6) evaluates. This includes singular points of the same
component wherever the denominator is nonzero. These elementary
resultant and function-field facts are intermediate tools for the
specific prescriptions below.

## 40. Projector faces and finite global witnesses

**Definition 40.1 (Two projector charts and primal value generation).**
For real $u$ set $N=1+u^2$ and use both charts

$$
\Pi_1(u)=\frac1N\begin{pmatrix}1&u\\u&u^2\end{pmatrix},\qquad
\Pi_2(u)=\frac1N\begin{pmatrix}u^2&u\\u&1\end{pmatrix}.
\tag{40.1}
$$

They cover every real rank-one upper-plane projection, including both
coordinate projections. For every family in this definition put

$$
A=N(G_s(K)-E),\quad P=-\sigma_2(A),\quad f=P/N^2,\quad
h=\operatorname{Tr}K-1,\quad F=\det A+NhP.
\tag{40.2}
$$

These are actual polynomial formulas in the parameters: use (36.2),
(39.2) and the ordinary determinant. In particular no unspecified
elimination ideal enters their definition.

First use the endpoint families $K=\Pi_j(u)\oplus\delta$ for
$j=1,2$ and $\delta=0,1$, with $h=\delta$.
If $F(u)\not\equiv0$, take all its real roots. If $F\equiv0$, put
$H(u)=NP_u-4uP$ and take all its real roots when $H\not\equiv0$.
If both vanish identically, use $u=0$.
For each chart also use, with $0<w<1$, the three families

$$
\begin{array}{c|c|c}
\text{family}&K&h\\ \hline
\mathrm P&\Pi_j(u)\oplus w&w\\
\mathrm L&w\Pi_j(u)\oplus1&w\\
\mathrm U&(I_2-w\Pi_j(u))\oplus0&1-w
\end{array}
\tag{40.3}
$$

For each family factor its nonzero $F(u,w)$ into distinct real
irreducible factors $C$. For a nonabsolute factor use its finite real
zeros from Definition 39.2. For an absolute factor form

$$
J_C=(NP_u-4uP)C_w-NP_wC_u.
\tag{40.4}
$$

If $C\nmid J_C$, take $\mathcal I(C,J_C)$.
If $C\mid J_C$, evaluate the constant $c=P/N^2$ on $C$ using
$\operatorname{rem}_C P=c\operatorname{rem}_C(N^2)$.
Only if $k^2<c<1/4$, put $t=\sqrt c$ and apply the strip sampler
of Definition 39.3: use $(0,t)$ for P and L, and $(1-t,1)$ for U.
Every sampled pair is a candidate.

For every generated endpoint or face point reimpose its original
family equations and intervals and the exact primal filters

$$
F=0,\quad P>0,\quad k<t=\sqrt P/N<1/2,\quad 0\le h<t.
\tag{40.5}
$$

The family automatically gives effect feasibility. Its entry is
accepted only after the witness sampler of Definition 40.2 passes.
In particular the $\delta=1$ endpoint branch fails (40.5), but is
retained in the enumeration as an explicit endpoint convention.

**Definition 40.2 (Finite necessary and sufficient witness sampler).**
For a feasible candidate with residual $R=G_s(K)-E$ of spectrum
$(-t,h,t)$, $k<t<1/2$, $0\le h<t$, put

$$
\begin{gathered}
P_-=(R-hI_3)(R-tI_3)/(2t(t+h)),\\
P_+=(R+tI_3)(R-hI_3)/(2t(t-h)),\\
Y(a)=aP_--(1-a)P_+,\qquad 0<a<1,\\
H(a)=G_s(\Delta_W(Y(a)))=M(a)\oplus c(a).
\end{gathered}
\tag{40.6}
$$

Require

$$
\begin{gathered}
[M,K_2]=0,\quad Q_1=MK_2\ge0,\quad Q_0=-M(I_2-K_2)\ge0,\\
c(a)d\ge0,\qquad-c(a)(1-d)\ge0.
\end{gathered}
\tag{40.7}
$$

After the commutator equality, $Q_0,Q_1$ are real symmetric; positivity
means exactly two diagonal inequalities and a determinant inequality
for each. There is one independent affine commutator equality, six
affine diagonal or scalar inequalities, and two determinant
inequalities of degree at most two in $a$.
Partition $[0,1]$ by its endpoints and all real roots there of these
nonzero polynomials; test all partition points and adjacent midpoints,
always imposing $0<a<1$ and every original condition in (40.7).
Zero polynomials are omitted only from the partition. There are at
most twenty-five samples. The first passing sample supplies $Y$.

**Theorem 40.3 (Primal generation and complete witness filtering on its faces).**
Every accepted primal entry has a feasible effect and a trace-norm-one
matching global witness, with value $t=\eta_n(E)$. If a global optimum
is on any endpoint or P, L, U face in Definition 40.1, at least one
entry of those families is accepted. For a supplied simple-contact
feasible effect satisfying (40.5), the finite witness sampler passes
if and only if that effect is a global optimum.

Proof. Trace preservation gives $\operatorname{Tr}(G_s(K)-E)=h$.
When $F=0$, $P>0$, its characteristic polynomial is

$$
\det(\lambda I_3-(G_s(K)-E))=(\lambda-h)(\lambda^2-P/N^2).
\tag{40.8}
$$

Thus (40.5) is exactly the simple spectrum $(-t,h,t)$ in the required
range. The two projector charts are rational descriptions of lines
with a nonzero first or second coordinate; together they include
their respective missing coordinate lines without an infinite
parameter. They do not rotate a sector of the physical map $G_s$.

The face polynomial $F$ is not identically zero. For P its leading
$w^3$ coefficient is $-\alpha\beta N^3\ne0$. For L or U, evaluate
at $u=1$ and let $J=G_s(\Pi_j(1)\oplus0)$. This positive matrix
has trace one and rank at least two, so $\sigma_2(J)>\det J$.
Their leading $w^3$ coefficients are respectively
$N^3(\det J-\sigma_2(J))$ and its negative, both nonzero there.
This includes $n=2$.

At an optimum with interior family parameters, the strict spectral
inequalities are open. Every nearby real point of $F=0$ preserving
them is a feasible effect with error $\sqrt f$. On a regular point
of an absolute factor $C$, a local minimum of $f$ has zero tangential
derivative, precisely $J_C=0$. At a singular point both partials of
$C$ vanish, so again $J_C=0$. If $C\nmid J_C$, the coprime
intersection therefore contains the point. If $C\mid J_C$, the
function-field fact in Definition 39.4 makes $f$ constant on $C$.
The strip sampler supplies a feasible point with the same value as
the original optimum, which is consequently another global optimum.
Nonabsolute factors have only the finite singular real points handled
in Definition 39.2. Repeated $F$-factors are retained once, and their
factor-specific $J_C$ avoids any squarefree or simple-root assumption.
For an endpoint, a nonzero $F$ supplies its root; if $F\equiv0$,
differentiation of $f$ gives $H=NP_u-4uP=0$, unless $f$ is constant.
In that last case $u=0$ has the same value and the same strict
spectral conditions as the optimum, since $h=\delta$ is fixed.

Evaluating (40.6)'s projector polynomials at the three distinct
residual eigenvalues gives exactly the rank-one orthogonal projectors
onto $-t$ and $+t$. Hence $\|Y(a)\|_1=1$ and
$-\operatorname{Tr}(Y(a)R)=t$. In a simultaneous eigenbasis the
commuting positivity tests in (40.7) read
$\mu\kappa\ge0$ and $-\mu(1-\kappa)\ge0$. They say
$\mu\le0$ at $\kappa=0$, $\mu\ge0$ at $\kappa=1$, and $\mu=0$
at an interior effect eigenvalue. These are exactly support attainment
over the entire upper effect interval. The scalar conditions are the
same support criterion for $d$. Thus
$\operatorname{Tr}(HK)=\operatorname{Tr}(H_+)$ and (36.7) proves
sufficiency against all complex effects.

Conversely Theorem 36.2 supplies a real matching witness at every
simple-contact optimum. Both signs are nonzero, and equality in norm
duality puts them on the two simple extreme eigenspaces. Thus that
witness is exactly $Y(a)$ for some $0<a<1$, and its support condition
is (40.7). All signs and equality truth values are constant on each
open partition interval. The finite sampler therefore passes whenever
such an $a$ exists. It also passes for every sampled constant-component
global optimum above. The sampler tests witnesses of a supplied
effect; value generation is furnished by Definition 40.1. $\square$

## 41. Reciprocal dual conics and exact effect reconstruction

**Definition 41.1 (Two conic charts and their dual values).**
For each $\epsilon\in\{-1,+1\}$ put $\chi=(1+\epsilon)/2$.
For real $j$ use both charts

$$
\begin{array}{c|ccc}
 &d_0(j)&a_0(j)&b_0(j)\\ \hline
\mathrm A&\alpha-2j+sj^2&sj^2-\alpha&2j(j-\alpha)\\
\mathrm B&s-2j+\alpha j^2&s-\alpha j^2&2(1-\alpha j)
\end{array}
\tag{41.1}
$$

The symbols $d_0,a_0,b_0$ are chart polynomials, not effect entries.
Charts A and B are reciprocal under $j\mapsto1/j$.
For $u\ne0$, $d_0(j)\ne0$ define

$$
\begin{gathered}
g_0=\gamma u a_0/d_0,\quad g_1=\gamma b_0/d_0,\\
Z=\begin{pmatrix}
\epsilon u^2&\epsilon u/s&g_0\\
\epsilon u/s&\epsilon\alpha/s&g_1\\
g_0&g_1&-\epsilon\beta/s
\end{pmatrix},\\
G_s(\Delta_W(Z))=
\epsilon\begin{pmatrix}u^2&u\\u&1\end{pmatrix}\oplus0,\\
Q(u)=u^4+(4/s^2-2)u^2+1/s^2,\\
L_\epsilon(u)=\epsilon\bigl(pu^2+2\sqrt{pq}\,u/s+
                 (\alpha q-\beta r)/s\bigr)-\chi(1+u^2),\\
V(u,j)=L_\epsilon(u)d_0(j)
       +2\gamma\sqrt r\,[\sqrt p\,u a_0(j)+\sqrt q\,b_0(j)],\\
T(u,j)=Q(u)d_0(j)^2+4\gamma^2[u^2a_0(j)^2+b_0(j)^2],\\
N_Z=\sqrt T/|d_0|,\qquad \phi(u,j)=\operatorname{sgn}(d_0)V/\sqrt T.
\end{gathered}
\tag{41.2}
$$

The open domain for these formulas is
$u\ne0$, $d_0\ne0$, $Vd_0>0$. In particular $\phi>0$.

**Theorem 41.2 (Conic determinant, norm and kernel identities).**
Every point of this open domain satisfies

$$
\begin{gathered}
\alpha g_0^2-2ug_0g_1+su^2g_1^2
     =\beta\ell_0u^2/s^2,\qquad \det Z=0,\\
\det Z_{\{0,1\}}=-\ell_0u^2/s^2<0,\quad
\tau:=\operatorname{Tr}Z=\epsilon(1+u^2),\\
\sigma:=\sigma_2(Z)
=-\frac{(1-s^2)u^2+\alpha\beta}{s^2}-g_0^2-g_1^2<0,\\
\|Z\|_1=\sqrt{\tau^2-4\sigma}=N_Z>0.
\end{gathered}
\tag{41.3}
$$

Thus $Z$ has one positive eigenvalue, one negative eigenvalue and one
zero eigenvalue. With

$$
P_0=\operatorname{adj}(Z)/\sigma,\qquad
S=[2Z-\tau(I_3-P_0)]/N_Z,
\tag{41.4}
$$

$P_0$ is its orthogonal kernel projector and $S=\operatorname{sign}Z$.
The vector $b_0^{\rm ker}=((P_0)_{02},(P_0)_{12})$ is nonzero.
The normalized $Y=Z/N_Z$ is a trace-norm-one dual witness with value
$\phi(u,j)$.

Proof. Substitution of either row of (41.1) gives the conic identity
in (41.3). Write $Z=\left(\begin{smallmatrix}A&g\\g^{\mathsf T}&c_0\end{smallmatrix}\right)$.
Its upper determinant is $-\ell_0u^2/s^2$, and
$c_0=-\epsilon\beta/s\ne0$. The Schur determinant
$\det Z=\det A(c_0-g^{\mathsf T}A^{-1}g)$ vanishes exactly by the
conic identity. Computing its three principal minors gives the
formula for $\sigma$; the diagonal sum gives $\tau$.
The upper indefinite block and $\sigma<0$ prove the asserted rank
and signs. The gap between the two nonzero eigenvalues is
$\sqrt{\tau^2-4\sigma}$. Expanding gives

$$
\tau^2-4\sigma=Q(u)+4(g_0^2+g_1^2)=T/d_0^2,
\tag{41.5}
$$

proving the norm formula and $T>0$ at every $d_0\ne0$.
On the kernel the adjugate eigenvalue is the product of the two
nonzero eigenvalues, namely $\sigma$; elsewhere it is zero. This
proves $P_0$. On the two other eigenvalues, the formula for $S$ is
their signed difference divided by their gap, proving (41.4).

The kernel is spanned by $(-A^{-1}g,1)$. Since $c_0\ne0$ and
$\det Z=0$, one has $g\ne0$, so this vector has both a nonzero upper
part and a nonzero last coordinate. Its projector therefore has
$b_0^{\rm ker}\ne0$. The propagated raw positive-part trace is
$\chi(1+u^2)$, and expansion of its target pairing gives

$$
\operatorname{Tr}(ZE)-\operatorname{Tr}((G_s(\Delta_W(Z)))_+)=V/d_0.
\tag{41.6}
$$

Dividing by $N_Z$ and using (36.2) proves the stated dual value.
$\square$

**Definition 41.3 (Finite extraction of dual critical values).**
In each signed chart form the actual polynomials

$$
A_{\rm crit}=2V_uT-VT_u,\qquad B_{\rm crit}=2V_jT-VT_j.
\tag{41.7}
$$

If both vanish identically, evaluate the constant $c=V^2/T$ by
coefficient proportionality $V^2=cT$. Only if $k^2<c<1/4$ use
$u=1,-1$ and one $j$ sample in each interval cut out by the two
distinct real roots of $d_0$: adjacent midpoints and the two tails
as in Definition 39.3. Retain exactly the open-domain points.
The discriminant of either $d_0$ is $4\ell_0>0$; its leading
coefficient is nonzero. Since $V^2=cT>0$ on $d_0\ne0$, the sign of
$Vd_0$ is constant on each component of this domain, and these samples
find an admissible point whenever one exists.

Otherwise put $G_{\rm crit}=\gcd(A_{\rm crit},B_{\rm crit})$ with
$\gcd(0,P)=P$. The two nonzero nonconstant quotients, when both
present, are coprime; include their intersection $\mathcal I$ of
Definition 39.2. This same operation applies when only one quotient
depends on $j$. A nonzero constant quotient contributes no points;
an identically zero quotient paired with $1$ contributes none.
These conventions include all critical points off $G_{\rm crit}=0$.
For each distinct real irreducible factor $C$ of $G_{\rm crit}$:
use Definition 39.2 for nonabsolute $C$; for absolute $C$, discard
it if it divides $u$, $d_0$, $V$ or $T$. Otherwise evaluate its
constant $c=V^2/T$ by
$\operatorname{rem}_C(V^2)=c\operatorname{rem}_C T$.
Only if $k^2<c<1/4$, apply the open-domain curve sampler of
Definition 39.3 with the displayed markers $u,d_0,V$.

For every generated pair reimpose
$u\ne0$, $d_0\ne0$, $Vd_0>0$ and
$k<t=\phi(u,j)<1/2$, then apply the reconstruction below.

**Definition 41.4 (Exact primal reconstruction and sufficient filters).**
For each generated dual point use $Z,N_Z,P_0,S$ of (41.2)–(41.4).
Put $b=b_0^{\rm ker}$, $e=(\sqrt{pr},\sqrt{qr})$, and

$$
\begin{gathered}
h=\frac{b\mathbin{\cdot}[t(S_{02},S_{12})-e]}{b\mathbin{\cdot}b},\\
hb=t(S_{02},S_{12})-e,\qquad 0\le h<t,\\
C=E-tS+hP_0,\\
x=C_{00},\quad z=C_{01}/s,\quad
y=(\alpha C_{11}-\beta C_{22})/s,\quad
d=(\alpha C_{22}-\beta C_{11})/s.
\end{gathered}
\tag{41.8}
$$

The vector equality is an unsquared filter, not merely its scalar
projection. Require the complete effect inequalities

$$
0\le d\le1,\quad 0\le x,y\le1,\quad
z^2\le xy,\quad z^2\le(1-x)(1-y).
\tag{41.9}
$$

Accept the entry precisely when every equality and inequality passes;
then take $K=\left(\begin{smallmatrix}x&z\\z&y\end{smallmatrix}\right)\oplus d$
and $Y=Z/N_Z$.

**Theorem 41.5 (Global sufficiency of reconstructed conic entries).**
Every accepted conic entry attains $t=\eta_n(E)$ with the matching
trace-norm-one witness $Y$.

Proof. The nonzero $b$ makes its denominator positive. The unsquared
vector equality makes the cross block of $C$ vanish, and (41.8) is
then exactly the finite-$s$ inverse of $G_s$. Inequalities (41.9)
are equivalent to effect feasibility. Its residual is
$R=-tS+hP_0$, of spectrum $(-t,t,h)$ and norm $t$.
By (41.6) the normalized physical dual value is precisely
$\phi=t$. Weak duality (36.7) gives equality. This implication
uses the explicit reconstruction filters, without any stationarity
assumption. $\square$

## 42. Nonempty exhaustive selection for simple contacts

**Theorem 42.1 (No missing interior support type).**
Under Definition 39.1, the combined accepted lists of §§40–41 are
nonempty. Every accepted entry has the common value $\eta_n(E)$.
This includes all signed finite horizons, $n=2$, multiple roots,
singular or constant-value components, zero middle residual
eigenvalues, zero support eigenvalues and rank transitions.

Proof. By Theorems 36.2 and 37.3 every optimum has residual spectrum
$(-t,h,t)$ with $k<t<1/2$ and $0\le h<t$. Its real matching witness
has rank two, one positive and one negative eigenvalue, and kernel
the middle residual eigenspace. Write

$$
H=G_s(\Delta_W(Y))=M\oplus c_0.
\tag{42.1}
$$

First classify every support possibility. One has $H\ne0$ by
Theorem 36.2, and in fact $M\ne0$. If $M=0$, $c_0\ne0$, the inverse
block formulas give
$Y_{00}=Y_{01}=0$, $Y_{11}=-\beta c_0/s\ne0$ and
$Y_{22}=\alpha c_0/s$. Rank two forces
$\det Y=-Y_{11}Y_{02}^2=0$, hence $Y_{02}=0$.
Then $e_0=(1,0,0)^{\mathsf T}$ lies in its kernel and would be the
middle residual eigenvector. This contradicts
$R_{02}=-\sqrt{pr}\ne0$. The alternative $c_0=0$ would give $H=0$.

Support attainment in (36.4) makes $M$ a normal to the upper effect
interval at $K_2$. Both upper eigenvalues cannot be interior, since
then $M=0$. Nor can $K_2=I_2$, since
$h=\operatorname{Tr}K-1=1+d\ge1>t$.
If $K_2=0$, the same trace identity and $h\ge0$ force $d=1$, $h=0$;
but then

$$
\det(G_s(0_2\oplus1)-E)=-p\alpha\beta\ne0,
\tag{42.2}
$$

contradicting the zero middle eigenvalue. Consequently the only upper
effect spectra and permitted scalar positions are

$$
\begin{array}{c|c|c}
\operatorname{spec}K_2&\text{scalar case}&\text{family or support}\\ \hline
(0,1)&d=0,1&\text{endpoint projector}\\
(0,1)&0<d<1&\mathrm P\\
(0,\lambda),\ 0<\lambda<1&d=1&\mathrm L\\
(0,\lambda),\ 0<\lambda<1&0<d<1&c_0=0,\ M\text{ negative rank one}\\
(\kappa,1),\ 0<\kappa<1&d=0&\mathrm U\\
(\kappa,1),\ 0<\kappa<1&0<d<1&c_0=0,\ M\text{ positive rank one}
\end{array}
\tag{42.3}
$$

Indeed for $(0,\lambda)$, $h=\lambda+d-1\ge0$ excludes $d=0$;
for $(\kappa,1)$, $h=\kappa+d<t<1/2$ excludes $d=1$.
The ranks and signs of $M$ in the last two support cases follow
from its vanishing on the interior upper eigenvalue and its sign on
the sole endpoint. This is an exhaustive partition, not an assumption
of strict complementarity. When a free upper eigenvalue reaches an
endpoint, it enters the projector cases; scalar transitions enter the
listed scalar endpoints. All feasible non-strict norm and support
conditions are retained.

Theorem 40.3 supplies an accepted entry for every optimum on the first,
second, third or fifth row. Its proof also covers an optimum on a
nonabsolute factor or singular point. On a constant component the
sampler may choose another effect, but its error is the same global
value and the necessary witness filter passes. Vertical and horizontal
components are included by Definition 39.3; no regular-Jacobian
hypothesis is used.

For either remaining row $c_0=0$ and $M$ is nonzero signed rank one.
Its support vector has both coordinates nonzero. A vector supported
only on the second coordinate gives $Y_{00}=Y_{01}=0$ and nonzero
$Y_{11}$; rank two then gives $Y_{02}=0$ and makes $e_0$ the kernel,
contradicting $R_{02}\ne0$. A vector supported only on the first
coordinate gives $Y_{11}=Y_{22}=Y_{01}=0$; then
$\det Y=-Y_{00}Y_{12}^2=0$ makes $e_1=(0,1,0)^{\mathsf T}$ the
kernel, contradicting $R_{12}=-\sqrt{qr}\ne0$.
After positive rescaling there are $u\ne0$ and
$\epsilon\in\{-1,+1\}$ such that

$$
M=\epsilon\begin{pmatrix}u^2&u\\u&1\end{pmatrix}.
\tag{42.4}
$$

Inverting $G_s$ determines its upper input block and bottom diagonal
exactly as in $Z$ of (41.2). Rank two requires precisely the conic
identity (41.3). This conic is real and nondegenerate: its upper
matrix is invertible indefinite and its bottom diagonal times its
upper determinant is nonzero.

For explicit coverage put $x=g_0/(u\gamma)$, $y=g_1/\gamma$.
The conic becomes $\alpha x^2-2xy+sy^2=\alpha$, with known point
$(1,0)$. The lines $y=j(x-1)$ through it give chart A of (41.1).
The tangent direction $j=\alpha$ yields the base point, since its
denominator is $\alpha(s\alpha-1)=-\alpha\ell_0\ne0$.
The only missing projective line direction is vertical. Its other
intersection is $(1,2/s)$, obtained at $j=0$ in chart B.
The latter is the reciprocal $j\mapsto1/j$ chart, so both together
cover the entire real conic. Poles with $d_0=0$ are never evaluated;
every finite conic point, including both branches, has a finite
coordinate in one of the two charts.

It remains to prove that finite critical extraction retains a global
dual value and that its reconstruction passes. On each chart the
objective $\phi=\operatorname{sgn}(d_0)V/\sqrt T$ is smooth on its
open domain. Every normalized chart point is a valid dual witness.
The normalized matching witness realizes $t>k$ and is therefore a
local maximum on its chart, giving $A_{\rm crit}=B_{\rm crit}=0$
without dividing by any derivative. The common zeros off
$G_{\rm crit}=0$ belong to the coprime quotient intersection.
Nonabsolute common factors have the finite singular real zeros of
Definition 39.2. An absolute common factor through this open-domain
point cannot divide $u,d_0,V$ or $T$. On that factor both partials
of $V^2/T$ vanish, so its function-field differential vanishes and
Definition 39.4 gives the constant $c=t^2$.
The open-domain sampler is nonempty there and supplies a genuine
normalized dual witness with positive value $\sqrt c=t$.
This includes points over projection discriminants and leading
coefficient zeros, which are tested directly. If both critical
polynomials vanish identically, the same constant-value argument
holds on the whole domain. For $k^2<c<1/4$, the sign of $Vd_0$
is constant on each component of
$\{u\ne0,d_0\ne0\}$, so the stated two $u$ samples and one sample
per $j$ interval suffice. Zero critical polynomials, repeated common
factors and multiple resultant roots are thus all included.

Finally fix any original primal optimum $K_*$ and any normalized
sampled dual witness $Y$ of value $t$. Both endpoints of

$$
t=\operatorname{Tr}(YE)-\operatorname{Tr}(H_+)
\le\operatorname{Tr}(Y(E-G_s(K_*)))
\le\|Y\|_1\|E-G_s(K_*)\|_{\rm op}=t
\tag{42.5}
$$

are equal. Simplicity of the two residual extremes makes its middle
projector exactly $P_0=\ker Y$ and its signed extreme part
$\operatorname{sign}Y=S$. Consequently

$$
G_s(K_*)-E=-tS+h_*P_0,\qquad 0\le h_*<t.
\tag{42.6}
$$

The cross-block equality is the unsquared vector equality in (41.8).
Since $b\ne0$, its scalar formula uniquely recovers $h_*$, and
inverting $G_s$ recovers $K_*$ itself. Every effect filter therefore
passes. Thus at least one conic candidate is accepted in each of the
two remaining support cases. Theorems 40.3 and 41.5 prove globality
of all accepted entries and equality of their values. $\square$

## 43. Degree bounds and deterministic selection

**Definition 43.1 (Fixed selection order).**
In the repeated-contact prescription order $j=1,2,3,4$ of (37.2),
then the increasing distinct roots $t$, then the negative $e_0$ sign
before the positive sign, and the normal generators as in (37.4).
Order partition samples increasingly and select the first passing
entry. If that accepted set is empty, use the following simple-contact
order: endpoint projector families first, then P, L, U in written
order, with chart 1 before chart 2; then the dual families with
$\epsilon=-1$ before $+1$ and chart A before B. Normalize factors
as in Definition 39.1 and order their finite coefficient tuples
lexicographically in the fixed monomial order. Order root and sample
coordinates increasingly, and take the first accepted entry and the
first passing witness sample. All such choices give the same value.

**Theorem 43.2 (Uniform finite degrees and denominator domains).**
The simple-contact construction requires only factorization of
polynomials of total degree at most eleven, arithmetic, exact scalar
tests and univariate real roots of degree at most $104$. Its value
has algebraic degree over $\mathbb Q(p,q,r,s)$ at most

$$
16\cdot792\cdot11!.
\tag{43.1}
$$

Its effect and witness coordinates are algebraic by the displayed
bounded root and rational-radical operations. Every candidate and
sample list is finite with bounds independent of the input populations
and finite horizon. The deterministic selection of Definition 43.1
is consequently defined on the whole domain of Definition 36.1.

Proof. Write bidegrees in the order $(u,w)$ for primal faces. Directly
from the displayed matrix formulas,

$$
\deg P\le(4,2),\quad \deg F\le(6,3),\quad\deg J_C\le(11,4).
\tag{43.2}
$$

The Sylvester resultant $\operatorname{Res}_w(C,J_C)$ has $u$-degree
at most $4\cdot6+3\cdot11=57$, and recovering $w$ needs degree at
most four. Endpoint $F$ has degree at most six and its fallback
$NP_u-4uP$ degree at most five. A nonabsolute primal factor has
finite-zero resultant degree at most $33$. For a flat primal
component, the projection polynomial (39.3) has degree at most $36$
and its fibers degree at most six. Thus singular and flat cases
have equally fixed degree bounds.

For each dual conic chart, in the order $(u,j)$,

$$
\deg V\le(2,2),\quad\deg T\le(4,4),\quad
\deg A_{\rm crit}\le(5,6),\quad\deg B_{\rm crit}\le(6,5).
\tag{43.3}
$$

The coprime critical resultant has $u$-degree at most
$5\cdot5+6\cdot6=61$, with $j$ recovery degree at most six.
A common factor has bidegree at most $(6,6)$ and total degree at
most eleven. Its nonabsolute real-zero resultant degree is at most
$66$. For an absolute common factor the five factors in (39.5)
have respective degree bounds $6,66,6,2,24$, so its projection
polynomial has degree at most

$$
6+66+6+2+24=104.
\tag{43.4}
$$

Its fibers have degree at most six. Horizontal factors and whole-plane
constant branches use the lower-degree rules already specified.
These estimates give parameter-independent finite candidate counts;
a loose bound is fewer than $100000$ primal-or-dual candidates before
the at-most-twenty-five primal witness samples. The repeated-contact
bounds are those of Theorem 37.3, with at most thirteen scalar
certificate samples. No stationary point or resultant root is accepted
without its sufficient global witness or exact reconstruction filters.

For the field-degree assertion, a normalized polynomial of total
degree $d$ has at most $d$ absolute factors. Galois action permutes
those factors, so the joint algebraic coefficient field of its
normalized factors has degree at most $d!$. The primal factors come
from $F$ of total degree at most nine. A nonflat primal value has
degree over $L$ at most
$9!\cdot57\cdot4\cdot2=456\cdot9!$; nonabsolute finite points give
at most $198\cdot9!$, and flat-component values at most $2\cdot9!$.
An isolated coprime dual value gives degree at most
$61\cdot6\cdot2=732$.
The dual common factors have total degree at most eleven; their
nonabsolute finite points give at most
$11!\cdot66\cdot6\cdot2=792\cdot11!$, and constant-component
values at most $2\cdot11!$. Thus $792\cdot11!$ bounds every selected
simple-contact value over $L$. Adjoining the four radicals
$\sqrt p,\sqrt q,\sqrt r,\gamma$ costs at most sixteen over
$\mathbb Q(p,q,r,s)$, proving (43.1). These are algebraic degree
bounds, with no assertion about numerical cost.

Finally every denominator has a stated domain. In the primal charts
$N=1+u^2>0$. In (40.6), $2t(t+h)>0$ and $2t(t-h)>0$, including
$h=0$. In the conic charts $s\ne0$ and
$\alpha,\beta,\ell_0,\gamma>0$; $d_0\ne0$ is tested,
$T>0$, $\sigma_2(Z)<0$, and $b\mathbin{\cdot}b>0$ were proved in
Theorem 41.2. Repeated-contact denominators were checked in
Theorem 37.3. In Theorem 38.1, $A,J,\beta,t-e_0$ are positive and
$e_0<0$; its normalization is the proved positive trace norm.
No division uses $\alpha-s^2$, a polynomial derivative, a Jacobian,
a root separation or an untested zero. In particular
$\alpha=s^2$ at $n=2$ changes no rule. Zero polynomials and factors,
multiple roots, horizontal and vertical components, chart poles and
constant-value components all have explicit branches. Non-strict
filters retain rank and scalar endpoints and $h=0$.
Theorems 37.3 and 42.1 give nonemptiness, and every accepted entry
has its own primal and matching dual equality. The fixed orders
therefore select a pair without a remaining feasibility or optimization
parameter. $\square$

## 44. Combination with all boundaries, phases and the terminal decoder

**Definition 44.1 (All finite horizons and populations).**
For the task of [ERM, Definition 27.1][ERM], use the following ordered
suppliers. At $n=0,1$ use [ERM, Theorem 27.3][ERM]. For $n\ge2$
use [ERM, Theorems 27.4–27.5][ERM] on $p=0$ or $q=0$, and
Theorem 35.1, with its balanced priority in Theorem 30.3, on
$r=0,pq>0$. Their stated population endpoints include the vertices;
at every zero task error select the input witness $Y=E$.
For positive populations first use the floor region of
[ERM, Theorem 27.7, (27.24)][ERM]. If it fails, use Definitions
37.1–37.2 when their accepted list is nonempty; otherwise use §§40–43.

The inherited floor test is also a finite scalar test, rather than
an unevaluated choice of its parameter $\lambda$. Substitute the
explicit affine quantities of (27.24) into their scalar bounds and
two determinant inequalities. Partition $[0,k]$ by its endpoints
and the real roots there of all nonzero resulting polynomials, which
have degree at most two; test every partition point and every adjacent
midpoint against all the original inequalities. Omit zero polynomials
only from this partition. If any point passes, use the least passing
sample in that order and the effect of Theorem 27.7 with the universal
floor witness (27.9). Constant signs on each complementary interval
make this test equivalent to the original criterion. No floor
parameter remains to optimize. This use leaves the inherited boundary
and floor formulas and their hypotheses intact.

**Theorem 44.2 (Exact all-input optimum and a same-qutrit CPTP decoder).**
For every complex unit $v_{\rm act}$, every finite integer $n\ge0$,
and every real instrument angle in [ERM, Definition 27.1][ERM],
Definition 44.1 gives the value, an attaining effect and a matching
lower certificate for the rank-one task
$E_{\rm act}=|v_{\rm act}\rangle\langle v_{\rm act}|$.
For the positive-interior branches let

$$
\begin{gathered}
v_{\rm act}=\Lambda(\sqrt p,\sqrt q,\sqrt r)^{\mathsf T},\quad
K_\Lambda=\Lambda K\Lambda^\dagger,\quad
Y_\Lambda=\Lambda Y\Lambda^\dagger,\\
B=U_0K_\Lambda U_0^\dagger,\\
\mathcal D_B(X)=\operatorname{Tr}(BX)E_{\rm act}
 +\operatorname{Tr}((I_3-B)X)(I_3-E_{\rm act})/2.
\end{gathered}
\tag{44.1}
$$

The boundary and small-horizon suppliers give the same effect and
decoder interface on their own domains. At every zero value use
$Y_\Lambda=E_{\rm act}$, the phase transfer of the witness $Y=E$.
For every selected pair,

$$
\begin{gathered}
0\le B\le I_3,\qquad Y_\Lambda=Y_\Lambda^\dagger,\qquad
\|Y_\Lambda\|_1=1,\\
\eta_n(E_{\rm act})
=\|(F^n)^\dagger(B)-E_{\rm act}\|_{\rm op}
=\operatorname{Tr}(Y_\Lambda E_{\rm act})
 -\operatorname{Tr}((F^n(Y_\Lambda))_+),\\
\sup_{\rho\in\mathsf D(\mathbb C^3)}
\left|\operatorname{Tr}(E_{\rm act}\mathcal D_B(F^n(\rho)))
              -\operatorname{Tr}(E_{\rm act}\rho)\right|
=\eta_n(E_{\rm act}).
\end{gathered}
\tag{44.2}
$$

This determines the rank-one quantitative target of [ERM, Definition
27.10][ERM]; complementation supplies each corresponding rank-two
task, and $0,I_3$ have value zero. The decoder is chosen for this
one task and horizon and is fixed for all complex qutrit inputs.
The resources are exactly the terminal qutrit with the chronological
history erased, as in (27.1).

Proof. The stated earlier theorems supply $n=0,1$, all population
boundaries and the floor region with their own domains and endpoint
conventions. For positive populations outside the floor, Theorem 36.2
gives (36.3). If a repeated-contact optimum exists, Theorem 37.3
supplies a nonempty accepted repeated-contact list. If that list is
empty, every optimum is simple at its positive extreme, and Theorem
42.1 supplies a nonempty simple-contact list. Theorems 37.3, 40.3
and 41.5 prove the matching equalities for every accepted entry.
The explicit finite rules and Theorem 43.2 provide the stated
algebraic selection, including both signs of $s$ and all degeneracies.
Propositions 38.2 and 38.3 respectively supply an exact open
quadratic region and positive-interior tasks requiring the
simple-contact complement; neither replaces any boundary hypothesis.

For a zero-value branch, the selected rank-one projection satisfies
$Y_\Lambda=E_{\rm act}=E_{\rm act}^\dagger\ge0$,
$\|Y_\Lambda\|_1=\operatorname{Tr}(E_{\rm act})=1$ and
$\operatorname{Tr}(Y_\Lambda E_{\rm act})=1$.
The actual physical channel
$F=\tfrac12(\operatorname{Ad}_{U_0}+\operatorname{Ad}_{U_1})$
of [ERM, (27.3)][ERM] preserves positivity and trace, as does every
$F^n$, including $F^0=\mathrm{id}$. Hence
$F^n(Y_\Lambda)\ge0$ and
$\operatorname{Tr}((F^n(Y_\Lambda))_+)=\operatorname{Tr}(F^n(Y_\Lambda))=1$.
Its global lower value in [ERM, (27.4)][ERM] is therefore $1-1=0$,
matching the inherited attaining effect. This construction applies to
every zero-value population and horizon without division by the error
or by a population. It uses the original forward channel and arbitrary
complex $v_{\rm act}$. It adds only the task projection to the finite
prescription; the positive-value witnesses and their selections are
those of the stated suppliers.

Proposition 27.2 gives the phase transfer in (44.1), preserving the
entire attainable image and the forward dual support identity.
In particular it is $Y_\Lambda$ itself that is the input functional;
the physical effect is conjugated by $U_0$. Only the diagonal
invariance of $G_s$ and its effect image is used here.

For complete positivity and trace preservation, diagonalize
$B=\sum_{j=1}^3 b_j|u_j\rangle\langle u_j|$, $0\le b_j\le1$,
and choose an orthonormal basis $w_1,w_2$ of $\ker E_{\rm act}$.
The Kraus operators

$$
L_j=\sqrt{b_j}|v_{\rm act}\rangle\langle u_j|,\qquad
M_{\ell j}=\sqrt{(1-b_j)/2}|w_\ell\rangle\langle u_j|,
\quad 1\le j\le3,\quad1\le\ell\le2
\tag{44.3}
$$

all act on the same $\mathbb C^3$. Their adjoint products sum to
$I_3$, and their Kraus sum is (44.1). Orthogonality of the prepared
states gives $\mathcal D_B^\dagger(E_{\rm act})=B$.
Conversely the adjoint of every allowed CPTP decoder is positive
and unital, so its image of $E_{\rm act}$ is an effect.
For every Hermitian residual $T$ the spectral theorem gives

$$
\sup_{\rho\in\mathsf D(\mathbb C^3)}|\operatorname{Tr}(T\rho)|
=\max_j|\lambda_j(T)|=\|T\|_{\rm op},
\tag{44.4}
$$

with equality at an extreme eigenstate. Thus the selected primal
residual and its global witness compare with every complex input,
every complex effect and every allowed decoder, proving (44.2).
Real coordinates of the selected pair impose no restriction on
these quantified complex domains.
Finally the unital complement identity of [ERM, Proposition 27.8][ERM]
negates the residual under $B\mapsto I_3-B$, with the corresponding
exchange of the prepared range and kernel states. It gives the same
value for the complementary rank-two task, including use of the same
channel for this complementary binary pair. The theorem concerns
separate fixed tasks and finite horizons; retained-memory recovery,
uniform recovery over unbounded horizons and simultaneous correction
of arbitrary task collections have their separate quantifiers.
$\square$

## 追加锚（本行以下为增补区）
