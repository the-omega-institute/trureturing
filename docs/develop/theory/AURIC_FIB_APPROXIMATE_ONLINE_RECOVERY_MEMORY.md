# AURIC FIB approximate online recovery memory

## 1. Mathematical scope and source conventions

**Convention 1.1 (Spaces and error).** Hilbert spaces are finite-dimensional
and complex, except for explicitly specified probability spaces and compact
groups. Write $M_d=\mathcal B(\mathbb C^d)$,
$\operatorname{Ad}_U(X)=UXU^\dagger$. A channel is complex-linear,
completely positive and trace-preserving (CPTP). The diamond norm is
unhalved and includes every untouched finite reference. The recovery target
is an embedded qutrit in $H=\mathbb C^5$. Only classical processing occurs
between measured instrument steps; the quantum correction occurs once, at
the declared horizon. All results concern this finite-dimensional model.

**Convention 1.2 (Mathematical suppliers).** The actual instrument and its
coordinates are those of [OWN, Definitions 1.3–2.1, Theorem 2.2 and
Theorem 6.1][OWN]. Its five-window Kraus supplier is [FIVE, Definition 17.2,
Theorem 17.3 and (18.4)][FIVE]. Both references are fixed at revision
`55208d97e98beb34acc9db6cdcd1c9da16331362`. The same-length residue input
used in §5 is [OWN, Definition 8.1 and Theorem 8.2][OWN]; the other bounds
do not require exact word injectivity. The external spectral supplier is
Bourgain–Gamburd, *A spectral gap theorem in SU(d)*, publisher final,
JEMS **14**(5) (2012), 1455–1511, DOI
[10.4171/JEMS/337][BG-DOI], p. 1455, Theorem 1 and its density footnote;
its normalized measure is (0.1), p. 1457 [BG][BG]. The supplier theorem is
used inside §6 with its hypotheses and normalization specified there.
The vector-loss, forward-walk, rounding and memory conclusions below are
ordinary deductions for the actual instrument.

## 2. Actual measured instrument and complete memory

**Definition 2.1 (Embedding and fixed branches).** In the ordered basis
$(e_0,e_1,e_2,e_3,e_4)$ of $H$, put

$$
u=(e_0+e_3)/\sqrt2,\qquad v=(e_1+e_4)/\sqrt2,\qquad z=e_2,
\qquad R=\operatorname{span}\{u,v,z\}.
$$

Let $B:\mathbb C^3\to H$ have columns $u,v,z$, put $P_R=BB^\dagger$,
and define $\iota:M_3\to M_5$ by $\iota(X)=BXB^\dagger$. The actual
unrotated Kraus operators and the fixed rotated measured operators are

$$
\begin{aligned}
K_0&=|u\rangle\langle e_0|+2^{-1/2}|v\rangle\langle e_2|
                                  +|z\rangle\langle e_4|,\\
K_1&=|u\rangle\langle e_1|+2^{-1/2}|v\rangle\langle e_2|
                                  +|z\rangle\langle e_3|,\\
A_0&=(\sqrt3K_0+iK_1)/2,\qquad
A_1=(iK_0+\sqrt3K_1)/2.
\end{aligned}
$$

The dilation is the isometry
$\mathcal Vx=K_0x\otimes f_0+K_1x\otimes f_1$ for an environment
with orthonormal basis $f_0,f_1$ and pure ready state $f_0$, completed to
a unitary interaction on $H\otimes\mathbb C^2$. The fixed outgoing
measurement basis is

$$
(\sqrt3 f_0-if_1)/2,\qquad(-if_0+\sqrt3 f_1)/2.
$$

In qutrit coordinates set

$$
U_0=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad
U_1=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix},\qquad
W=U_0^\dagger U_1=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix},
$$

$$
V_0=(\sqrt3 U_0+iU_1)/2=U_0e^{i\pi W/6},\qquad
V_1=(iU_0+\sqrt3 U_1)/2=V_0W.
$$

Here $W$ is a qutrit reflection; an integer width will always be explicitly
called a width when the same letter occurs as a subscript.

**Theorem 2.2 (Restricted fairness and chronology).** The measured operators
are CPTP in aggregate on $M_5$ and obey

$$
K_jB=BU_j/\sqrt2,\qquad A_jB=BV_j/\sqrt2.
$$

The $V_j$ are unitary. At every step on $R$, including every entangled
qutrit-reference input, the supplied actual label is a fresh fair bit.
For $h=(h_1,\ldots,h_n)$ the restricted branch is
$2^{-n/2}BQ_h$, where

$$
Q_h=V_{h_n}\cdots V_{h_1},\qquad
Q_h=\lambda^n\oplus G_h\quad\text{on }\mathbb C\xi\oplus T,
$$

$$
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\qquad T=\xi^\perp,\qquad
\lambda=e^{i\pi/6},\qquad
g_j=V_j|_T,\qquad G_h=g_{h_n}\cdots g_{h_1}.
$$

In particular $\det g_0=-1$, $\det g_1=1$.

**Proof.** The squared effects of $K_0,K_1$ are respectively
$\operatorname{diag}(1,0,1/2,0,1)$ and
$\operatorname{diag}(0,1,1/2,1,0)$, and sum to $I_5$.
Thus $\mathcal V$ is an isometry and has the stated unitary completion.
The rotated measurement gives exactly $A_0,A_1$. Expansion cancels the
cross terms and gives
$\sum_jA_jXA_j^\dagger=\sum_jK_jXK_j^\dagger$ for every complex $X$.
Applying these operators to $u,v,z$ proves the displayed restrictions.
Since $W=W^\dagger=W^{-1}$, both $V_j$ are unitary. Consequently each
restricted effect is $I_3/2$, and each output remains in $R$. Fresh
preparations give conditional probability $1/2$ at every prefix, including
with a reference; hence every length-$n$ history has probability $2^{-n}$.
The permutations fix $\xi$, so $V_j\xi=\lambda\xi$ and $T$ is reducing.
In the orthonormal basis

$$
f_1=(1,-1,0)^{\mathsf T}/\sqrt2,\qquad
f_2=(1,1,-2)^{\mathsf T}/\sqrt6
$$

of $T$ their matrices are

$$
A:=g_0=\frac14\begin{pmatrix}
\sqrt3-i&3+i\sqrt3\\3-i\sqrt3&-\sqrt3-i
\end{pmatrix},\qquad
J:=W|_T=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\qquad g_1=AJ.
\tag{2.1}
$$

Their determinants give the final assertion. All restrictions agree with
the suppliers in Convention 1.2. Fairness is asserted on $R$, not on
arbitrary inputs in $H$. $\square$

**Definition 2.3 (Permitted classical controllers).** Fix a known horizon
$n$ and $0<\varepsilon<1/4$. The instrument of Definition 2.1 is repeated
unchanged with fresh preparations and actual acquired labels. There is no
intermediate quantum feedback, postselection, reference read, retained
environment or input-dependent quantum side information.

A complete persistent classical state includes every private persistent
variable, history-dependent program or control choice, archive, buffer and
decoder input. Conditioned on an independent shared seed $s$, its update is
a stochastic kernel
$T_{k,j,s}(b\mid r)$, depending on time $k$, label $j$, horizon and
$\varepsilon$. Conditional on $s$, the initial-state law is independent
of the input and all future labels. Fresh discarded randomness is integrated
into the update kernel.
Any persistent random tape or history-dependent clock information belongs
to $r$. A deterministic schedule, the known horizon, static table descriptions
and their precision, inverse-control precision, acquisitions, preparations
and communication are separate resources. Static tables can be arbitrary
real stochastic tables chosen nonuniformly in time and horizon; they carry
no additional run-dependent information.

The seed is finite or standard Borel, independent of all acquired labels
and the input, and shared by controller and decoder. Kernels and decoder
families are measurable. Its value is free. Width is

$$
\operatorname*{ess\,sup}_{s}\ \max_{0\le k\le n}|\mathcal R_{k,s}|,
$$

where $\mathcal R_{k,s}$ is the complete counted state set. State sets may
be padded to one common width outside a seed null set. A terminal decoder
$D^H_{r,s}:M_5\to M_5$ may be any CPTP map.

**Definition 2.4 (Averaged recovery and two memory minima).** If
$p_s(r\mid h)$ is the induced terminal-state law, the corrected encoded
channel is

$$
\mathcal E_n=
\mathbb E_S\,2^{-n}\sum_{h,r}p_S(r\mid h)
 D^H_{r,S}\circ\iota\circ\operatorname{Ad}_{Q_h}:M_3\to M_5.
\tag{2.2}
$$

Success means $\|\mathcal E_n-\iota\|_\diamond\le\varepsilon$.
This condition is on the averaged channel; it imposes no per-history or
per-seed error bound. Let $W_n(\varepsilon)$ be the least finite online
peak width achieving it under Definition 2.3. Let $M_n(\varepsilon)$ be
the least essential terminal alphabet size with the same error and seed
permissions but unrestricted intermediate classical memory. Thus the
latter permits any measurable terminal kernel $p_s(r\mid h)$.
Both minima exist as integer minima because the full history is feasible.
At $n=0$ they equal one.

## 3. Typed full-space recovery

**Lemma 3.1 (CPTP retraction).** Define

$$
C(X)=B^\dagger XB+\operatorname{Tr}((I_5-P_R)X)|0\rangle\langle0|,
\qquad C:M_5\to M_3.
$$

Then $C$ is CPTP, $C\iota=\operatorname{id}_3$, and
$\iota\otimes\operatorname{id}_Z$ is a trace-norm isometry for every
finite reference $Z$.

**Proof.** If $(w_a)$ is an orthonormal basis of $R^\perp$, Kraus
operators for $C$ are $B^\dagger$ and $|0\rangle\langle w_a|$.
Their squared effects sum to $P_R+(I_5-P_R)=I_5$. The retraction identity
follows from $B^\dagger B=I_3$. Conjugation by $B\otimes I_Z$ preserves
all nonzero singular values, including for non-Hermitian operators.
$\square$

**Theorem 3.2 (Averaged diamond equivalence).** Replacing every full decoder
by $D_{r,s}=CD^H_{r,s}\iota:M_3\to M_3$ cannot increase recovery error.
Conversely every family $D_{r,s}:M_3\to M_3$ extends to full decoders
$D^H_{r,s}=\iota D_{r,s}C$ with exactly the same encoded recovery error.
Thus $W_n$ and $M_n$ can equivalently be optimized with qutrit decoders
and target $\operatorname{id}_3$.

**Proof.** For the averaged qutrit corrected channel $\mathcal C_n$,

$$
\mathcal C_n-\operatorname{id}_3
=C\circ(\mathcal E_n-\iota).
$$

This is a composition of a map $M_3\to M_5$ with a CPTP map
$M_5\to M_3$, so diamond contractivity proves the first direction. In
particular, for one decoder and one unitary it applies to
$C\circ(D_H\iota\operatorname{Ad}_Q-\iota)$; both maps inside the
parentheses have the same type. In the converse construction
$\mathcal E_n-\iota=\iota\circ(\mathcal C_n-\operatorname{id}_3)$.
Lemma 3.1 proves equality of diamond norms in every reference dimension.
All identities commute with the finite sums and seed integral. $\square$

**Corollary 3.3 (Phase-correct unitary extension).** For any $Y\in U(T)$,
put $\widehat Y=\lambda^n\oplus Y$ on $\mathbb C\xi\oplus T$.
Then

$$
D_Y=B\widehat Y^\dagger B^\dagger+(I_5-P_R)
\tag{3.1}
$$

is a full-$H$ unitary and a legal terminal correction. Its relative error
on the qutrit is $1\oplus Y^\dagger G_h$.

**Proof.** The summands act unitarily on the orthogonal spaces $R$ and
$R^\perp$. On $R$, $\widehat Y^\dagger Q_h=1\oplus Y^\dagger G_h$.
The factor $\lambda^n$ is retained because it is a relative phase between
$\xi$ and $T$. $\square$

## 4. Universal vector contraction and block loss

**Definition 4.1 (Arbitrary normalized tuples).** On $T\cong\mathbb C^2$
put $F_j=\lambda^{-1}g_j$ and
$F_h=F_{h_n}\cdots F_{h_1}=\lambda^{-n}G_h$. For an integer width
$W\ge1$, take any complex tuple $(x_{0,r})_{r=1}^W$ satisfying
$\sum_r\|x_{0,r}\|_2=1$. For any sequence of stochastic layers define

$$
x_{k+1,b}=\frac12\sum_{r=1}^W\sum_{j=0}^1
 T_{k+1,j}(b\mid r)F_jx_{k,r},\qquad
N_k=\sum_r\|x_{k,r}\|_2.
\tag{4.1}
$$

Let $a_W(n)$ be the supremum of $N_n$ over all such initial tuples and
all stochastic layers. This includes arbitrary time-, horizon- and
$\varepsilon$-dependent layers; no stationarity or physically reachable
initial-tuple restriction is imposed.

**Lemma 4.2 (Contraction and arbitrary-block transfer).** One has
$N_{k+1}\le N_k$, $a_W(0)=1$ and
$a_W(k+\ell)\le a_W(k)a_W(\ell)$. Suppose that for some integer $L\ge1$
and $0<\kappa<1$, every unit $t\in T$ and every stochastic assignment
$p(b\mid h)$ of length-$L$ histories to at most $W$ endpoints obey

$$
\sum_b\left\|2^{-L}\sum_h p(b\mid h)F_ht\right\|_2
\le1-\kappa.
\tag{4.2}
$$

Then, for every $n\ge0$,

$$
a_W(n)\le(1-\kappa)^{\lfloor n/L\rfloor}.
\tag{4.3}
$$

**Proof.** Unitarity, nonnegative stochastic coefficients and the triangle
inequality give

$$
N_{k+1}\le\frac12\sum_{b,r,j}T_{k+1,j}(b\mid r)\|x_{k,r}\|=N_k.
$$

At a split time normalize the tuple by its sum of norms, unless this sum
is zero; the remaining layers give the submultiplicative inequality.
For an actual block, let $p(b\mid r,h)$ be its endpoint probability from
initial state $r$ along the same actual history $h$. Its final tuple is

$$
y_b=2^{-L}\sum_{r,h}p(b\mid r,h)F_hx_r.
$$

For each nonzero $x_r$ apply (4.2) to $x_r/\|x_r\|$, multiply by
$\|x_r\|$, and then use the triangle inequality when merging different
sources at endpoint $b$. This gives
$\sum_b\|y_b\|\le(1-\kappa)\sum_r\|x_r\|$.
Iterate over full blocks; the remainder is contractive. In particular the
endpoint relaxation uses the same history as the vector product, without
asserting independence between endpoint and history. Every block starts
with only $W$ counted states, so this inference concerns online peak width,
not unrestricted intermediate memory. $\square$

**Theorem 4.3 (Recovery forces vector survival).** Every successful
width-$W$ controller in Definitions 2.3–2.4 satisfies

$$
1-\varepsilon\le a_W(n).
\tag{4.4}
$$

This includes arbitrary full-$H$ CPTP decoders and independent standard
Borel seeds measured by essential supremum width.

**Proof.** Use Theorem 3.2 and fix a unit $t\in T$. The operator
$Z_t=|t\rangle\langle\xi|$ has trace norm one, and
$\operatorname{Ad}_{Q_h}(Z_t)=|F_ht\rangle\langle\xi|$.
For almost every fixed seed $s$ the conditional histories remain fair.
If $r_k$ is the counted state, then

$$
x_{k,r}=\mathbb E[\mathbf1_{\{r_k=r\}}F_{h_k}\cdots F_{h_1}t\mid S=s]
$$

satisfies (4.1). Its initial tuple is $x_{0,r}=\Pr(r_0=r\mid s)t$,
with sum of norms one. All persistent variables are in $r$, so the stated
kernels give exactly this recursion even for stochastic updates.
The conditional corrected channel obeys

$$
\mathcal C_{n,s}(Z_t)=\sum_rD_{r,s}(|x_{n,r}\rangle\langle\xi|),
\qquad \|\mathcal C_{n,s}(Z_t)\|_1\le N_{n,s}\le a_W(n).
$$

The trace-norm contraction used here also holds on non-Hermitian
operators: the adjoint of a CPTP map is unital CP; its Schwarz inequality
makes it an operator-norm contraction, and trace/operator duality gives
the assertion. Thus it applies to $Z_t$ without a Hermiticity assumption.
Padding states gives one full-measure seed set on which the same bound
holds for all the finitely many times. Integrating yields
$\|\mathcal C_n(Z_t)\|_1\le\mathbb E_SN_{n,S}\le a_W(n)$.
On the other hand the averaged diamond criterion implies
$\|\mathcal C_n(Z_t)\|_1\ge1-\varepsilon$.
No conditional recovery-error claim is inferred from average recovery;
only the uniform conditional upper bound is integrated. $\square$

## 5. Fully explicit arithmetic bound

**Theorem 5.1 (Arithmetic block loss).** For every integer $W\ge1$ and
$n\ge0$, put $L_W^{\rm ar}=\lceil\log_2(3W)\rceil$. Then

$$
a_W(n)\le
\left(1-\frac1{216W^2}\right)^{\lfloor n/L_W^{\rm ar}\rfloor}.
\tag{5.1}
$$

**Proof.** The exact input is same-length projective injectivity from
[OWN, Theorem 8.2][OWN]. Its integral coordinates are
$b_1=(1,0,-1)^{\mathsf T}$, $b_2=(0,1,-1)^{\mathsf T}$ on $T$,
$\tau=i\sqrt3$ and $P_j=-2i\widehat V_j$, with

$$
P_0=\begin{pmatrix}-\tau&1\\\tau-1&\tau-1\end{pmatrix},\qquad
P_1=\begin{pmatrix}1&-\tau\\\tau-1&\tau-1\end{pmatrix}
=P_0\widehat W,\qquad
\widehat W=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

The published all-word invariant is the ring homomorphism
$\phi(a+b\tau)=a+b\pmod2$, sending both $P_j$ to
$E=\left(\begin{smallmatrix}1&1\\0&0\end{smallmatrix}\right)$.
Here $E^2=E$ and $\phi(\widehat W)E\ne E$. Cancellation of common
leading factors takes place over $\mathbb Q(\tau)$, where
$\det P_j=\pm4$ are invertible. At the first unequal letters equality
would require $X=\widehat W Y$ for equal-length tails. Nonempty tails
have residue $E$, a contradiction; empty tails would require
$I=\widehat W$. At fixed length a qutrit projective scalar is one by
applying the equality to $\xi$, whose eigenvalue is $\lambda^L$ on
both sides. This is precisely the same-length part of that supplier;
no group classification or finite enumeration is needed.

For the quantitative separation let $\eta=-i\sqrt3$. The actual letters
satisfy

$$
V_0=(i/2)(\eta U_0+U_1),\qquad V_1=(i/2)(U_0+\eta U_1),\qquad
Q_h\in(i/2)^L M_3(\mathbb Z[\eta]).
$$

Distinct length-$L$ words therefore have a nonzero entry difference
$(i/2)^L(a+b\eta)$. Since $|a+b\eta|^2=a^2+3b^2\ge1$,
$\|Q_h-Q_{h'}\|_{\rm op}\ge2^{-L}$.
The two words agree on $\xi$, so this is also a lower bound for
$\|G_h-G_{h'}\|_{\rm op}$. If their determinants agree, then
$R'=G_h^\dagger G_{h'}\in SU(2)$ and

$$
(I-R')^\dagger(I-R')=(2-\operatorname{tr}R')I_2.
$$

Indeed $R'+R'^\dagger=(\operatorname{tr}R')I_2$ for $SU(2)$.
The two singular values of $G_h-G_{h'}$ are equal. Thus for every unit
$t\in T$, within either determinant class,

$$
\|F_ht-F_{h'}t\|_2\ge2^{-L}.
\tag{5.2}
$$

Write $M=2^L$. The endpoint objective in (4.2) is convex in
$p(b\mid h)$. Each stochastic assignment is a convex combination of
deterministic functions $f$, with weights $\prod_h p(f(h)\mid h)$;
these weights sum to one and have the required marginals. It suffices to
bound every deterministic assignment. Split each endpoint by determinant,
using the triangle inequality. There are at most $2W$ nonempty groups.
For $m$ unit vectors in one group with pairwise distance at least
$\delta=M^{-1}$,

$$
m-\left\|\sum_{i=1}^m v_i\right\|
=\frac{\sum_{i<j}\|v_i-v_j\|^2}{m+\|\sum_i v_i\|}
\ge\frac{(m-1)\delta^2}{4}.
$$

Summing the losses and dividing by $M$ gives, uniformly in the starting
unit vector and all stochastic endpoint assignments,

$$
\sum_b\left\|M^{-1}\sum_h p(b\mid h)F_ht\right\|
\le1-\frac{1-2W/M}{4M^2}.
\tag{5.3}
$$

Take $L=L_W^{\rm ar}$. Then $3W\le M<6W$. For $u=M/W\in[3,6)$,

$$
\frac{u-2}{4u^3}-\frac1{216}
=\frac{(6-u)(u^2+6u-18)}{216u^3}\ge0.
$$

Thus the loss is at least $1/(216W^2)$, and Lemma 4.2 proves (5.1).
The argument uses vector separation to prove an averaged grouping loss;
a pairwise collision statement by itself would not give (5.1). $\square$

**Corollary 5.2 (Effective necessary width).** Put
$b_\varepsilon=-\ln(1-\varepsilon)>0$. Successful width $W$ requires

$$
n<\lceil\log_2(3W)\rceil(1+216b_\varepsilon W^2).
\tag{5.4}
$$

In particular, for $n\ge1$,

$$
W_n(\varepsilon)\ge
\min\left\{n,
\sqrt{\frac{[\,n/\log_2(6n)-1\,]_+}{216b_\varepsilon}}\right\},
\tag{5.5}
$$

where $[x]_+=\max\{x,0\}$. This is an effective
$\Omega_\varepsilon(\sqrt{n/\ln n})$ lower bound at fixed error.

**Proof.** Combine (4.4) and (5.1) and use $-\ln(1-x)>x$ for
$0<x<1$. With $k=\lfloor n/L_W^{\rm ar}\rfloor$ one obtains
$k<216b_\varepsilon W^2$, including $k=0$, and then (5.4).
If $W<n$, $L_W^{\rm ar}<\log_2(6n)$, giving (5.5); if $W\ge n$
the minimum in (5.5) is already a lower bound. The positive part covers
the small-$n$ endpoint. For $n<L_W^{\rm ar}$, (5.1) only asserts
$a_W(n)\le1$. No formula here is evaluated at $\varepsilon=0$.
$\square$

## 6. Algebraic density and the actual forward spectral comparison

**Definition 6.1 (Actual conjugate reflections).** Retain $A,J$ of (2.1)
and set

$$
J_k=A^{-k}JA^k,\qquad R_1=J_0J_1,\qquad R_2=J_0J_2,\qquad
\mathcal G=\{G\in U(2):\det G=\pm1\}=SU(2)\sqcup J SU(2).
$$

**Theorem 6.2 (Dense phase-resolved group).** The algebraic matrices
$R_1,R_2\in SU(2)$ generate a dense subgroup of $SU(2)$. Moreover
$\overline{\langle g_0,g_1\rangle}=\mathcal G$; its identity component
has real dimension three, and its action on unit vectors of $T$ contains
the full sphere $S^3$, including phase.

**Proof.** Direct calculation from (2.1) gives

$$
\operatorname{tr}A=-i/2,\qquad
\alpha_\pm=(\pm\sqrt{15}-i)/4,\qquad
q=\alpha_+/\alpha_-=(-7+i\sqrt{15})/8.
$$

In an orthonormal $A$-eigenbasis, write
$J=\left(\begin{smallmatrix}a&b\\\bar b&-a\end{smallmatrix}\right)$.
The identity
$a(\alpha_+-\alpha_-)=\operatorname{tr}(AJ)=-\sqrt3/2$ gives
$a=-1/\sqrt5$, and $J^2=I$ gives $|b|=2/\sqrt5$.
Using Pauli matrices, write $J_k=n_k\cdot\sigma$ with real unit $n_k$.
Then

$$
n_k\cdot n_\ell=\frac15+\frac45\operatorname{Re}(q^{k-\ell}),
\qquad \operatorname{tr}R_1=-1,\qquad \operatorname{tr}R_2=\frac54,
$$

$$
\operatorname{Gram}(n_0,n_1,n_2)=
\begin{pmatrix}1&-1/2&5/8\\-1/2&1&-1/2\\5/8&-1/2&1\end{pmatrix},
\qquad\det\operatorname{Gram}=\frac{27}{64}>0.
\tag{6.1}
$$

The Pauli vector parts of $R_1,R_2$ are respectively proportional to
$n_0\times n_1,n_0\times n_2$. Their independence proves noncommutation.
The element $R_2$ has infinite order: finite order would make its trace
an algebraic integer, whereas the rational number $5/4$ is not an integer.

For completeness the closed-subgroup argument here uses the Lie algebra
of $SU(2)$, identified with $\mathbb R^3$ and its cross product. A proper
nonzero Lie subalgebra has dimension one, since a two-plane is not closed
under cross product. A closed infinite subgroup has positive-dimensional
identity component; a zero-dimensional compact Lie group is finite.
Thus a proper infinite closed subgroup of $SU(2)$ has a circle as identity
component and lies in its normalizer. In coordinates where the circle is
diagonal, every element of its normalizer outside the circle is
anti-diagonal and has trace zero. Both $R_i$ have nonzero trace, so a
proper closed subgroup containing them would put them in one circle and
make them commute, contradicting (6.1). This proves density. Their entries
are algebraic already in (2.1), without choosing an eigenbasis.

Each $R_i$ is a word in $A,J$, and $J=g_0^{-1}g_1$. The closed group
generated by $g_0,g_1$ therefore contains $SU(2)$ and the determinant-minus
coset representative $A$; it is all $\mathcal G$. Finally $SU(2)$ acts
freely and transitively on the unit vectors of $\mathbb C^2$: each unit
vector determines the first column of a unique $SU(2)$ matrix. This orbit
is $S^3$, not the sphere of projective rays. $\square$

**Definition 6.3 (Measures and top gap).** For probability measures on
$\mathcal G$, use

$$
T_\eta f(x)=\int f(g^{-1}x)\,d\eta(g),\qquad
T_\alpha T_\beta=T_{\alpha*\beta},\qquad
\check\eta(E)=\eta(E^{-1}).
$$

With normalized Haar measure, define

$$
\sigma=\tfrac14(\delta_{R_1}+\delta_{R_1^{-1}}
                    +\delta_{R_2}+\delta_{R_2^{-1}}),\qquad
\gamma=\inf_{0\ne f\perp1\text{ in }L^2(SU(2))}
\frac{\|f\|_2^2-\langle f,T_\sigma f\rangle}{\|f\|_2^2}.
\tag{6.2}
$$

The actual forward measure is

$$
\mu=\tfrac12(\delta_A+\delta_{AJ}),\qquad
\nu=\check{\mu^{*3}}*\mu^{*3}.
$$

**Theorem 6.4 (From the published top gap to the forward walk).** The
number $\gamma$ in (6.2) is positive. Put

$$
\rho=\sqrt{1-\gamma/16}\in(0,1).
$$

Then

$$
\nu\ge\sigma/16,\qquad
\|T_\mu^3\|_{L^2_0(\mathcal G)}\le\rho,\qquad
\|T_\mu^L\|_{L^2_0(\mathcal G)}\le\rho^{\lfloor L/3\rfloor}.
\tag{6.3}
$$

Here $L^2_0$ means orthogonal to constants. No numerical value of
$\gamma$ is specified.

**Proof.** [BG, p. 1455, Theorem 1][BG] applies to finitely many algebraic
matrices in $SU(d)$ generating a Zariski-dense subgroup of $SL_d(\mathbb C)$;
its footnote identifies this with topological density in $SU(d)$.
Take $d=2$, $k=2$, and the actual $R_1,R_2$ of Theorem 6.2. The paper's
self-adjoint operator is
$z f(x)=\sum_{i=1}^2[f(R_ix)+f(R_i^{-1}x)]$.
Since $\sigma$ is symmetric, $z/4=T_\sigma$ under our inverse convention.
The paper's top-gap assertion $\lambda_1(z)<4$ is exactly $\gamma>0$.
It is not an absolute gap or a gap for a nonsymmetric forward walk.
Also $\gamma\le2$ since $T_\sigma$ is a self-adjoint contraction.

The three length-three histories with a single label $1$ have products
$A^3J_k$, $k=0,1,2$. The ordered differences of the $k=0$ word with the
$k=1,2$ words and their reverses give
$R_1,R_1^{-1},R_2,R_2^{-1}$ in $\nu$. Each ordered pair has probability
$1/64$. Thus $\nu\ge\sigma/16$. These are differences of actual forward
histories, not a substitution of a symmetric walk for $\mu$.

Decompose $L^2(\mathcal G)$ orthogonally into constants, the character
$\det$, and the subspace $\mathcal H_c$ with zero mean on each determinant
coset. All these subspaces are preserved by the convolution operators in
question. On each coset, left $SU(2)$ action is a copy of its regular
action, so $\sigma$ has the same top gap $\gamma$ on $\mathcal H_c$.
The determinant of each actual letter is a fair sign, hence
$T_\mu^3\det=0$ and $T_\nu\det=0$.
The positive measure $\nu-\sigma/16$ has mass $15/16$. The Dirichlet
form of an average of unitary translations is nonnegative in real part;
therefore, for $f\in\mathcal H_c$,

$$
\langle f,(I-T_\nu)f\rangle
\ge\frac1{16}\langle f,(I-T_\sigma)f\rangle
\ge\frac\gamma{16}\|f\|_2^2.
$$

Crucially $T_\nu=(T_\mu^3)^*T_\mu^3$ is positive. Thus its norm on
$\mathcal H_c$ is at most $1-\gamma/16$, and it is zero on the remaining
nonconstant determinant mode. Taking a square root gives the second
inequality in (6.3). The remainder of fewer than three steps has norm at
most one, proving the last inequality. This handles both determinant
cosets and the top-versus-absolute-gap distinction. $\square$

## 7. Sphere small balls and spectral block loss

**Theorem 7.1 (Uniform phase-resolved small balls).** For every unit
$t\in T$, every $L\ge0$, every center $c\in S^3$ and
$0<\delta\le1/2$, under the actual fair length-$L$ history,

$$
\Pr(\|F_ht-c\|_2\le\delta)
\le8\delta^3+10\rho^{\lfloor L/3\rfloor}.
\tag{7.1}
$$

**Proof.** Normalized Haar chord-ball volume on $S^3$ is independent of
center and equals

$$
v(r)=\frac2\pi\int_0^{2\arcsin(r/2)}\sin^2u\,du.
$$

For $0<r\le1$, with $\theta=2\arcsin(r/2)$,
$r\le\theta\le\pi r/3\le\pi/3$. Using
$2u/\pi\le\sin u\le u$ on this interval gives

$$
\frac8{3\pi^3}r^3\le v(r)\le r^3.
\tag{7.2}
$$

Indeed the upper integration bound is
$2\theta^3/(3\pi)\le(2\pi^2/81)r^3<r^3$.
For each starting unit vector $t$, the pullback $f\mapsto[G\mapsto f(Gt)]$
is an isometric embedding of $L^2(S^3)$ into $L^2(\mathcal G)$ and
intertwines left convolution. Both determinant cosets send Haar to the
same uniform sphere measure. Hence (6.3) bounds the sphere density
evolution, uniformly in $t$.

Smooth $t$ to a uniformly distributed $t'$ in its $\delta$-ball,
independently of the history, and apply the same actual history to both.
All products are isometries, so $\|G_ht-G_ht'\|\le\delta$.
The event $G_ht\in B(c,\delta)$ implies
$G_ht'\in B(c,2\delta)$. The initial density has integral one and
mean-zero $L^2$ norm at most $v(\delta)^{-1/2}$. By (6.3) and
Cauchy–Schwarz the probability of this latter ball is at most

$$
v(2\delta)+\rho^{\lfloor L/3\rfloor}
 \sqrt{v(2\delta)/v(\delta)}
\le8\delta^3+\sqrt{3\pi^3}\,\rho^{\lfloor L/3\rfloor}.
$$

Here $2\delta\le1$ permits both applications of (7.2), and
$\sqrt{3\pi^3}<10$. Finally
$F_ht=\lambda^{-L}G_ht$; this deterministic scalar rotates the tested
center and preserves sphere measure and distance. It does not quotient
out the relative phase. $\square$

**Theorem 7.2 (Joint stochastic-color loss).** For every integer $W\ge1$
put

$$
\delta_W=(32W)^{-1/3},\qquad
L_W^{\rm sp}=3\left\lceil\frac{\ln(40W)}{-\ln\rho}\right\rceil,
\qquad c_0=2^{-16/3}.
\tag{7.3}
$$

Then for all $n\ge0$,

$$
a_W(n)\le(1-c_0W^{-2/3})^{\lfloor n/L_W^{\rm sp}\rfloor}.
\tag{7.4}
$$

A successful width $W$ necessarily satisfies both

$$
1-\varepsilon\le
 (1-c_0W^{-2/3})^{\lfloor n/L_W^{\rm sp}\rfloor},
\qquad
n<L_W^{\rm sp}\bigl(1+b_\varepsilon c_0^{-1}W^{2/3}\bigr).
\tag{7.5}
$$

**Proof.** Fix a unit $t$ and any stochastic endpoint assignment along
length-$L_W^{\rm sp}$ histories. Write

$$
x_b=\mathbb E[p(b\mid h)F_ht],\qquad
c_b=x_b/\|x_b\|\quad\text{if }x_b\ne0,
$$

choosing any unit $c_b$ otherwise. Expanding squared distances gives the
exact same-history identity

$$
1-\sum_b\|x_b\|
=\frac12\mathbb E\sum_b p(b\mid h)\|F_ht-c_b\|^2.
\tag{7.6}
$$

The real inner-product term sums to $\sum_b\|x_b\|$, and
$\sum_b p(b\mid h)=1$, which proves (7.6) also for random colors and
zero endpoint vectors. Since $\delta_W<1/2$, Theorem 7.1 shows that
every $\delta_W$-ball has probability at most
$1/(4W)+1/(4W)=1/(2W)$. At most $W$ such balls cover at most half the
probability. Outside their union every candidate center has distance at
least $\delta_W$, so (7.6) is at least
$\delta_W^2/4=c_0W^{-2/3}$. This holds for any joint history/color law
with the specified fair history marginal. Apply Lemma 4.2 to obtain
(7.4). Theorem 4.3 gives the first condition in (7.5), and
$-\ln(1-x)>x$ gives the second as in Corollary 5.2. $\square$

## 8. Explicit stochastic online and offline constructions

**Definition 8.1 (Radial lattice shell and determinant bit).** Use the
real-linear quaternion map

$$
\Phi(q)=\begin{pmatrix}
q_0+iq_1&q_2+iq_3\\-q_2+iq_3&q_0-iq_1
\end{pmatrix},\qquad q\in\mathbb R^4.
$$

It satisfies $\Phi(q)^\dagger\Phi(q)=\|q\|_2^2I_2$,
$\|\Phi(q)\|_{\rm op}=\|q\|_2$ and $\Phi(S^3)=SU(2)$.
For integer $m\ge8$ put $\delta=1/m$ and

$$
\mathcal N_\delta=
\left\{a/\|a\|:\ a\in\delta\mathbb Z^4,
                         \ 1-2\delta\le\|a\|\le1+2\delta\right\}.
$$

States are $(d,q)\in\{0,1\}\times\mathcal N_\delta$ and represent
$Y=J^d\Phi(q)$. The initial state is $(0,(1,0,0,0))$, representing
$I_2$ and belonging to the shell because $m$ is an integer. After label
$j$, set

$$
d'=d\mathbin\oplus(1-j),\qquad
z=\Phi^{-1}(J^{d'}g_jJ^d\Phi(q))\in S^3.
\tag{8.1}
$$

Independently round each real coordinate $z_i$ to the two neighboring
$\delta$-lattice coordinates with probabilities giving mean $z_i$.
If it is already a lattice coordinate, leave it there. Write the rounded
vector as $a=z+e$, set $q'=a/\|a\|$ and retain $(d',q')$.

**Lemma 8.2 (Legal rounding, cardinality and second-order moments).** This
is a finite stochastic update depending only on the current counted state
and current label, with at most $28\pi^2m^3$ states. Uniformly in $z$,

$$
\mathbb Ee=0,\quad \|e\|\le2\delta,\quad
\mathbb E\|e\|^2\le\delta^2,
\tag{8.2}
$$

$$
\|\mathbb E(q'-z)\|\le4\delta^2,\qquad
\mathbb E\|q'-z\|^2\le4\delta^2.
\tag{8.3}
$$

**Proof.** Because $\det g_j=(-1)^{1-j}$, (8.1) has determinant one
and defines a unit quaternion. Each coordinate rounding error has mean
zero, magnitude at most $\delta$, and variance at most $\delta^2/4$.
This proves (8.2). In particular $1-2\delta\le\|a\|\le1+2\delta$,
so $a$ is nonzero and its radial normalization belongs to the same fixed
state set. Duplicate radial normalizations may be merged.

For $f(v)=v/\|v\|$, write $u=v/\|v\|$, $e=\alpha u+b$, $b\perp u$.
Differentiation gives

$$
D^2f(v)[e,e]=-
 \frac{\|b\|^2u+2\alpha b}{\|v\|^2},\qquad
\|D^2f(v)[e,e]\|\le\frac{2\|e\|^2}{\|v\|^2}.
$$

Along $z+te$, $0\le t\le1$, the radius is at least
$1-2\delta\ge1/2$. Taylor's integral remainder is bounded by
$4\|e\|^2$, while the first derivative has zero expectation because
$\mathbb Ee=0$. This proves the first bound of (8.3). Also
$\|a/\|a\|-z\|\le2\|a-z\|$, proving its second bound.
The update therefore uses unbiased lattice rounding followed by radial
normalization with a controlled second-order mean bias.

To count the shell lattice points, center a side-$\delta$ cube at each.
Their interiors are disjoint, and their circumradius in $\mathbb R^4$ is
$\delta$. All cubes lie between radii $1-3\delta$ and $1+3\delta$.
Using four-ball volume $\pi^2r^4/2$ and $\delta\le1/8$,

$$
\#\{a\}\delta^4
\le\frac{\pi^2}{2}[(1+3\delta)^4-(1-3\delta)^4]
=12\pi^2\delta(1+9\delta^2)\le14\pi^2\delta.
$$

Including the determinant bit gives at most $28\pi^2m^3$ states.
All persistent information in the construction is precisely this state;
rounding draws are discarded after the update. $\square$

**Lemma 8.3 (Local averaged diamond error).** Fix a current state $Y$ and
label $j$, put $Z=g_jY$, and let $Y'=J^{d'}\Phi(q')$ be the rounded
next state. On $\mathbb C\xi\oplus T$ define

$$
\mathcal L_{Y,j}=\mathbb E\operatorname{Ad}_{1\oplus Y'^\dagger Z}.
$$

Then $\|\mathcal L_{Y,j}-\operatorname{id}_3\|_\diamond\le12/m^2$.
The same estimate holds for any fixed target $Z\in\mathcal G$, rounded
in its determinant coset: set $d'$ by $\det Z=(-1)^{d'}$, round
$z=\Phi^{-1}(J^{d'}Z)$, and use the resulting $Y'=J^{d'}\Phi(q')$.

**Proof.** Put $B_{\rm err}=Y'^\dagger Z-I_2$ on $T$, extended as
zero on $\xi$. Since $Z=J^{d'}\Phi(z)$, real linearity of $\Phi$,
adjoint linearity over real expectations, and (8.3) give

$$
\|\mathbb EB_{\rm err}\|_{\rm op}\le4\delta^2,\qquad
\mathbb E\|B_{\rm err}\|_{\rm op}^2\le4\delta^2.
$$

In every reference dimension the exact expansion is

$$
(\mathcal L_{Y,j}-\operatorname{id})(X)
=(\mathbb EB_{\rm err})X+X(\mathbb EB_{\rm err})^\dagger
 +\mathbb E[B_{\rm err}XB_{\rm err}^\dagger],
$$

with identity tensor factors understood. Left/right multiplication has
trace-norm bound given by the operator norm of its multiplier, and the
quadratic term is bounded by the second operator-norm moment. The sum is
at most $(4+4+4)\delta^2$. This is a local averaged estimate; it is not
an $O(\delta^2)$ estimate for every individual rounding branch. $\square$

**Theorem 8.4 (Explicit online and offline bounds).** For $n\ge1$ and
$0<\varepsilon<1/4$,

$$
W_n(\varepsilon)\le
\min\left\{2^n,\ 28\pi^2
       \left\lceil4\sqrt{n/\varepsilon}\right\rceil^3\right\},
\tag{8.4}
$$

$$
M_n(\varepsilon)\le
\min\left\{2^n,\ 28\pi^2
       \left\lceil4/\sqrt\varepsilon\right\rceil^3\right\}.
\tag{8.5}
$$

At $n=0$, $W_0(\varepsilon)=M_0(\varepsilon)=1$.

**Proof.** For the online construction choose
$m=\lceil4\sqrt{n/\varepsilon}\rceil\ge8$ and run Definition 8.1.
Let the actual accumulated restricted product be $G_t$, the rounded
state be $Y_t$, and set $E_t=1\oplus Y_t^\dagger G_t$. Define the CP
subchannel

$$
\mathcal M_t(Y)=
\mathbb E[\mathbf1_{\{Y_t=Y\}}\operatorname{Ad}_{E_t}],\qquad
\mathcal C_t=\sum_Y\mathcal M_t(Y).
$$

Every $E_t$ is unitary and its probability is independent of the input.
Thus $\mathcal M_t(Y)^\dagger(I)=\Pr(Y_t=Y)I$, and
$\|\mathcal M_t(Y)\|_\diamond=\Pr(Y_t=Y)$. Equivalently, it is that
probability times a channel, with the zero-probability case interpreted
as the zero map.

Conditional on $Y_t=Y$ and the next actual fair label $j$, the fresh
rounding is independent of the past relative error. The identity

$$
E_{t+1}=(1\oplus Y'^\dagger g_jY)E_t
$$

therefore implies the probability-weighted recursion

$$
\mathcal C_{t+1}=\frac12\sum_{Y,j}
 \mathcal L_{Y,j}\circ\mathcal M_t(Y).
\tag{8.6}
$$

Subtract $\mathcal C_t$ and use Lemma 8.3 with the actual subchannel
weights. Since $\sum_Y\Pr(Y_t=Y)=1$,

$$
\|\mathcal C_{t+1}-\mathcal C_t\|_\diamond\le12/m^2,\qquad
\|\mathcal C_n-\operatorname{id}_3\|_\diamond
\le12n/m^2\le3\varepsilon/4.
\tag{8.7}
$$

The channels at intermediate times in this calculation are analysis
quantities; the physical procedure applies only the terminal correction
(3.1) with $Y=Y_n$. Its qutrit relative error is exactly $E_n$, so
(8.7) and the typed embedding establish success on every reference.
Lemma 8.2 proves the lattice-shell part of (8.4).

For (8.5), retain the complete history using the unrestricted intermediate
memory, compute $G_h$, and at the terminal time round it once in its
correct determinant coset using
$m=\lceil4/\sqrt\varepsilon\rceil$. Conditional on each history,
Lemma 8.3, with exact target $Z=G_h$, gives averaged relative error at
most $12/m^2\le3\varepsilon/4$. Averaging histories preserves this
bound. Retain only $(d,q)$ and use (3.1), giving (8.5) by the same count.
This argument uses a single final rounding rather than accumulation of
$n$ rounding errors.

Alternatively keep the binary prefix in a register of at most $2^n$
values, update $r_k=2r_{k-1}+h_k$, and at the known horizon apply
$BQ_h^\dagger B^\dagger+(I_5-P_R)$. It recovers exactly and gives the
other terms in both minima. None of these constructions requires shared
randomness. Static probabilities and unitary controls are exact in the
specified mathematical resource model. $\square$

## 9. Fixed-error growth power and bit count

**Theorem 9.1 (Quantified spectral lower bound and exponent).** For fixed
$0<\varepsilon<1/4$, retain the actual $\gamma,\rho$ of §6 and put

$$
K_\varepsilon=3500\pi^2\varepsilon^{-3/2},\qquad
s=-\ln\rho>0,\qquad
H_{\gamma,\varepsilon}
=3\left(\frac{3/2+\ln(40K_\varepsilon)}s+1\right),
$$

$$
c_{\gamma,\varepsilon}
=\left(\frac{c_0}{2b_\varepsilon H_{\gamma,\varepsilon}}\right)^{3/2}.
$$

For every integer $n$ satisfying

$$
n\ge e,\qquad n\ge2H_{\gamma,\varepsilon}\ln n,
\tag{9.1}
$$

one has

$$
c_{\gamma,\varepsilon}\left(\frac n{\ln n}\right)^{3/2}
\le W_n(\varepsilon)
\le\min\left\{2^n,28\pi^2
       \left\lceil4\sqrt{n/\varepsilon}\right\rceil^3\right\}.
\tag{9.2}
$$

Consequently

$$
\lim_{n\to\infty}\frac{\ln W_n(\varepsilon)}{\ln n}=\frac32,
\qquad
\left\lceil\log_2 W_n(\varepsilon)\right\rceil
=\frac32\log_2n+O_\varepsilon(\log\log n).
\tag{9.3}
$$

**Proof.** For $n\ge1$, $x=\sqrt{n/\varepsilon}\ge1$, so
$\lceil4x\rceil\le5x$. Theorem 8.4 gives
$W_n\le K_\varepsilon n^{3/2}$. Since $\ln n\ge1$ under (9.1),

$$
L_{W_n}^{\rm sp}
\le3\left(\frac{\ln(40K_\varepsilon)+(3/2)\ln n}{s}+1\right)
\le H_{\gamma,\varepsilon}\ln n.
$$

The second condition in (9.1) ensures
$\lfloor n/L_{W_n}^{\rm sp}\rfloor\ge
 n/(2H_{\gamma,\varepsilon}\ln n)$. Combining (4.4) and (7.4), and
using $1-x\le e^{-x}$, gives

$$
b_\varepsilon\ge
c_0 W_n^{-2/3}\lfloor n/L_{W_n}^{\rm sp}\rfloor
\ge\frac{c_0n W_n^{-2/3}}{2H_{\gamma,\varepsilon}\ln n}.
$$

Rearrangement gives (9.2). The start condition is nonempty and holds for
all sufficiently large $n$; for example it is sufficient that
$n\ge\max\{e,(2H_{\gamma,\varepsilon})^2\}$, since
$\ln n\le\sqrt n$ for $n\ge1$. Taking logarithms in (9.2) squeezes
$\ln W_n$ between
$(3/2)\ln n-(3/2)\ln\ln n+\ln c_{\gamma,\varepsilon}$ and
$(3/2)\ln n+\ln K_\varepsilon$. This proves both statements of (9.3),
including rounding to an integer bit count. The instrument is fixed, so
the fixed $\gamma$ dependence is included in the error-dependent constants.
$\square$

## 10. An independent explicit backup

**Theorem 10.1 (Single-one histories).** Without using exact word
injectivity, group classification or the spectral-gap theorem, for every
integer $W\ge1$ and $n\ge0$,

$$
a_W(n)\le(1-8^{-W}/10)^{\lfloor n/(W+1)\rfloor}.
\tag{10.1}
$$

Successful width $W$ therefore requires

$$
n<(W+1)(1+10b_\varepsilon8^W),
\tag{10.2}
$$

and at fixed error

$$
W_n(\varepsilon)\ge\tfrac13\log_2n
 -\tfrac13\log_2\log_2(n+2)-O_\varepsilon(1).
\tag{10.3}
$$

**Proof.** The actual $q$ in §6 satisfies $q+q^{-1}=-7/4$.
It is not a root of unity, since that would make this noninteger rational
number an algebraic integer. Define

$$
t_d=4^d(q^d+q^{-d}),\qquad t_0=2,\quad t_1=-7,\qquad
t_d=-7t_{d-1}-16t_{d-2}.
$$

Thus $t_d\in\mathbb Z$. For every $d\ge1$, $q^d\ne1$, so

$$
|1-q^d|^2=\frac{2\cdot4^d-t_d}{4^d}\ge4^{-d},
\tag{10.4}
$$

because its numerator is a strictly positive integer. In the orthonormal
$A$-eigenbasis the off-diagonal entries of $J_k$ are
$bq^{-k},\bar bq^k$, with $|b|=2/\sqrt5$. The diagonal entries are
independent of $k$. Hence $J_k-J_\ell$ has two equal singular values
$(2/\sqrt5)|q^k-q^\ell|$.

Take the $W+1$ actual length-$(W+1)$ histories with a single label $1$.
Their products are $A^{W+1}J_k$, $0\le k\le W$. For every unit starting
vector their $F_h$ images have pairwise squared distance at least
$(4/5)4^{-W}$ by (10.4). A deterministic assignment to $W$ endpoints
must merge two of them. For unit $u,v$,
$2-\|u+v\|\ge\|u-v\|^2/4$. Keeping this pair and bounding every
other history by the triangle inequality gives block loss at least

$$
2^{-(W+1)}\cdot\frac14\cdot\frac45\,4^{-W}
=8^{-W}/10.
$$

The convex decomposition of stochastic endpoint assignments used in §5
extends this bound to all randomized endpoints. Lemma 4.2 proves (10.1),
and (4.4) and logarithms give (10.2).

For an explicit logarithmic consequence, let
$C_\varepsilon=1+10b_\varepsilon\ge1$. Equation (10.2) implies
$n<C_\varepsilon(W+1)8^W$. If $W<\log_2 n$, then
$W+1\le2\log_2(n+2)$, so

$$
W>\frac{\log_2n-\log_2\log_2(n+2)-\log_2(2C_\varepsilon)}3.
$$

If $W\ge\log_2 n$, this same weaker lower bound is immediate. This
proves (10.3) for $n\ge1$. Thus even the independent backup rules out
every fixed online width. $\square$

## 11. Model boundaries and remaining estimates

**Proposition 11.1 (Free-seed pairwise fingerprints).** For every integer
$b\ge1$ and horizon $n$, there is a width-$2^b$ online summary such
that every fixed pair of distinct histories has collision probability
exactly $2^{-b}$ over an independent free seed. This pairwise guarantee
does not imply approximate qutrit recovery for the actual instrument.

**Proof.** Choose the seed $S=(a_1,\ldots,a_n)$ independently with each
$a_k$ uniform in $\mathbb F_2^b$, and update
$r_k=r_{k-1}+h_ka_k$, starting at zero. For two fixed distinct histories,
choose one differing coordinate. Conditional on all other seed coordinates,
the difference of their summaries is uniform, proving the probability.
For any fixed $b$ and fixed $\varepsilon<1/4$, (10.2) excludes recovery
for all sufficiently large $n$, despite this uniform pairwise guarantee.
A summary fingerprint is neither a simultaneous injection nor a recovery
channel. This explains why the joint losses (5.3) and (7.6) are needed.
$\square$

**Proposition 11.2 (Finite groups and identical letters).** If the full
qutrit projective branch classes generate a finite group $\mathcal F$,
exact recovery has peak width at most $|\mathcal F|$. In particular, the
unrotated $\theta=0$ instrument admits width six. If both branches equal
the same unitary $D$, width one suffices at each known horizon even when
$D$ has infinite projective order.

**Proof.** Accumulate the current projective class by left multiplication
and apply an inverse representative at termination; a global qutrit phase
does not affect the channel. For $\theta=0$, the actual $U_0,U_1$ generate
the permutation group $S_3$, so the accumulator has six values. If the
letters are identical, the product is the known $D^n$ and the decoder is
$D^{-n}$ without any history-dependent state. Infinite order by itself
therefore does not force growing width. $\square$

**Convention 11.3 (Endpoints and unresolved quantitative refinements).**
All approximate conclusions here use $0<\varepsilon<1/4$; the finite
necessary conditions (5.4), (7.5) and (10.2) retain their $n,\varepsilon$
dependence, including blocks longer than $n$. The formulas involving
$b_\varepsilon$ or division by $\sqrt\varepsilon$ are not evaluated at
zero error. At $\varepsilon=0$, the separate exact result
[OWN, Theorems 9.2–9.3][OWN] gives $W_n(0)=M_n(0)=2^n$ with the same
independent-seed and full-decoder permissions. A fixed-$n$ polynomial lower
bound diverging as $\varepsilon\downarrow0$ would contradict the always
available exact-history upper bound $2^n$.

The actual density proved in §6 determines the phase-resolved dimension
three. The fixed-error power and leading bit coefficient are (9.3).
The logarithmic gap between the two sides of (9.2), a numerical lower
bound for the specified $\gamma$, optimal joint $n,\varepsilon$ behavior
and constants, finite-precision control and table descriptions, and the
separate acquisition, communication and deterministic-clock costs remain
undetermined by these estimates. In particular (9.2) does not assert
$\Theta(n^{3/2})$ or a fully numerical near-optimal lower bound.

[OWN]: https://github.com/the-omega-institute/trureturing/blob/55208d97e98beb34acc9db6cdcd1c9da16331362/docs/develop/theory/AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md
[FIVE]: https://github.com/the-omega-institute/trureturing/blob/55208d97e98beb34acc9db6cdcd1c9da16331362/docs/develop/theory/AURIC_FIB_FIVE_WINDOW_QUANTUM_MEMORY.md
[BG]: https://content.ems.press/assets/public/full-texts/serials/jems/14/5/11408/online/10.4171-jems-337.pdf
[BG-DOI]: https://doi.org/10.4171/JEMS/337

## 追加锚（本行以下为增补区）
