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

## 12. Actual single-source maxima and exact lossless startup

**Convention 12.1 (Fixed model and complex vectors).** Throughout §§12–16
the instrument, embedding, untouched references, complete persistent state,
seed independence and averaged unhalved diamond criterion are exactly
Definitions 2.1–2.4. In particular the angle remains $\pi/6$ and the
decoder is an arbitrary CPTP map on $M_5$. The matrices
$F_j=\lambda^{-1}g_j$ are those of Definition 4.1; individual letters,
words and vectors are never rephased. Use the ordered basis $(f_1,f_2)$
of (2.1), and put $e_-=(1,0)^{\mathsf T}$ and
$e_+=(0,1)^{\mathsf T}$. These coordinates give

$$
F_0=\begin{pmatrix}
(1-i\sqrt3)/4&\sqrt3/2\\
(\sqrt3-3i)/4&-1/2
\end{pmatrix},\qquad F_1=F_0J,\qquad J=\operatorname{diag}(-1,1).
\tag{12.1}
$$

The widths below bound the complete state at every time. They do not
bound static table precision or deterministic schedules.

**Theorem 12.2 (Single-source maximum and lossless threshold).** Fix
integers $W\ge1$ and $n\ge0$. For deterministic, possibly many-to-one,
time-varying maps $f_{k,j}:[W]\to[W]$, write
$\phi_h=f_{n,h_n}\circ\cdots\circ f_{1,h_1}$, with the identity at
$n=0$. The quantity in Definition 4.1 has the attained normal form

$$
a_W(n)=
\max_{\substack{f_{k,j}:[W]\to[W],\ r_0\in[W]\\
                 t\in\mathbb C^2,\ \|t\|_2=1}}
\sum_{b=1}^W
\left\|2^{-n}\sum_{\substack{h\in\{0,1\}^n\\
                            \phi_h(r_0)=b}}F_ht\right\|_2.
\tag{12.2}
$$

Every maximizing path starts from the actual single-source tuple
$e_{r_0}t$ and is reachable by its displayed controller. One has

$$
a_W(0)=1,\qquad
a_W(n)=1\ \Longleftrightarrow\ W\ge2^{n-1}\quad(n\ge1).
\tag{12.3}
$$

Proof. Write $X_W=\ell_1([W];\mathbb C^2)$ with norm
$\|x\|_{1,2}=\sum_r\|x_r\|_2$, and let $L_k$ denote the layer in
(4.1). For a fixed product $L=L_n\cdots L_1$, decompose
$x=\sum_r e_rx_r$. If $\|x\|_{1,2}=1$, the triangle inequality gives

$$
\|Lx\|_{1,2}\le
\sum_{r:x_r\ne0}\|x_r\|_2
 \left\|L\left(e_r\frac{x_r}{\|x_r\|_2}\right)\right\|_{1,2}
\le\max_{r,\|t\|_2=1}\|L(e_rt)\|_{1,2}.
$$

Zero input blocks contribute zero. The reverse inequality follows because
every $e_rt$ is an allowed initial tuple. For fixed $W,n$, the product of
stochastic simplices and the complex unit sphere is compact, and the
objective is continuous, so the maxima are attained.

To reduce the layers, let $P(b\mid r)$ be any column-stochastic table.
For $f:[W]\to[W]$ set
$\alpha_P(f)=\prod_{r=1}^W P(f(r)\mid r)$ and
$D_f(b\mid r)=\mathbf1_{\{f(r)=b\}}$. Finite marginalization gives
$\sum_f\alpha_P(f)=1$ and
$\sum_f\alpha_P(f)D_f(b\mid r)=P(b\mid r)$.
Apply this identity to both label tables at each time. Expanding the
product of the layers expresses $L$ as a convex combination of products
of deterministic layers, with weights independent of the actual labels.
The norm of $L(e_rt)$ is at most the largest norm of these deterministic
products on that same input. Deterministic tables are already permitted,
giving equality of the maxima. The path expansion is exactly (12.2).
There are $W^{2Wn}$ table programs, $W$ starting states, and a compact
full complex sphere of choices of $t$. Maximization over this Cartesian
product can be performed in any order. No minimax exchange is involved.

For the sufficiency in (12.3), start at $e_+$ and discard the first
label. Since $Je_+=e_+$, both first-step vectors equal
$v=F_0e_+=(\sqrt3/2,-1/2)^{\mathsf T}$. Store the subsequent $n-1$
labels exactly. At time $k\ge1$ this uses $2^{k-1}$ states. Histories
with the same suffix $(h_2,\ldots,h_n)$ have identical full-phase vectors,
so the terminal sum of norms is one. Pad to width $W$ when needed.

For necessity, use the attained deterministic single-source maximum.
Each $F_ht$ is a unit vector. The terminal norm sum is at most one by
the triangle inequality. If it is one, equality holds separately in each
nonempty endpoint group. For unit vectors $v_1,\ldots,v_m$,

$$
m^2-\left\|\sum_{i=1}^m v_i\right\|_2^2
=\sum_{i<j}\|v_i-v_j\|_2^2.
$$

Thus equality requires all vectors within that group to coincide,
including their complex phases. The already established separation (5.2)
says that two distinct length-$n$ histories in the same determinant class
have distance at least $2^{-n}$ for every unit $t$. Hence one endpoint
contains at most one history from each of the two determinant classes,
and $2^n\le2W$. Empty endpoint groups cause no exception. Compact
attainment makes the inequality $a_W(n)<1$ strict below this threshold;
it supplies no quantitative size for that strict deficit. At $n=0$ the
empty product preserves the norm. $\square$

The normal form is used here for the actual startup statement and below
for the energy minimum. It is a convex reduction of a vector objective.
It neither determinizes the averaged recovery error nor finds a decoder
which works simultaneously for every qutrit direction. There is no
additional relaxed-to-reachable bridge for the maximum in (12.2): its
maximizers themselves have single-source reachable paths. A bound for
only one direction or a restricted set of controllers would still be
insufficient.

**Proposition 12.3 (Width one and necessary startup allowance).** For the
actual generators,

$$
a_1(0)=1,\qquad a_1(n)=2^{1-n}\quad(n\ge1).
\tag{12.4}
$$

For fixed $W$, the largest positive integer horizon with $a_W(n)=1$ is
$1+\lfloor\log_2W\rfloor$. Consequently, if constants $c>0$ and a
function $s(W)$ obey the proposed uniform envelope

$$
a_W(n)\le
\exp\{-cW^{-2/3}(n-s(W))_+\}\qquad(W\ge1,\ n\ge0),
\tag{12.5}
$$

then necessarily $s(W)\ge1+\lfloor\log_2W\rfloor$. In particular
$s(W)=K\ln(2W)$ requires $K\ge1/\ln2$. With $W\ge2$ and
$s(W)=K\ln W$, it requires $K\ge2/\ln2$. These are necessary conditions,
not a proof of (12.5) for either choice.

Proof. Width one leaves the unique layer

$$
M=(F_0+F_1)/2=F_0(I+J)/2
=\begin{pmatrix}0&\sqrt3/2\\0&-1/2\end{pmatrix}.
$$

It has operator norm one and $M^2=-M/2$. Thus
$M^n=(-1/2)^{n-1}M$ for $n\ge1$, proving (12.4).
Theorem 12.2 gives the largest lossless horizon. Substituting that horizon
in (12.5) forces its exponent to vanish. For $W=2^m$ the resulting
condition with $\ln(2W)$ is
$m+1\le K(m+1)\ln2$. For $\ln W$ on $W\ge2$, take $W=2$ and $n=2$.
At $W=1,n=1$, any formula using $s(W)=K\ln W$ instead would assert
$1\le e^{-c}<1$. Replacing $\ln W$ by $\ln(2W)$ removes this
contradiction but does not establish a decay estimate. $\square$

**Proposition 12.4 (Reachable width-two startup and recovery separation).**
There is an actual width-two single-source path with $N_0=N_1=N_2=1$.
Nevertheless at width one and horizon one every recovery protocol in
Definitions 2.3–2.4 has unhalved diamond error at least one, although
$a_1(1)=1$.

Proof. Start from $x_0=(e_+,0)$. At time one map every state to state
one for both labels. At time two map every state to state one on label
zero and to state two on label one. Then

$$
x_1=(v,0),\qquad
x_2=(F_0v/2,F_1v/2),\qquad v=F_0e_+.
\tag{12.6}
$$

Unitarity gives all three norms equal to one. In particular a universal
strict one-step loss asserted whenever the preceding reachable norm is
at least $3/4$ fails even at positive time.

For the recovery assertion let $Z=|e_-\rangle\langle\xi|$ in qutrit
coordinates, so $\|Z\|_1=1$. The fair uncorrected horizon-one channel
sends it to $|Me_-\rangle\langle\xi|=0$. At width one, for almost every
seed there is only one decoder input; every full-$H$ CPTP decoder sends
this zero operator to zero. Averaging over any independent seed still
annihilates $Z$, whereas the target sends it to $\iota(Z)$, of trace
norm one. This is already a diamond-norm witness without a reference.
It proves the bound for arbitrary full-$H$ decoders and hence explicitly
separates the necessary vector-survival condition (4.4) from sufficient
recovery. $\square$

## 13. Finite-support replacement of the entire averaged recovered channel

**Theorem 13.1 (Finite-horizon independent seed replacement).** For each
finite $W\ge1$ and $n\ge0$, every legal width-$W$ controller with a free
independent measurable standard-Borel seed has another legal controller
whose entire averaged recovered channel (2.2) is identical, with an
independent seed supported on at most

$$
W^{1+2Wn}
\tag{13.1}
$$

programs. Each selected program consists of one initial state and complete
deterministic update tables for all times and both labels. Its terminal
maps are CPTP maps on $M_5$ obtained by seed-weighted averaging of the
original terminal maps. The peak width remains at most $W$.

Proof. Let $\mu$ be the original seed law and $\pi_s$ the initial-state
law. Since the horizon is finite, intersect the full-measure sets on
which the width bound and the finitely many kernel and decoder
conditions hold. Use the measurable padded labels of Definition 2.3
to identify every state space there with a subset of $[W]$. Extend
unused states by any fixed stochastic transitions and CPTP decoders.
On the exceptional null set choose a fixed legal padded protocol.
This does not change (2.2).

Let $v=(r_0,(f_{k,j})_{k,j})$ range over the finite set of all such
programs, including tables at unused states. Define measurable weights

$$
\beta_s(v)=\pi_s(r_0)
 \prod_{k=1}^n\prod_{j=0}^1\prod_{r=1}^W
       T_{k,j,s}(f_{k,j}(r)\mid r),\qquad
\beta(v)=\int\beta_s(v)\,d\mu(s).
\tag{13.2}
$$

Empty products equal one. Marginalizing each table column gives
$\sum_v\beta_s(v)=1$, including zero entries, and hence
$\sum_v\beta(v)=1$. For a fixed history $h$, each pair
$(k,h_k)$ uses exactly one table column along its path; summing every
unused column gives one. Summing paths and initial states therefore gives

$$
p_s(r\mid h)=
 \sum_v\beta_s(v)\mathbf1_{\{\phi_h^v(r_0)=r\}}.
\tag{13.3}
$$

This is a distribution of complete tables sampled independently of the
actual acquired history, not a choice based on a future label.

For $\beta(v)>0$ put

$$
\overline D^{\,H}_{r,v}
=\frac1{\beta(v)}
 \int\beta_s(v)D^H_{r,s}\,d\mu(s).
\tag{13.4}
$$

The integral exists entrywise in the finite-dimensional vector space of
linear maps on $M_5$. Measurability is inherited from the original
family, and CPTP maps form a bounded closed convex set. More explicitly,
their Choi matrices are positive with the fixed trace-preserving partial
trace; weighted integration preserves both properties. Thus (13.4) is
CPTP on all of $M_5$. If $\beta(v)=0$, nonnegativity gives
$\beta_s(v)=0$ almost everywhere; omit that program. One may instead
give it any CPTP decoders and probability zero, with no division by zero.

Choose the new free seed $v$ with probability $\beta(v)$, independently
of the qutrit, reference and actual labels. Start at its $r_0$, follow
its tables and use (13.4). The new averaged recovered channel is

$$
2^{-n}\sum_{h,v}\beta(v)
 \overline D^{\,H}_{\phi_h^v(r_0),v}
       \circ\iota\circ\operatorname{Ad}_{Q_h}
=\int 2^{-n}\sum_{h,r}p_s(r\mid h)
 D^H_{r,s}\circ\iota\circ\operatorname{Ad}_{Q_h}\,d\mu(s).
\tag{13.5}
$$

Substitute (13.4), interchange the finite sums with the bounded integral,
and apply (13.3) to prove this equality. There are $W$ initial states
and $W^{2Wn}$ complete table programs, proving (13.1).
Equality as complex-linear maps also gives equality after tensoring with
every untouched finite reference, and therefore identical averaged
unhalved diamond error. $\square$

**Convention 13.2 (Scope of the replacement).** Theorem 13.1 is exact for
the specified finite horizon and averaged channel. The new terminal
decoders can be mixtures of many original decoders. It asserts neither
that one original seed succeeds nor that one deterministic program with
one original decoder has no larger error. It gives no efficient
algorithm, finite-precision description bound or horizon-uniform finite
list of programs. Nonuniform changing tables and arbitrary measurable
seed-dependent decoders remain allowed. Seed independence and inclusion
of every persistent variable in the counted state are essential to the
factorization (13.3).

For the necessary condition (4.4) one can also retain the original seed:
for each fixed unit $t$, on the common full-measure padded set
$N_{n,s}\le a_W(n)$, whence
$\|\mathcal C_n(Z_t)\|_1\le\int N_{n,s}\,d\mu(s)\le a_W(n)$.
This integration uses a uniform conditional upper bound, not conditional
success and not a measurable selection of an optimal seed.

## 14. Same-controller backward vectors and occupation-weighted energy

**Definition 14.1 (Actual dual fields).** Use the complex inner product
$\langle y,x\rangle=y^\dagger x$, conjugate-linear in its first
argument, and real pairing
$[y,x]=\operatorname{Re}\sum_r\langle y_r,x_r\rangle$.
The real norm dual of $X_W$ is
$Y_W=\ell_\infty([W];\mathbb C^2)$, with
$\|y\|_{\infty,2}=\max_r\|y_r\|_2$.
For a fixed deterministic controller $f$ let $L_k$ be its actual forward
layer and define its adjoint by

$$
(L_k^\ast y)_r
=\frac12\sum_{j=0}^1 F_j^\dagger y_{f_{k,j}(r)}.
\tag{14.1}
$$

For terminal $y$, define $b_n=y$ and
$b_k=L_{k+1}^\ast b_{k+1}$ for $0\le k<n$.
For a fixed starting state $r_0$, let the scalar occupation law of this
same controller under the actual fair labels be

$$
p_0(r)=\mathbf1_{\{r=r_0\}},\qquad
p_{k+1}(s)=\frac12\sum_{r,j}
 p_k(r)\mathbf1_{\{f_{k+1,j}(r)=s\}}.
\tag{14.2}
$$

The $b_k$ are backward analysis fields. They are not additional stored
variables, reverse stochastic kernels or intermediate quantum operations.

**Theorem 14.2 (Exact dual maximum and minimum energy).** At the same
width $W$ and for the actual $F_j$, one has

$$
\begin{aligned}
\|L_n\cdots L_1(e_{r_0}t)\|_{1,2}
&=\max_{\|y\|_{\infty,2}\le1}
 \operatorname{Re}\langle b_0(r_0),t\rangle,\\
a_W(n)
&=\max_{\substack{f,r_0\\\|y_s\|_2=1\ (s\in[W])}}
 \|b_0(r_0)\|_2 .
\end{aligned}
\tag{14.3}
$$

For each fixed $f,r_0,y$ with all terminal norms one, the exact identity is

$$
1-\|b_0(r_0)\|_2^2
=\frac14\sum_{k=0}^{n-1}\sum_r p_k(r)
 \left\|F_0^\dagger b_{k+1}(f_{k+1,0}(r))
       -F_1^\dagger b_{k+1}(f_{k+1,1}(r))\right\|_2^2 .
\tag{14.4}
$$

In particular,

$$
1-a_W(n)^2
=\frac14\min_{\substack{f,r_0\\\|y_s\|_2=1\ (s\in[W])}}
 \sum_{k=0}^{n-1}\sum_r p_k(r)
 \left\|F_0^\dagger b_{k+1}(f_{k+1,0}(r))
       -F_1^\dagger b_{k+1}(f_{k+1,1}(r))\right\|_2^2 .
\tag{14.5}
$$

Every $p_k$ and $b_k$ inside a candidate in this minimum must come from
that candidate's same controller $f$, with (14.1)–(14.2).
There is no positive-occupation assumption.

Proof. For $x\in X_W$, Cauchy–Schwarz gives
$[y,x]\le\|x\|_{1,2}$ on the dual unit ball. Equality is attained by
$y_s=x_s/\|x_s\|_2$ at nonzero blocks; at a zero block any unit vector
works. Expanding (4.1) in the pairing proves (14.1) and
$[y,L_kx]=[L_k^\ast y,x]$. Unitarity and the triangle inequality imply
$\|L_k^\ast y\|_{\infty,2}\le\|y\|_{\infty,2}$ even for many-to-one
maps. Iterating gives the first identity in (14.3).

For fixed $f,r_0$, maximize also over unit $t$. The maximum of
$\operatorname{Re}\langle b_0(r_0),t\rangle$ is
$\|b_0(r_0)\|_2$, including the zero case. All maxima exist on compact
finite-dimensional sets and their order can be exchanged. They may
be restricted to unit terminal blocks: choose a maximizing $t$ for
this fixed forward product and choose unit norm-supporting $y$ for its
terminal tuple, arbitrarily at zero blocks. This gives the full forward
maximum. Conversely, for every such $y$ its initial norm is bounded by
that forward maximum, by the same dual formula maximized over $t$.
Theorem 12.2 now proves the second identity in (14.3). This argument
optimizes only maxima; it does not interchange a minimum with a maximum.

To prove the energy identity, put
$E_k=\sum_r p_k(r)\|b_k(r)\|_2^2$. Apply the usual complex Hilbert-space
parallelogram identity inside (14.1),

$$
\left\|\frac{u+v}{2}\right\|_2^2
=\frac{\|u\|_2^2+\|v\|_2^2}{2}
 -\frac{\|u-v\|_2^2}{4},
$$

with $u=F_0^\dagger b_{k+1}(f_{k+1,0}(r))$ and
$v=F_1^\dagger b_{k+1}(f_{k+1,1}(r))$. Multiply by $p_k(r)$ and
sum over $r$. Unitarity and the same occupation recursion (14.2) identify
the first sum with $E_{k+1}$. Hence

$$
E_{k+1}-E_k
=\frac14\sum_r p_k(r)\|u-v\|_2^2.
$$

Now $E_0=\|b_0(r_0)\|_2^2$ and $E_n=1$, so telescoping proves (14.4).
For terminal norms at most one the general formula has the additional
nonnegative right-hand term
$\sum_s p_n(s)(1-\|y_s\|_2^2)$. No term divides by $p_k(r)$, so zero
occupancies contribute zero without restricting the corresponding field.
All fields are built from the same complex $F_j^\dagger$; their phases
are retained.

The finite set of $f,r_0$ and the product of complex unit spheres is
compact. By (14.3), its maximum of $\|b_0(r_0)\|_2^2$ is $a_W(n)^2$.
Taking one minus this maximum in (14.4) proves the attained minimum
(14.5). At $n=0$ the sum is empty and both sides vanish. $\square$

**Proposition 14.3 (Stochastic version for the original controller).**
For a stochastic controller at a fixed seed, replace (14.1) by

$$
(L_{k+1}^\ast b_{k+1})_r
=\sum_{j,s}\nu_{k,r}(j,s)F_j^\dagger b_{k+1}(s),\qquad
\nu_{k,r}(j,s)=\tfrac12T_{k+1,j}(s\mid r),
\tag{14.6}
$$

and use
$p_{k+1}(s)=\sum_{r,j}p_k(r)\nu_{k,r}(j,s)$ from the same stochastic
controller. If $z_{j,s}=F_j^\dagger b_{k+1}(s)$, the exact telescoping
identity is

$$
\begin{aligned}
1-\|b_0(r_0)\|_2^2
={}&\sum_s p_n(s)(1-\|y_s\|_2^2)\\
&+\frac12\sum_{k,r}p_k(r)
 \sum_{j,s,j',s'}\nu_{k,r}(j,s)\nu_{k,r}(j',s')
       \|z_{j,s}-z_{j',s'}\|_2^2 .
\end{aligned}
\tag{14.7}
$$

Here $p_0=e_{r_0}$, the time sum is $0\le k<n$, and the terminal
norms are at most one. With an initial probability law $\pi$, replace
$\|b_0(r_0)\|_2^2$ by $\sum_r\pi(r)\|b_0(r)\|_2^2$.

Proof. For the finite probability vector $\nu_{k,r}$, expansion of the
squared norm of $\sum\nu_{k,r}z_{j,s}$ gives its mean squared norm minus
one half the displayed ordered-pair squared-distance sum. Multiply by
$p_k(r)$ and use the same stochastic occupation recursion to obtain
$E_{k+1}-E_k$ as that variance term. Telescoping and
$1-E_n=\sum_s p_n(s)(1-\|y_s\|_2^2)$ give (14.7).
The adjoint pairing and contraction follow by the same finite expansion.
Zero transition probabilities and zero occupancies have zero weight.
For deterministic tables this variance is exactly the one-quarter term
in (14.4). These identities hold almost everywhere for the original
measurable seed family and can be integrated, since the finite sums are
measurable and bounded. For the extremum $a_W(n)$ the deterministic
minimum (14.5) already suffices by Theorem 12.2. $\square$

## 15. Permutation-program suppliers and actual transfer obstructions

**Convention 15.1 (The CDG supplier and its conditions).** Cohen, Doron
and Goldgraber, *A Forward–Backward Weight Analysis of INW for Permutation
Branching Programs*, arXiv:2607.18168v2 [CDG][CDG], Theorem 3.1, analyzes
binary read-once permutation branching programs. Under Definition 2.2,
both label transitions at every layer are permutations of the same
$w$ states. Definition 2.3 tests scalar Boolean acceptance probability
against uniform input bits. For $0<\eta\le1$, the paper takes spectral
expander parameter $\theta_{\rm exp}=\eta/(32w^3)$ and obtains an
$\eta$-fooling INW generator with seed length
$O((\log w+\log(1/\eta))\log n)$; a single layer uses one fair bit.
Definition 2.4 requires undirected regular expanders with normalized
adjacency minus the averaging matrix of operator norm at most
$\theta_{\rm exp}$. Their degrees are polynomial in $1/\theta_{\rm exp}$
and independent of $n$; identity layers pad other lengths to powers of
two.

For comparison with the actual deterministic controller, use the paper's
row matrices
$P_{k,j}(r,s)=\mathbf1_{\{f_{k,j}(r)=s\}}$ and
$T_k=(P_{k,0}+P_{k,1})/2$. These are the transposes of the column
tables used in (4.1). In the notation of [CDG, §3.1][CDG-WEIGHTS], the
scalar forward and backward recursions and weights are

$$
\begin{aligned}
p_{k+1}^{\mathsf T}&=p_k^{\mathsf T}T_{k+1},&
\mathfrak F_{[n]}(p_0)
 &=\sum_{k=0}^{n-1}
   \|p_k^{\mathsf T}(P_{k+1,0}-P_{k+1,1})\|_1,\\
q_k&=T_{k+1}q_{k+1},&
\mathfrak B_{[n]}(q_n)
 &=\sum_{k=0}^{n-1}
   \|(P_{k+1,0}-P_{k+1,1})q_{k+1}\|_1 .
\end{aligned}
\tag{15.1}
$$

The paper's Lemma 3.2 proves the length-independent permutation bounds

$$
\mathfrak F_I(p)\le2\sum_{r<s}|p_r-p_s|\le2w\|p\|_1,\qquad
\mathfrak B_I(q)\le2\sum_{r<s}|q_r-q_s|\le2w\|q\|_1.
\tag{15.2}
$$

Backward propagation there is a reversed permutation walk. Proposition
3.4 bounds the INW expander-product discrepancy by
$\theta_{\rm exp}\mathfrak F_L(p)\mathfrak B_R(q)$.
Proposition 3.5 then proves, for $c\ge2$ and
$\theta_{\rm exp}\le1/(8c^2w^3)$, the direct bilinear bound

$$
|p^{\mathsf T}(\widetilde T_I-T_I)q|
 \le c\theta_{\rm exp}\mathfrak F_I(p)\mathfrak B_I(q)
\tag{15.3}
$$

on dyadic intervals. Its induction uses (15.2), including the estimate
$\mathfrak F_R(\delta)\le2w\|\delta\|_1$ for a propagated error vector.
This is a known nonaccumulation estimate for PRG-versus-uniform error.
It is not a decay estimate for the actual uniform-input vector objective
(12.2). Equations (15.1)–(15.3) are cited supplier statements, used to
specify the hypotheses tested by the following actual-model examples.

**Proposition 15.2 (Many-to-one scalar weight counterfamilies).** At
unchanged finite controller width, the analogues of (15.2) for arbitrary
legal deterministic transitions fail: there are width-two forward
weights $2n$ and width-three backward weights $n$ for every horizon $n$.
Attach the unchanged actual $F_j$ to each label in both families.

Proof. For width two use the same maps at every time, each sending every
state to state one on label zero and to state two on label one. Their
row matrices and a stationary fair occupation law are

$$
P_0=\begin{pmatrix}1&0\\1&0\end{pmatrix},\qquad
P_1=\begin{pmatrix}0&1\\0&1\end{pmatrix},\qquad
p^{\mathsf T}=(1/2,1/2).
\tag{15.4}
$$

Thus $p^{\mathsf T}T=p^{\mathsf T}$ but
$p^{\mathsf T}P_0=(1,0)$ and $p^{\mathsf T}P_1=(0,1)$.
Each forward weight is two, giving $\mathfrak F_{[n]}(p)=2n$.
Both states have positive occupation; starting from a single state also
gives weight two at the first step and the same stationary law thereafter.
For the stationary initial law the first bound in (15.2) would be zero,
and even $2w\|p\|_1=4$ is exceeded for $n>2$.
For example $P_0^{\mathsf T}$ has row sums two and zero, so it is not a
reverse stochastic kernel in the row convention.

For width three let
$f_0=(1,2,1)$ and $f_1=(1,2,2)$ on states $(1,2,3)$, and take
$q=(0,1,1/2)^{\mathsf T}$. The associated row matrices obey

$$
Tq=q,\qquad (P_0-P_1)q=(0,0,-1)^{\mathsf T}.
\tag{15.5}
$$

Starting with terminal $q_n=q$ gives the same $q_k=q$ at every time
and hence $\mathfrak B_{[n]}(q)=n$. The two bounds in (15.2) would be
four and nine, respectively. If the actual controller starts at state
three, its occupation there is one at time zero and zero for every
$k\ge1$: $p_0=(0,0,1)^{\mathsf T}$ and
$p_k=(1/2,1/2,0)^{\mathsf T}$ for every $k\ge1$, since both maps
send all states into $\{1,2\}$ and fix states one and two.
Starting in state one gives $p_k=(1,0,0)^{\mathsf T}$ for all $k\ge0$.
Thus this unweighted backward sum charges state three at each step,
although its forward occupation is zero after the first step
(and at every time when starting in state one). In (14.4) the occupation
is instead the one belonging to the same chosen controller and initial
state. Both families are legal actual transition tables; no successful
recovery is asserted for them. They disprove a transplantation of
(15.2), not the permutation theorem or a loss-conditioned alternative.
$\square$

**Proposition 15.3 (Scalar acceptance does not determine actual phase
observables).** At width one, all the scalar weights in (15.1) can
vanish while different label laws give different actual vector
expectations. For the actual generators at horizon two and $t=e_-$,
uniform independent labels give zero, whereas the law assigning
probability $1/2$ to each of $00,11$ gives a vector of norm $1/2$.

Proof. The sole controller has $P_0=P_1=[1]$, so every scalar acceptance
test of this controller is constant and its weights vanish. Uniform
labels give $M^2e_-=0$. Put $a=(1-i\sqrt3)/4$. Direct multiplication of
(12.1) gives

$$
\frac{F_0^2+F_1^2}{2}e_-=aF_0e_-,
\qquad |a|=1/2.
\tag{15.6}
$$

Unitarity proves the asserted norm. Thus even exact agreement on all
scalar tests of this controller misses the actual complex observable.
The correlated label law is a test of observable sufficiency; it is
not substituted for the physical fair labels, and no claim is made that
it is a CDG generator. $\square$

For each fixed dual test in (14.3), the actual observable is

$$
g_{f,r_0,t,y}(h)=
 \operatorname{Re}\langle y_{\phi_h(r_0)},F_ht\rangle\in[-1,1],
\tag{15.7}
$$

not merely terminal acceptance of the controller. A direct faithful
permutation simulation is available at finite horizon by retaining an
$n$-bit register: at time $k$ XOR label $j$ into bit $k$. Each such
update is a permutation of $2^n$ states, and the terminal register
determines both $\phi_h(r_0)$ and the full-phase $F_h$. If a generator
fools every terminal accepting set for this register within $\eta$, the
two terminal laws have total variation at most $\eta$. Writing a
function $g\in[-1,1]$ as $2u-1$ with $0\le u\le1$, and integrating
the indicators of $\{u>z\}$ for $0\le z\le1$, bounds its expectation
difference by $2\eta$. Thus the CDG theorem can control (15.7) through
this register, but with width $2^n$ its seed bound is
$O((n+\log(1/\eta))\log n)$. This supplies no improved width-$W$
recovery bound. A transfer retaining small width and controlling the
phase-sensitive observable would require its own proved reduction and
cost estimate. The counterfamilies above do not exclude all such
reductions, all forward–backward methods or other approaches.

## 16. Quantitative boundary of the energy representation

**Definition 16.1 (Minimum energy and a sufficient unresolved target).**
Let $\mathcal Q_W(n)$ denote the minimum of the sum on the right of
(14.5), before the factor $1/4$. Its exact value as a representation is

$$
\mathcal Q_W(n)=4(1-a_W(n)^2).
\tag{16.1}
$$

A sufficient uniform coercive estimate would be the existence of
constants $c,K>0$ such that, for every $W\ge1$ and $n\ge0$,

$$
\mathcal Q_W(n)\ge
4\left(1-\exp\{-2cW^{-2/3}(n-K\ln(2W))_+\}\right).
\tag{16.2}
$$

Equivalently, it would give (12.5) with $s(W)=K\ln(2W)$.
Estimate (16.2) is unresolved. Nonnegativity and telescoping alone do
not prove it. The zero energies throughout the exact startup range in
(12.3), including the width-two path (12.6), are compatible with
(14.4)–(14.5). By Proposition 12.3 a valid estimate of this form must
allow at least that startup. Finite convolutions of the actual
two-letter walk have finite support and remain singular to sphere Haar
measure; the auxiliary smoothing in Theorem 7.1 is not smoothing of the
physical walk.

**Proposition 16.2 (Conditional sharp fixed-error consequence).** If
(16.2) holds, then for each fixed $0<\varepsilon<1/4$ the actual
recovery problem satisfies
$W_n(\varepsilon)=\Theta_\varepsilon(n^{3/2})$.
This is only an implication with the unproved premise (16.2).

Proof. By (16.1) the premise gives
$a_W(n)\le\exp\{-cW^{-2/3}(n-K\ln(2W))_+\}$.
For a successful width $W$, (4.4) implies

$$
b_\varepsilon\ge cW^{-2/3}(n-K\ln(2W))_+.
$$

If $W\ge n^{3/2}$ the required lower bound already holds. Otherwise
$\ln(2W)\le\ln2+(3/2)\ln n$, so for all sufficiently large $n$,
depending only on $K$, the positive part is at least $n/2$. Then

$$
W\ge\left(\frac{c}{2b_\varepsilon}\right)^{3/2}n^{3/2}.
$$

Theorem 8.4 supplies the unchanged upper bound. Combining the two cases
proves the conditional statement. $\square$

**Convention 16.3 (Reused results and remaining mathematical scope).**
The same-determinant-class separation (5.2), phase-resolved ball estimate
(7.2), same-history loss identity (7.6), spectral block bounds and
stochastic rounding construction are existing results of §§5–8.
The convex table expansion, norm duality and Hilbert variance identities
are used only inside the actual-model deductions above. In particular a
static Haar quantization loss is not a dynamic occupation-weighted
coercivity theorem. The external nonaccumulation input used for comparison
is the direct bilinear statement of [CDG, Propositions 3.4–3.5][CDG-ERROR],
with its permutation and scalar-test conditions.

Theorem 9.1 remains the established fixed-error rate:
$c_{\gamma,\varepsilon}(n/\ln n)^{3/2}\le W_n(\varepsilon)
\le C_\varepsilon n^{3/2}$ in its stated range, with growth power $3/2$
and leading bit coefficient $3/2$. No logarithmic improvement or
unconditional repaired exponential bound follows from §§12–15.
A bound such as (16.2) is sufficient, not shown necessary for sharp
actual recovery; vector survival tests one direction at a time and
does not incorporate all decoder constraints, as Proposition 12.4
demonstrates. The cited overlap does not constitute an exhaustive
literature classification or a claim of novelty. These are ordinary
finite-dimensional mathematical proofs, without a Lean/kernel
certificate or a physical or QFT assertion.

[CDG]: https://arxiv.org/html/2607.18168v2
[CDG-WEIGHTS]: https://arxiv.org/html/2607.18168v2#S3.SS1
[CDG-ERROR]: https://arxiv.org/html/2607.18168v2#S3.SS3

## 追加锚（本行以下为增补区）

## 17. From an actual backward field to full-qutrit recovery with a parity bit

**Definition 17.1 (Field energy and determinant parity).** Fix integers
$W\ge1$, $n\ge0$, a starting state $r_0\in[W]$, deterministic changing
maps $f_{k,j}:[W]\to[W]$, and terminal vectors $y_s\in\mathbb C^2$
with $\|y_s\|_2=1$ for every $s$. Use precisely the backward fields
$b_k$ and occupations $p_k$ of (14.1)–(14.2) for this same controller.
Write $R_n(h)=\phi_h(r_0)$ and set

$$
\begin{aligned}
\beta&=\|b_0(r_0)\|_2,\\
\mathscr E(f,r_0,y)
&=\sum_{k=0}^{n-1}\sum_r p_k(r)
 \left\|F_0^\dagger b_{k+1}(f_{k+1,0}(r))
       -F_1^\dagger b_{k+1}(f_{k+1,1}(r))\right\|_2^2,\\
\omega&=e^{2\pi i/3},\qquad
\eta(h)=\sum_{k=1}^n h_k\pmod2,\qquad
 d_\eta=\omega^n(-1)^\eta .
\end{aligned}
\tag{17.1}
$$

The $F_j$ remain exactly (12.1), with their full complex phases. The
energy here is a mathematical squared-norm functional. It specifies no
Hamiltonian, physical energy, dynamics of a quantum field, or QFT model.
By Theorem 14.2, $0\le\beta\le1$ and
$\mathscr E=4(1-\beta^2)$. Let $S=[\xi\ f_1\ f_2]$ be the unitary
qutrit change of basis in Theorem 2.2. Thus
$Q_h=\lambda^n S(1\oplus F_h)S^\dagger$.

**Theorem 17.2 (Paid-parity operational bridge).** For every field in
Definition 17.1 there is a legal controller of peak width at most $2W$
with deterministic classical updates and one terminal full-$H$ unitary,
whose averaged encoded error satisfies

$$
\|\mathcal E_n-\iota\|_\diamond
\le\min\{2,(1-\beta)(3+\beta)\}
\le\min\{2,3\mathscr E(f,r_0,y)/4\}.
\tag{17.2}
$$

The norm is unhalved and includes every untouched finite reference. The
complete persistent state is $(r,\eta)\in[W]\times\{0,1\}$; the extra
bit stores actual determinant parity. No intermediate quantum operation,
extra quantum register, label resampling, postselection, reference access,
or shared random seed is needed.

Proof. Iterating (14.1) along the same actual fair histories gives

$$
2^{-n}\sum_h F_h^\dagger y_{R_n(h)}=b_0(r_0).
\tag{17.3}
$$

For $\beta>0$ choose $t=b_0(r_0)/\beta$; for $\beta=0$ choose any fixed
unit $t$. In both cases $b_0(r_0)=\beta t$. The standard quaternionic
completion of a complex two-vector is

$$
C(z)=\begin{pmatrix}z_1&-\overline z_2\\
z_2&\overline z_1\end{pmatrix},\qquad
C(z)^\dagger C(z)=\|z\|_2^2I_2,\qquad
\det C(z)=\|z\|_2^2 .
\tag{17.4}
$$

For unit $z$, this is the $SU(2)$ matrix with first column $z$. It is
the same real quaternion algebra used in §8, with different real
coordinates. Calculation in (12.1) gives
$\det F_0=\omega$ and $\det F_1=-\omega$. Multiplicativity therefore
retains the exact identity $\det F_h=d_{\eta(h)}$, including the empty
product. Define the static terminal table

$$
\Gamma_{s,\eta}
 =C(y_s)\operatorname{diag}(1,d_\eta)C(t)^\dagger,\qquad
\mathsf V_h=\Gamma_{R_n(h),\eta(h)}^\dagger F_h.
\tag{17.5}
$$

Every $\Gamma_{s,\eta}$ is unitary, sends $t$ to $y_s$, and has
$\det\Gamma_{s,\eta}=d_\eta$. Hence $\mathsf V_h\in SU(2)$, and
(17.3) says

$$
\left(2^{-n}\sum_h\mathsf V_h^\dagger\right)t=\beta t.
$$

To pass from one vector to the whole matrix, use the real vector space
$\mathbb H_2=\{C(z):z\in\mathbb C^2\}$, closed under real sums and
adjoints and containing $SU(2)$ and real scalar matrices. Every
$Q\in\mathbb H_2$ satisfies $Q^\dagger Q=\alpha I_2$ for some
$\alpha\ge0$, by (17.4). If $Qt=0$ for a unit $t$, then $\alpha=0$
and $Q=0$. Apply this to
$Q=2^{-n}\sum_h\mathsf V_h^\dagger-\beta I_2$ and take adjoints:

$$
2^{-n}\sum_h\mathsf V_h=\beta I_2.
\tag{17.6}
$$

This uses the standard completion and rigidity inside the source-specific
construction, rather than a phase quotient or a simultaneous assumption
about all starting directions.

The classical update, starting from $(r_0,0)$, is

$$
(r,\eta)\longmapsto(f_{k,j}(r),\eta\mathbin\oplus j).
\tag{17.7}
$$

At the known horizon apply the full-$H$ unitary

$$
\mathcal U^H_{s,\eta}
 =BS(1\oplus\Gamma_{s,\eta}^\dagger)S^\dagger B^\dagger
       +(I_5-P_R).
\tag{17.8}
$$

Its summands are unitary on the orthogonal spaces $R$ and $R^\perp$.
On the actual branch the corrected qutrit matrix is
$\lambda^n S(1\oplus\mathsf V_h)S^\dagger$.
Only the common scalar $\lambda^n$ on the entire qutrit disappears in
its channel. Thus the error equals that of
$\Lambda=2^{-n}\sum_h\operatorname{Ad}_{U_h}$ relative to identity,
where $U_h=1\oplus\mathsf V_h$, by the trace-norm isometry of Lemma 3.1
and unitary change of qutrit coordinates. All phases between $\xi$ and
$T$ are retained.

Put $D=\mathbb E_hU_h=1\oplus\beta I_2$. Expanding around the mean,
with the same actual uniform history law throughout, gives the exact CP
decomposition

$$
\begin{aligned}
\Lambda&=\operatorname{Ad}_D+\Psi,\\
\Psi(X)&=\mathbb E_h[(U_h-D)X(U_h-D)^\dagger],\\
\Psi^\dagger(I_3)&=I_3-D^\dagger D=(1-\beta^2)P_T,
\qquad P_T=0\oplus I_2.
\end{aligned}
\tag{17.9}
$$

The mixed terms vanish because $\mathbb E_h(U_h-D)=0$.
For completeness, the standard CP norm identity used here follows in all
reference dimensions from a Stinespring operator $A$ for $\Psi$:
$A^\dagger A=\Psi^\dagger(I)$, multiplication by $A\otimes I$ costs
at most $\|A\|^2$, and partial trace is trace-norm contractive, including
on non-Hermitian operators by trace/operator duality. Therefore
$\|\Psi\|_\diamond\le\|\Psi^\dagger(I)\|_{\rm op}$.
A unit eigenstate for the largest eigenvalue gives the reverse inequality
by positivity and trace, so here
$\|\Psi\|_\diamond=1-\beta^2$.

For every complex operator $X$ on the qutrit and any reference, suppressing
identity tensor factors,

$$
DXD^\dagger-X=(D-I)XD^\dagger+X(D^\dagger-I).
$$

Since $\|D\|_{\rm op}=1$ and $\|D-I\|_{\rm op}=1-\beta$, this proves
$\|\operatorname{Ad}_D-\operatorname{id}\|_\diamond\le2(1-\beta)$.
Consequently (17.9) gives
$\|\Lambda-\operatorname{id}\|_\diamond
\le1-\beta^2+2(1-\beta)=(1-\beta)(3+\beta)$.
The distance between channels is at most two, and

$$
3(1-\beta^2)-(1-\beta)(3+\beta)=2\beta(1-\beta)\ge0.
$$

Together with (14.4), these are exactly (17.2). The mean-cancellation
estimate is the standard mixture mechanism: [Hastings, Lemma 1][HASTINGS]
gives variance plus twice the mean displacement. In this application
$(\mathsf V_h-\beta I)^\dagger(\mathsf V_h-\beta I)$ is scalar by the
quaternion algebra, so its averaged operator-norm variance is exactly
$1-\beta^2$. The random index is the entire actual history, without an
independent-gate hypothesis or a uniform small error on each history.

At $\beta=0$, (17.6) follows without division, and (17.2) has the channel
cap two. At $\beta=1$, (17.9) is zero variance; every positive-probability
$U_h=D=I_3$, giving exact recovery. At $n=0$, $b_0(r_0)=y_{r_0}$,
$\beta=1$, $d_0=1$ and the reached $\Gamma$ is identity, giving the
identity correction. Unreachable states may have arbitrary unit terminal
vectors and padded updates; their occupation weights are zero and no
formula divides by them. The unit-terminal hypothesis is essential:
with subunit terminal data the additional deficit described after (14.4)
remains. Static real choices of $t,y,\Gamma$, exact control precision,
calibration and deterministic clock information are separate resources
under Definition 2.3. Only $(r,\eta)$ is run-dependent persistent memory.
$\square$

**Proposition 17.3 (Actual same-width and phase boundaries).** The
factor-two construction cannot be replaced by an unconditional same-width
converse on the basis of $a_W(n)$ alone. For the actual width-one,
horizon-one controller, $a_1(1)=1$ but the best unhalved recovery error is
at least one. Omitting the retained parity from (17.5), or identifying
scalar phases on $T$, can destroy the claimed entire-code recovery.

Proof. The first assertion is Proposition 12.4: the actual average
$M=(F_0+F_1)/2$ kills $e_-$ and hence kills
$|e_-\rangle\langle\xi|$ before every sole decoder, even with a free
independent seed. A width-two controller records the actual label and
applies its full inverse, giving exact recovery.
For the completion example take $y=F_0e_+$ at $W=n=1$. Then
$b_0=e_+$ and $\beta=1$, since $Je_+=e_+$. If the table uses
$\Gamma=F_0$ for both histories, its corrected matrices are $I_2,J$;
their mean is $\operatorname{diag}(0,1)$, not $I_2$.
Finally $1\oplus(-I_2)$ sends $|e_-\rangle\langle\xi|$ to its
negative; its trace-norm discrepancy on this norm-one operator is two.
A scalar on $T$ is therefore not an irrelevant scalar on the qutrit.
These examples do not prove that every controller needs an additional bit,
or that one bit is minimal at every positive error. $\square$

## 18. Attained operational error and vector-width comparison

**Definition 18.1 (Operational error at a fixed width).** For integers
$W\ge1$, $n\ge0$, let $\varepsilon_{\rm op}(W,n)$ be the infimum of
$\|\mathcal E_n-\iota\|_\diamond$ over all legal width-at-most-$W$
protocols in Definitions 2.3–2.4, including their full-$H$ CPTP decoders
and free independent seeds. For this infimum the same resource class is
used without a success threshold. Define, for $0\le\delta<1$,

$$
V_n(\delta)=\min\{W\ge1:a_W(n)\ge1-\delta\}.
\tag{18.1}
$$

At zero error $W_n(0)$ has the separate exact meaning in Convention 11.3.
The width minima are finite because retaining the history is feasible.

**Theorem 18.2 (Attainment and quantitative comparison).** The operational
infimum is a minimum for every fixed $W,n$. For all such integers,

$$
1-a_W(n)\le\varepsilon_{\rm op}(W,n),\qquad
\varepsilon_{\rm op}(2W,n)
 \le(1-a_W(n))(3+a_W(n))\le4(1-a_W(n)).
\tag{18.2}
$$

Consequently, for $0<\varepsilon<1/4$,

$$
V_n(\varepsilon)\le W_n(\varepsilon)
       \le2V_n(\varepsilon/4).
\tag{18.3}
$$

The separately defined zero-error endpoints are

$$
\begin{aligned}
V_n(0)&=2^{n-1},&W_n(0)&=2^n&& (n\ge1),\\
V_0(\delta)&=1,&W_0(\varepsilon)&=1,
&\varepsilon_{\rm op}(W,0)&=0 .
\end{aligned}
\tag{18.4}
$$

Here the $n=0$ widths also include zero error, and the stated $V_0$ range
is $0\le\delta<1$. In particular the factor-two width comparison is
sharp at zero error, without asserting a same-width approximate converse.

Proof. Reuse Theorem 13.1. There are finitely many complete deterministic
programs, $P=W^{1+2Wn}$, each with one initial state and all changing
label tables. Every feasible averaged channel has a representation as a
probability mixture of these programs with program/state-indexed full-$H$
CPTP decoders. Conversely every such mixture is legal: use its program
index as the independent free seed. Include programs of weight zero with
arbitrary decoders. The product of the $P$-simplex with the finitely many
Choi sets of these decoders is compact. Indeed each Choi set is closed,
positive, has the fixed trace-preserving partial trace, and hence fixed
trace five and bounded norm. The map from these parameters to the
averaged channel (13.5) is continuous. Its compact image is exactly the
feasible set, so the continuous finite-dimensional diamond error attains
its minimum. This assertion neither selects one successful original seed
nor determinizes the averaged error.

For the first inequality of (18.2), the proof of Theorem 4.3 applies to
every candidate error, not just to a candidate below $1/4$. The norm-one
coherence $Z_t=|t\rangle\langle\xi|$ has corrected output norm at most
$a_W(n)$, even for arbitrary stochastic tables and almost every seed.
Thus the reverse triangle inequality gives error at least $1-a_W(n)$.
Averaging uses the uniform bound at each seed, not conditional success.
Take the infimum, or its attained minimum.

For the upper bound, Theorems 12.2 and 14.2 supply an attained
deterministic $f,r_0,y$ with unit terminal blocks and
$\|b_0(r_0)\|_2=a_W(n)$. Theorem 17.2 applies to this very controller,
producing width at most $2W$ and the middle bound of (18.2).
The final inequality uses $0\le a_W(n)\le1$.
Apply the first bound to an optimal successful width to get the left side
of (18.3). At $W=V_n(\varepsilon/4)$ the attained vector maximum has
$1-a_W(n)\le\varepsilon/4$, so the actual constructed protocol has
error at most $\varepsilon$; this gives the right side. No infimum is
replaced by an unattained threshold equality.

For (18.4), the vector threshold is exactly Theorem 12.2. The operational
threshold is the exact same-source history-separation and arbitrary-decoder
result [OWN, Theorems 9.2–9.3][OWN], already used in Convention 11.3;
it includes independent seeds and averaged error zero. At horizon zero
the empty branch needs only the identity decoder. These endpoint formulas
are separate from estimates dividing by $\sqrt\varepsilon$ or using
$-\log(1-\varepsilon)$. They show $W_n(0)=2V_n(0)$ for $n\ge1$,
while both widths at $n=0$ equal one. $\square$

## 19. Constant contraction and the remaining operational lower bound

**Theorem 19.1 (Conditional equivalence with explicit constants).** In the
fixed actual model the following two existence statements are equivalent:

1. There exist $C>0$ and $0<c_0<1$ such that, for every integer $W\ge1$,
   $a_W(\lceil CW^{2/3}\rceil)\le1-c_0$.
2. There exist one $\varepsilon_0\in(0,1/4)$, $c>0$ and an integer
   $n_0\ge1$ such that $W_n(\varepsilon_0)\ge c n^{3/2}$ for every
   integer $n\ge n_0$.

The first statement in fact implies such a lower bound at every fixed
$0<\varepsilon<1/4$. It is also equivalent to the existence of $C>0$
and $0<\eta<4$ such that for every $W$ the attained energy minimum at
$n=\lceil CW^{2/3}\rceil$ is at least $\eta$.
None of these existence statements is asserted without its premise.

Proof. Suppose statement 1 and put

$$
L_W=\lceil CW^{2/3}\rceil,\qquad
d=-\log(1-c_0)>0,\qquad b_\varepsilon=-\log(1-\varepsilon)>0.
$$

Submultiplicativity and contraction from Lemma 4.2 give

$$
a_W(n)\le(1-c_0)^{\lfloor n/L_W\rfloor}.
\tag{19.1}
$$

A successful width satisfies $1-\varepsilon\le a_W(n)$ by Theorem 4.3,
so $\lfloor n/L_W\rfloor\le b_\varepsilon/d$ and
$n<(1+b_\varepsilon/d)L_W$. Since $W\ge1$ implies
$L_W\le(C+1)W^{2/3}$, every successful width, for $n\ge1$, obeys

$$
W>\left(\frac{n}{(C+1)(1+b_\varepsilon/d)}\right)^{3/2}.
\tag{19.2}
$$

This supplies statement 2, with any chosen fixed error in its range,
$n_0=1$ and the corresponding displayed positive coefficient.

Conversely suppose statement 2. Choose $C$ so that

$$
C\ge\max\{1,n_0\},\qquad cC^{3/2}>2.
\tag{19.3}
$$

For any integer $W\ge1$ put $n=\lceil CW^{2/3}\rceil$. If
$a_W(n)\ge1-\varepsilon_0/4$, the attained construction in Theorem 18.2
gives an actual successful protocol of width at most $2W$. Then

$$
2W\ge W_n(\varepsilon_0)\ge cn^{3/2}
   \ge cC^{3/2}W>2W,
$$

a contradiction. Therefore
$a_W(\lceil CW^{2/3}\rceil)<1-\varepsilon_0/4$ for every $W$.
Statement 1 follows with $c_0=\varepsilon_0/4$. The factor two here
pays the retained parity bit in the actual operational construction.
The threshold error is attained, so the argument includes equality in
the hypothetical vector-survival premise.

Finally (16.1) identifies the attained minimum with $4(1-a_W(n)^2)$.
A deficit $c_0$ gives $\eta=4(1-(1-c_0)^2)\in(0,4)$; an energy
bound $\eta\in(0,4)$ gives deficit
$c_0=1-\sqrt{1-\eta/4}\in(0,1)$. This is an equivalence of conditions,
not a proof of a positive energy bound. $\square$

**Proposition 19.2 (Finite exceptions and a possible counterfamily).**
In statement 1 of Theorem 19.1 it is equivalent to require the estimate
only for $W\ge W_*$, for some finite integer $W_*$. Such exceptions can
be absorbed by increasing $C$. If there were legal fields with

$$
\frac{n_m}{W_m^{2/3}}\longrightarrow\infty,
\qquad \mathscr E(f_m,r_{0,m},y_m)\longrightarrow0,
\tag{19.4}
$$

then they would give full-qutrit recovery of error tending to zero and
width $2W_m=o(n_m^{3/2})$. Existence of a family (19.4) remains unresolved.

Proof. For each omitted width choose
$\ell_W=2+\lfloor\log_2 W\rfloor$, so Theorem 12.2 gives the attained
$q_W=a_W(\ell_W)<1$. Choose a positive integer $m_W$ with
$q_W^{m_W}\le1-c_0$; this is possible also when $q_W=0$.
Increase $C$ until $CW^{2/3}\ge m_W\ell_W$ for every omitted width.
There are finitely many. Submultiplicativity and monotonicity in horizon
then give the required contraction there. Increasing the horizon also
preserves contraction at all other widths. Thus finite width exceptions,
like the finite time exceptions in statement 2, do not change the
existence statement. For (19.4), Theorem 17.2 gives error at most
$3\mathscr E/4$ and
$2W_m/n_m^{3/2}=2(n_m/W_m^{2/3})^{-3/2}\to0$.
This is an implication conditional on the same-controller family;
it supplies no such family. $\square$

**Convention 19.3 (Distinct unresolved rates).** The equivalent condition
in Theorem 19.1 asks for a constant deficit after time proportional to
$W^{2/3}$. Its iterated consequence is (19.1), with that block scale.
The particular all-time envelope (16.2), with its logarithmic startup
allowance, is a stronger sufficient target and is not established by
this argument. The original gap in (9.2), sharper error dependence,
numerical constants and a genuine violating controller family remain
unresolved. Combining a conditional lower bound here with Theorem 8.4
would give $\Theta_\varepsilon(n^{3/2})$ at fixed error; no unconditional
improvement on Theorem 9.1 follows from the bridge alone.

## 20. The actual occupation graph and its exact time mode

**Definition 20.1 (Layered connection graph).** For a deterministic
controller and starting state as in Definition 17.1, with $n\ge1$, let

$$
\mathcal V_+=\{(k,r):0\le k\le n,\ p_k(r)>0\}.
$$

For every $0\le k<n$, each retained $(k,r)$, and each label $j$, keep
a separate undirected edge $e=(k,r,j)$ to
$(k+1,f_{k+1,j}(r))$, of weight $w_e=p_k(r)/2$. The endpoint is retained
by (14.2). Two labels with the same endpoints remain parallel edges.
The transport from the lower to the upper vertex is $F_j$; in the
reverse direction it is $F_j^\dagger$. For a complex field $z$ define

$$
Q_{\rm conn}(z)=\sum_{k=0}^{n-1}\sum_{r:p_k(r)>0}\sum_{j=0}^1
 \frac{p_k(r)}2
 \|z_{k+1,f_{k+1,j}(r)}-F_jz_{k,r}\|_2^2.
\tag{20.1}
$$

The scalar adjacency $A_0$ sums parallel edge weights, the degree matrix
is $D_0=\operatorname{diag}(d_v)$, and
$\mathcal L_0=I-D_0^{-1/2}A_0D_0^{-1/2}$ is the normalized scalar
Laplacian. Order its eigenvalues increasingly. The connection form keeps
each transport separately; complex fibers may equivalently be realified
to $\mathbb R^4$ with orthogonal, inverse-paired transports.

**Theorem 20.2 (Energy identity, degrees and time eigenfunction).** On this
actual graph, the restriction of the backward field satisfies

$$
Q_{\rm conn}(b)=\mathscr E(f,r_0,y)/4.
\tag{20.2}
$$

Its degrees and total volume are

$$
d_{k,r}=\begin{cases}p_k(r),&k=0\text{ or }k=n,\\
2p_k(r),&0<k<n,\end{cases}
\qquad \sum_{v\in\mathcal V_+}d_v=2n.
\tag{20.3}
$$

The graph is connected, and the scalar random-walk operator
$P=D_0^{-1}A_0$ has the nonconstant time eigenfunction
$g(k,r)=\cos(\pi k/n)$ with eigenvalue $\cos(\pi/n)$. Hence

$$
\lambda_2(\mathcal L_0)
\le1-\cos(\pi/n)\le\frac{\pi^2}{2n^2}\qquad(n\ge1).
\tag{20.4}
$$

Proof. At $(k,r)$ put
$u_j=F_j^\dagger b_{k+1}(f_{k+1,j}(r))$.
The actual backward equation is $b_k(r)=(u_0+u_1)/2$. By unitarity the
$j$ edge residual has norm $\|u_j-b_k(r)\|_2$, and these residuals are
$\pm(u_0-u_1)/2$. Their two weighted squares sum to
$p_k(r)\|u_0-u_1\|_2^2/4$. Summing proves (20.2), including every
zero-occupation term omitted from the graph.

A vertex has total outgoing weight $p_k(r)$ if $k<n$. Its total incoming
weight, if $k>0$, is $p_k(r)$ by the same occupation recursion (14.2),
regardless of whether the transitions are many-to-one. This proves the
degrees. Each layer has total occupation one, so the endpoint volumes are
one each, every interior layer has volume two, and the total is $2n$.
Every retained vertex is reached by a positive-weight history path from
$(0,r_0)$; their union is connected. There are no isolated retained
vertices or zero degrees.

For a function constant on each layer, the random walk sends the
interior value $g_k$ to $(g_{k-1}+g_{k+1})/2$. At time zero it sends it
to $g_1$, and at time $n$ to $g_{n-1}$. For $\theta=\pi/n$,

$$
\frac{\cos((k-1)\theta)+\cos((k+1)\theta)}2
 =\cos\theta\cos(k\theta),\quad
\cos\theta=\cos\theta\cos0,\quad
\cos((n-1)\theta)=\cos\theta\cos(n\theta).
\tag{20.5}
$$

Thus $Pg=\cos\theta\,g$, also at $n=1$, where the two layer values
are $1,-1$ and the eigenvalue is $-1$. Since $\cos(\pi/n)<1$ and
$g$ is nonconstant, the corresponding Laplacian eigenvalue is positive.
Similarity of $P$ with $D_0^{-1/2}A_0D_0^{-1/2}$ gives the first
inequality in (20.4). Equivalently $D_0^{1/2}g$ is an eigenvector of
$\mathcal L_0$, orthogonal to its constant mode $D_0^{1/2}\mathbf1$.
The elementary inequality $1-\cos x\le x^2/2$ gives the second bound.
No averaging of connection matrices is used. $\square$

**Proposition 20.3 (Boundary-field and scalar-gap limitations).** This
undirected occupation graph has no positive scalar spectral gap uniform
in horizon. The actual backward-field problem and unrestricted unit-sphere frustration
have different admissible fields and normalizations. In particular a direct
use of a scalar gap as a horizon-independent constant, or replacement of
unequal parallel transports by their average as a unitary signature, is
invalid for this graph.

Proof. The upper bound (20.4) tends to zero. The actual field satisfies
unit terminal values, $\|b_k(r)\|_2\le1$ internally, the directed
backward-averaging equation, and weights determined by its same forward
controller. In contrast, full unit-sphere frustration minimizes over
unit fields at every vertex. For a weighted connected graph with positive degrees and inverse-paired
orthogonal transports, [Bandeira–Singer–Spielman, Theorem 2.4][BSS] compares that minimum
$\eta_G$ with the lowest normalized connection eigenvalue by

$$
\lambda_1(\mathcal L_1)\le\eta_G
 \le44\frac{\lambda_1(\mathcal L_1)}{\lambda_2(\mathcal L_0)}.
\tag{20.6}
$$

Their normalization is the connection quadratic form divided by
$\sum_v d_v\|z_v\|_2^2$; for a unit field the denominator is the total
volume. Equation (20.2) concerns an unnormalized energy at a specified
boundary-constrained field, which is usually not a unit field internally.
Nor does its directed averaging impose the unrestricted undirected
Euler–Lagrange equation: variation of the latter includes incoming as well
as outgoing residuals. Thus neither a boundary coercivity estimate nor a
lower bound on $\mathscr E$ follows just by citing (20.6). Even a proved
application preserving its graph hypotheses would retain its
$1/\lambda_2(\mathcal L_0)$ factor, which cannot be bounded uniformly in
$n$ here by (20.4).

The cited theorem is stated with a single orthogonal signature for each
vertex pair. No extension to unequal parallel signatures is needed for
Theorem 20.2, and (20.6) is not being asserted for such a collapsed graph.
The actual example
$M=(F_0+F_1)/2$ has $M^\dagger M=\operatorname{diag}(0,1)$ by (12.1).
If two distinct labels share endpoints, replacing their separate
transports by $M$ therefore gives a nonunitary matrix. Scalar adjacency
may sum their weights; connection signatures must keep their separate
edge contributions. These facts limit this direct transfer. They do not
refute the contraction condition in Theorem 19.1 or preclude directed
boundary estimates, holonomy arguments, occupation-compatible reductions,
or other methods. $\square$

## 21. Attribution and mathematical boundaries of the bridge

**Convention 21.1 (Suppliers and scope of the deductions).** The
source-specific construction (17.3)–(17.8), the operational comparisons
(18.2)–(18.4), the conditional equivalence in §19, and the occupation/time
statements (20.2)–(20.4) are deductions in this manuscript's fixed model.
They reuse the same-determinant rigidity of §5, the quaternion algebra
and averaged cancellation of §8, the attained normal form and startup
threshold of §12, the finite-program channel representation of §13,
and the duality and occupation identity of §14. Those inputs are not
new standalone results of this supplement. The generic $SU(2)$
completion, CP norm identity, compactness and norm duality are standard
ingredients inside the proofs.

The primary mixture supplier is Matthew B. Hastings, *Turning Gate
Synthesis Errors into Incoherent Errors*, arXiv:1612.01011v1,
Lemma 1, equation (3) and proof [HASTINGS][HASTINGS]. For unitary target $U$, unitary $W_a$, probability $q(a)$, mean $\overline W$ and
$\delta=\sum_aq(a)\|W_a-\overline W\|_{\rm op}^2$, it bounds the
unhalved diamond error against $\operatorname{Ad}_U$ by
$\delta+2\|\overline W-U\|_{\rm op}$. Here its index is the whole actual
history and its variance is $1-\beta^2$, as established inside Theorem
17.2. Earl Campbell, *Shorter gate sequences for quantum computing by
mixing unitaries*, arXiv:1612.02689v3, §III, Lemma 1, equation (14)
[CAMPBELL][CAMPBELL], supplies the related bound $a^2+2b$ for a
probability mixture of unitaries $U_j$, a unitary target $V$, and
$a,b>0$, under the hypotheses $\|U_j-V\|_{\rm op}\le a$ for every index and
$\|\sum_jp_jU_j-V\|_{\rm op}\le b$. That paper's diamond distance is
half its diamond norm, by §I, equations (1)–(2). A uniform $a^2$ is not
replaced by an unproved averaged error; (17.9) or the Hastings variance
statement supplies the estimate actually used here.

The graph comparison (20.6) is Afonso S. Bandeira, Amit Singer and
Daniel A. Spielman, *A Cheeger Inequality for the Graph Connection
Laplacian*, arXiv:1204.3873v2, §2.2, Theorem 2.4, with the weighted
connected positive-degree graph, inverse-paired orthogonal signatures
and frustration definitions in
§1.3, equations (1.4)–(1.5) [BSS][BSS]. The scalar time-mode proof is
independent of that comparison and retains all parallel edges. The
permutation/scalar-test transfer boundaries of §15 are unchanged; no
additional coding or metric-spectral supplier is assumed to prove
contraction here.

These attributions identify the ingredients and their conditions, not
an exhaustive literature or priority classification. The mathematical
bridge addresses the actual two-letter, fixed-$\pi/6$, phase-faithful
qutrit with complete persistent classical-state accounting and untouched
references. It does not establish a physical implementation or a
Hamiltonian or QFT derivation. Exact static real controls, their
precision and calibration, deterministic schedules, acquisition and
communication costs remain separate under Definition 2.3. Uniform
constant contraction, (16.2), the logarithmic gap, sharper joint
$n,\varepsilon$ rates and an actual family (19.4) remain unresolved.

[HASTINGS]: https://arxiv.org/pdf/1612.01011v1
[CAMPBELL]: https://arxiv.org/pdf/1612.02689v3
[BSS]: https://arxiv.org/pdf/1204.3873v2

## 追加锚（本行以下为增补区）

## 22. Barycentric entropy amortization for the actual online flow

**Definition 22.1 (Fixed spectral constants and deficit).** Retain exactly
Definitions 2.1–2.4, including the fixed angle $\pi/6$, the embedded qutrit
in $H=\mathbb C^5$, full complex vector phase, complete persistent peak
width, free independent standard Borel seeds and deterministic schedule,
and fully averaged unhalved diamond error with every untouched reference.
Write $F=F_0$ from (12.1), $F_1=FJ$, and put

$$
\omega=(-1+i\sqrt3)/2,\qquad \mathcal A=\omega F,\qquad
C_1=J\mathcal A^{-1}J\mathcal A,\qquad
C_2=\mathcal A^{-1}C_1\mathcal A.
\tag{22.1}
$$

For normalized Haar measure on the full unit-vector sphere $S^3$, let
$\mathsf U_g v(x)=v(g^{-1}x)$ and set

$$
\mathsf S=\frac14\left(\mathsf U_{C_1}+\mathsf U_{C_1^{-1}}
                     +\mathsf U_{C_2}+\mathsf U_{C_2^{-1}}\right),\qquad
\gamma=\min\left\{1,
 \inf_{0\ne v\perp1}\frac{\langle v,(I-\mathsf S)v\rangle}
                              {\|v\|_2^2}\right\}.
\tag{22.2}
$$

The positivity $\gamma>0$ is proved in §24 from the spectral supplier
already used in §6; it is not a controller-dependent coercivity
assumption. This $\gamma$ is associated to $C_1,C_2$ and need not equal
the constant associated to $R_1,R_2$ in (6.2). Define

$$
\begin{aligned}
\kappa&=3\gamma/64,&
B_W(n)&=[\kappa\lfloor n/3\rfloor-\ln W]_+,\\
\Delta_W(n)&=\min\left\{\frac1{32},
                 \frac{B_W(n)}{32768W^{2/3}}\right\},&
C&=6+2^{17}/\gamma,\\
\alpha&=\sqrt{31/32},&c_*&=1-\alpha.
\end{aligned}
\tag{22.3}
$$

All logarithms in §§22–27 are natural unless a base is displayed.

**Theorem 22.2 (Unconditional finite-horizon deficit and sharp block
contraction).** For every integer $W\ge1$ and $n\ge0$,

$$
a_W(n)^2\le1-\Delta_W(n),\qquad
\mathcal Q_W(n)\ge4\Delta_W(n).
\tag{22.4}
$$

More specifically, every deterministic changing many-to-one controller,
starting state and unit terminal field of Definition 17.1, with its own
occupations and backward vectors, satisfies

$$
\mathscr E(f,r_0,y)\ge
\min\left\{\frac18,\frac{B_W(n)}{8192W^{2/3}}\right\}.
\tag{22.5}
$$

There are no positive-occupation or stationarity hypotheses. In particular,

$$
a_W(\lceil CW^{2/3}\rceil)\le\alpha=1-c_*,\qquad
 a_W(n)\le\alpha^{\lfloor n/\lceil CW^{2/3}\rceil\rfloor}.
\tag{22.6}
$$

Here $C$ and $c_*$ are absolute constants for the fixed instrument;
$0<\gamma\le1$, but no numerical lower bound on $\gamma$ is asserted.
The proof is given in §§23–26. It supplies the first condition of
Theorem 19.1 without an additional dynamic assumption. The exact
lossless startup of Theorem 12.2 is retained.

## 23. Actual conditional means and the entropy cost of their merging

**Definition 23.1 (The common-history conditional-mean flow).** Fix one
of the deterministic programs in (12.2), its starting state $r_0$ and a
unit $t\in\mathbb C^2$. On the actual independent fair acquired labels
$H_1,\ldots,H_n$ put

$$
\begin{aligned}
R_0&=r_0,& R_{k+1}&=f_{k+1,H_{k+1}}(R_k),\\
Z_0&=t,& Z_k&=F_{H_k}\cdots F_{H_1}t,\\
p_k(r)&=\Pr(R_k=r),&u_k(r)&=\mathbb E[Z_k\mid R_k=r],\\
S_k&=\sum_{r:p_k(r)>0}p_k(r)\|u_k(r)\|^2,& D_k&=1-S_k.
\end{aligned}
\tag{23.1}
$$

Conditional means are needed only where $p_k(r)>0$; a zero-occupation
state may be assigned zero for notation. These $p_k$ are exactly (14.2)
for this program, not a uniform law on its state set. All vectors retain
their complex phases relative to $\xi$. Realification to $\mathbb R^4$
uses the same Euclidean norm.

**Proposition 23.2 (Barycentric block payment on the actual law).** For
$k,\ell\ge0$ with $k+\ell\le n$, set

$$
Y=F_{H_{k+\ell}}\cdots F_{H_{k+1}}u_k(R_k),\qquad
Q=u_{k+\ell}(R_{k+\ell}).
$$

Then

$$
\mathbb E[Y\mid R_{k+\ell}]=Q,\qquad
\mathbb E\|Y-Q\|^2=S_k-S_{k+\ell}=D_{k+\ell}-D_k.
\tag{23.2}
$$

Consequently $D_0=0$, $0\le D_k\le D_{k+1}\le1$ and
$\|u_k(r)\|\le1$ on positive states. Let $G\sim N(0,I_4)$ be independent
of this whole finite experiment, fix $\sigma>0$, and let $f_k$ be the
Lebesgue density of $u_k(R_k)+\sigma G$. With
$\mathsf P=(\mathsf U_{F_0}+\mathsf U_{F_1})/2$ on $\mathbb R^4$,

$$
h(f_{k+\ell})\ge h(\mathsf P^\ell f_k)
              -\frac{D_{k+\ell}-D_k}{2\sigma^2}.
\tag{23.3}
$$

The Gaussian defines an auxiliary density only. It is not an operation,
noise source or persistent variable in the recovery procedure.

Proof. The future labels are independent of the entire earlier history.
The future state is a deterministic function of $R_k$ and those future
labels, even when each update is many-to-one. Thus, conditional on that
pair, replacing $Z_k$ by $u_k(R_k)$ preserves its expectation. For each
state $s$ this gives

$$
\mathbb E[Y\mathbf1_{\{R_{k+\ell}=s\}}]
=\mathbb E[Z_{k+\ell}\mathbf1_{\{R_{k+\ell}=s\}}].
$$

This proves the first identity in (23.2). Conditional-expectation
orthogonality and unitarity give
$\mathbb E\|Y-Q\|^2=\mathbb E\|Y\|^2-\mathbb E\|Q\|^2
=S_k-S_{k+\ell}$. Since $\|Z_k\|=1$, conditional convexity gives
$\|u_k(r)\|\le1$, and the remaining assertions follow.

Here is the finite-mixture entropy inequality needed for (23.3), with
its analytic details. Let $Y$ and $T$ be jointly finite-valued, in
$\mathbb R^d$ and a finite set respectively, put $Q=\mathbb E[Y\mid T]$,
and take an independent standard Gaussian $G$. For any $\sigma>0$,

$$
h(Y+\sigma G)-h(Q+\sigma G)
\le\frac{\mathbb E\|Y-Q\|^2}{2\sigma^2}.
\tag{23.4}
$$

Delete zero-probability atoms. For any of the resulting finite mixtures
with centers $a_i$ and positive weights $w_i$, its density is

$$
f(x)=\sum_iw_i(2\pi\sigma^2)^{-d/2}
                  e^{-\|x-a_i\|^2/(2\sigma^2)}.
$$

It is positive and smooth. A single positive component bounds $f$ below
by $e^{-K(1+\|x\|^2)}$ for some finite $K$; the Gaussian kernel's
maximum bounds it above by $(2\pi\sigma^2)^{-d/2}$. Thus
$|\log f(x)|\le K'(1+\|x\|^2)$ after enlarging the constant.
All these mixtures have finite moments of every order. Their entropies,
cross-entropies and pairwise KL divergences are therefore finite, also
when some centers coincide.

Let $f_Q$ be the density of $Q+\sigma G$ and $\varphi=\log f_Q$.
Differentiating the finite sum, with posterior weights proportional to
$w_i e^{-\|x-q_i\|^2/(2\sigma^2)}$, gives

$$
\nabla\varphi(x)=\frac{\mathbb E[Q\mid Q+\sigma G=x]-x}{\sigma^2},
\qquad
\nabla^2\varphi(x)=-\frac{I_d}{\sigma^2}
  +\frac{\operatorname{Cov}(Q\mid Q+\sigma G=x)}{\sigma^4}
\succeq-\frac{I_d}{\sigma^2}.
\tag{23.5}
$$

The gradient has at most linear growth. Taylor's formula integrated
along the line from $q+z$ to $y+z$ now yields

$$
\varphi(y+z)\ge\varphi(q+z)
 +\nabla\varphi(q+z)\cdot(y-q)-\frac{\|y-q\|^2}{2\sigma^2}.
$$

Use the same independent Gaussian in $q=Q$, $y=Y$, $z=\sigma G$.
The linear term is integrable and has expectation zero, because
$\mathbb E[Y-Q\mid T,G]=0$ and the gradient is measurable in $(T,G)$.
Consequently

$$
\mathbb E\varphi(Y+\sigma G)\ge
\mathbb E\varphi(Q+\sigma G)-\frac{\mathbb E\|Y-Q\|^2}{2\sigma^2}.
$$

For the density $f_Y$ of $Y+\sigma G$, the exact sign identity is

$$
\begin{aligned}
h(f_Y)-h(f_Q)+D_{\rm KL}(f_Y\|f_Q)
&=\int(f_Q-f_Y)\log f_Q\\
&=\mathbb E\varphi(Q+\sigma G)-\mathbb E\varphi(Y+\sigma G).
\end{aligned}
\tag{23.6}
$$

KL is nonnegative: $-\ln t\ge1-t$ integrated with
$t=f_Q/f_Y$ proves this directly. Dropping that nonnegative term proves
(23.4). The growth bounds above justify every expectation and subtraction.

Apply (23.4) to the actual $Y$ in (23.2), with $T=R_{k+\ell}$.
Conditional on $R_k$, the independent future labels rotate its center
by the actual length-$\ell$ word. Every $F_j$ is real orthogonal on
$\mathbb R^4$, so it preserves the isotropic Gaussian and Lebesgue
measure. The density of $Y+\sigma G$ is precisely
$\mathsf P^\ell f_k$. This proves (23.3). Neither the conditional means
nor their merging have been replaced by independently chosen centers.
$\square$

## 24. The actual finite-word comparison on radial and angular functions

**Proposition 24.1 (Phase-faithful three-step angular contraction).**
The constant $\gamma$ in (22.2) satisfies $0<\gamma\le1$. On
$L^2(\mathbb R^4,dx)$ let $\Pi$ be the orthogonal projection onto radial
functions. Then for every complex $v\in L^2(\mathbb R^4)$,

$$
\|v\|_2^2-\|\mathsf P^3v\|_2^2
\ge\frac\gamma{16}\|(I-\Pi)v\|_2^2.
\tag{24.1}
$$

Proof. The matrix identities connecting this use of the spectral
supplier to the actual letters are

$$
\begin{aligned}
\mathcal A&=\frac14\begin{pmatrix}
1+i\sqrt3&-\sqrt3+3i\\\sqrt3+3i&1-i\sqrt3
\end{pmatrix},& \det\mathcal A&=1,&\operatorname{tr}\mathcal A&=1/2,\\
C_1&=\frac14\begin{pmatrix}-2&\sqrt3+3i\\-\sqrt3+3i&-2\end{pmatrix},\\
C_2&=\frac1{16}\begin{pmatrix}
-8+6i\sqrt3&-5\sqrt3-3i\\5\sqrt3-3i&-8-6i\sqrt3
\end{pmatrix}.
\end{aligned}
\tag{24.2}
$$

They follow by multiplying (12.1) and (22.1); in particular
$\mathcal A^\dagger\mathcal A=I$, $C_i\in SU(2)$,
$\operatorname{tr}C_i=-1$ and $C_i^3=I$. One may check the last
mixed trace without expanding all entries: for determinant-one
$2\times2$ matrices, Cayley–Hamilton gives
$\operatorname{tr}(XY)+\operatorname{tr}(XY^{-1})
=\operatorname{tr}X\operatorname{tr}Y$. Here

$$
\operatorname{tr}(C_1\mathcal A^{-1})=1/2,\qquad
\operatorname{tr}(C_1\mathcal A)=-1,\qquad
\operatorname{tr}(C_1C_2)=-1/2-\operatorname{tr}(\mathcal A^{-2})=5/4.
\tag{24.3}
$$

There is also an exact identification with the existing dense pair of
Definition 6.1. The scalar relating $F$ and $A=g_0$ cancels in conjugation,
so $J_k=F^{-k}JF^k=A^{-k}JA^k$. Therefore

$$
C_1=J_0J_1=R_1,\qquad C_2=J_1J_2=R_1^{-1}R_2,\qquad
C_1C_2=R_2.
\tag{24.4}
$$

Thus $\langle C_1,C_2\rangle=\langle R_1,R_2\rangle$, whose density
is Theorem 6.2. Equivalently the same closed-subgroup argument applies
to (24.3): the trace $5/4$ makes $C_1C_2$ infinite order, since a finite
order matrix has algebraic-integer trace and a rational algebraic integer
is integral. A proper infinite closed subgroup of $SU(2)$ has a circle
as identity component and lies in its normalizer, as proved in §6.
Elements of that normalizer outside the circle have trace zero. The
nonzero traces of $C_1,C_2$ would put both in the circle; their commuting
order-three product would then have finite order, a contradiction.
This reuses the source's group argument, not a new density hypothesis.

Apply [BG, publisher final, Theorem 1 and footnote 1, p. 1455][BG],
DOI [10.4171/JEMS/337][BG-DOI], to $d=2$, $k=2$, $g_i=C_i$.
All entries in (24.2) belong to $\mathbb Q(i,\sqrt3)$ and hence are
algebraic. Both generators are in $SU(2)$, and their topological density
is equivalent to the theorem's Zariski density in $SL_2(\mathbb C)$
by that footnote. The paper uses the self-adjoint unnormalized Hecke sum
$zv(x)=\sum_{i=1}^2[v(C_ix)+v(C_i^{-1}x)]$ and proves its top spectral
supremum on constants-perpendicular is less than $4$. Its probability
normalization (0.1), p. 1457, is the symmetric measure with mass $1/4$
on each listed generator and inverse, with multiplicities. Under the
inverse-translation convention here this is precisely $\mathsf S=z/4$.
Only the resulting positive top gap is needed; no absolute gap for $z$
or gap for the nonsymmetric $\mathsf P$ is inferred directly.

The action on $S^3$ is the regular $SU(2)$ action, not a projective
quotient. Indeed the completion $C(z)$ in (17.4) is the unique $SU(2)$
matrix sending $(1,0)^{\mathsf T}$ to a prescribed unit complex vector
$z$. For any other fixed unit vector $t$, use $C(z)C(t)^\dagger$.
This identifies Haar with the uniform measure on the full sphere and
transfers the Hecke gap to (22.2). This proves $\gamma>0$.

In polar coordinates $x=r\theta$, with normalized sphere measure $m_3$,
$dx=2\pi^2r^3\,dr\,dm_3(\theta)$. For almost every $r>0$, the angular
section of $v$ is square-integrable; $\Pi v(r\theta)=\int v(r\eta)dm_3(\eta)$.
Apply the sphere gap to its zero-mean part and integrate in $r$.
Fubini and the boundedness of the rotation operators give

$$
\langle v,(I-\mathsf S)v\rangle
\ge\gamma\|(I-\Pi)v\|_2^2.
\tag{24.5}
$$

Finally, for a chronological word $w=abc$ write $g_w=F_cF_bF_a$.
The three actual words with one label $1$ satisfy

$$
g_{100}=F^3J_0,\qquad g_{010}=F^3J_1,\qquad g_{001}=F^3J_2.
$$

Their ordered differences are
$g_{100}^{-1}g_{010}=C_1$ and $g_{010}^{-1}g_{001}=C_2$;
reversing each pair gives its inverse. Each word has actual probability
$1/8$. Composition obeys $\mathsf U_g\mathsf U_h=\mathsf U_{gh}$,
so, with $\mathsf T=\mathsf P^3$,

$$
\mathsf T^*\mathsf T=\frac1{64}\sum_{u,w\in\{0,1\}^3}
                       \mathsf U_{g_u^{-1}g_w},\qquad
\|v\|_2^2-\|\mathsf T v\|_2^2
=\frac1{128}\sum_{u,w}\|v-\mathsf U_{g_u^{-1}g_w}v\|_2^2.
\tag{24.6}
$$

The second equality is the Hilbert variance identity for eight unitary
images. Keep the four specified ordered pairs, discarding nonnegative
terms. The symmetric Dirichlet form is

$$
\langle v,(I-\mathsf S)v\rangle
=\frac18\sum_{c\in(C_1,C_1^{-1},C_2,C_2^{-1})}
                         \|v-\mathsf U_cv\|_2^2.
$$

Hence (24.6) is at least $\langle v,(I-\mathsf S)v\rangle/16$;
(24.5) proves (24.1). This is the same actual forward-word comparison
mechanism as §6, with the neighboring pair $C_1,C_2$ and radial
disintegration made explicit. It adds no inverse move, extra label or
controllable quantum operation to the physical two-letter process.
$\square$

## 25. Peak width forces entropy production while the deficit is small

**Proposition 25.1 (Angular concentration and actual entropy production).**
For the flow in Definition 23.1, choose

$$
\sigma=\frac1{256W^{1/3}}.
\tag{25.1}
$$

If $D_k\le1/32$, then

$$
\|\Pi\sqrt{f_k}\|_2^2\le1/4,\qquad
h(\mathsf P^3f_k)-h(f_k)\ge\kappa.
\tag{25.2}
$$

Proof. Write $U=u_k(R_k)$. Since $\|U\|\le1$, Markov's inequality
applied to $1-\|U\|^2$ gives

$$
\Pr(\|U\|<1/2)\le\frac{D_k}{3/4}\le1/24.
$$

For the independent standard Gaussian in four real dimensions,
$\mathbb E\|G\|^2=4$, so $\Pr(\|G\|>16)\le1/64$.
Around every direction $u_k(r)/\|u_k(r)\|$ with $\|u_k(r)\|\ge1/2$
and positive occupation, take the sphere chord ball of radius

$$
\varrho=64\sigma=\frac1{4W^{1/3}}\le1/4.
$$

Their union $A_{\rm ang}$ has at most $W$ caps. The phase-resolved
sphere-volume formula used in (7.2) gives, for a cap of chord radius
$\varrho\le1$, geodesic radius $\theta=2\arcsin(\varrho/2)\le2\varrho$
and normalized area

$$
\frac2\pi\int_0^\theta\sin^2s\,ds
\le\frac{2\theta^3}{3\pi}\le4\varrho^3.
$$

Thus $a=m_3(A_{\rm ang})\le4W\varrho^3=1/16$. Let
$A_{\rm cone}=\{r\theta:r>0,\theta\in A_{\rm ang}\}$.
For nonzero $u$ and $u+e$, the triangle inequality and the reverse
triangle inequality imply

$$
\left\|\frac{u+e}{\|u+e\|}-\frac u{\|u\|}\right\|
\le\frac{2\|e\|}{\|u\|}.
$$

On $\|U\|\ge1/2$ and $\|G\|\le16$, the perturbed vector is nonzero:
$\sigma\|G\|\le16/256=1/16<1/2$. Its direction is within $\varrho$
of the corresponding center. Therefore the actual Gaussian mixture has

$$
\int_{A_{\rm cone}^c}f_k\le1/24+1/64=11/192<1/16.
\tag{25.3}
$$

For any complex radial $v$ of $L^2(dx)$ norm one, polar integration
gives $\int_{A_{\rm cone}}|v|^2=a$. Apply Cauchy–Schwarz on the cone
and its complement separately:

$$
|\langle v,\sqrt{f_k}\rangle|
\le\sqrt a\,\|\mathbf1_{A_{\rm cone}}\sqrt{f_k}\|_2
   +\sqrt{1-a}\,\|\mathbf1_{A_{\rm cone}^c}\sqrt{f_k}\|_2
\le\frac14+\sqrt{11/192}<\frac12.
$$

Taking the supremum over radial unit $v$ proves the first part of (25.2).
No angular probability of the actual history was replaced by Haar:
Haar enters only the cone's angular volume and radial projection.

For completeness the entropy-production estimate follows from elementary
KL and Hilbert inequalities. For a positive finite Gaussian mixture $f$,
rotations preserve differential entropy. The eight-word mixture
$\mathsf T f=\mathsf P^3f$ therefore satisfies

$$
h(\mathsf T f)-h(f)
=\frac18\sum_wD_{\rm KL}(\mathsf U_{g_w}f\|\mathsf T f).
\tag{25.4}
$$

All terms are finite by the growth bounds in §23. For positive
probability densities $p,q$, $-\ln t\ge2(1-\sqrt t)$, obtained from
$\ln s\le s-1$, gives

$$
D_{\rm KL}(p\|q)\ge2-2\int\sqrt{pq}
=\|\sqrt p-\sqrt q\|_2^2.
$$

Since $\sqrt{\mathsf U_gf}=\mathsf U_g\sqrt f$ and
$\|\sqrt{\mathsf T f}\|_2=1$, (25.4) is at least

$$
\begin{aligned}
2-2\langle\mathsf T\sqrt f,\sqrt{\mathsf T f}\rangle
&\ge2(1-\|\mathsf T\sqrt f\|_2)\\
&\ge1-\|\mathsf T\sqrt f\|_2^2\\
&\ge\frac\gamma{16}(1-\|\Pi\sqrt f\|_2^2).
\end{aligned}
\tag{25.5}
$$

Here $\mathsf T$ is an average of unitary operators and hence a
contraction; for $0\le b\le1$, $2(1-b)\ge1-b^2$. The last inequality
is (24.1) with $v=\sqrt f$. Apply the first part of (25.2) to obtain
$3\gamma/64=\kappa$. The dimension three in $W^{-1/3}$ is the angular
dimension of full complex unit vectors, while the auxiliary Gaussian
lives in four real dimensions. $\square$

## 26. One entropy budget and the all-controller deficit

Proof of Theorem 22.2. First fix the deterministic single-source program
and unit vector in Definition 23.1. The finite-mixture entropy budget at
each layer is

$$
0\le h(f_k)-h(\sigma G)
=I(R_k;u_k(R_k)+\sigma G)\le H(R_k)\le\ln W.
\tag{26.1}
$$

Here $H$ is discrete entropy in nats. To justify all signs and the upper
bound directly, put $p_r=p_k(r)>0$ and let $\phi_r$ be the Gaussian
component at center $u_k(r)$, so $f_k=\sum_rp_r\phi_r$.
Then the entropy difference equals
$\sum_rp_r\int\phi_r\ln(\phi_r/f_k)$ by expansion, since each component
has entropy $h(\sigma G)$. Each integral is KL and is nonnegative.
Also $f_k\ge p_r\phi_r$, so it is at most $-\ln p_r$.
Finally $\sum_r-p_r\ln p_r\le\ln W$, by KL nonnegativity against the
uniform law on $W$ padded states. These arguments allow coincident
centers and arbitrary nonuniform occupations. At initialization there
is one center $t$, so $h(f_0)=h(\sigma G)$ and $D_0=0$.

Suppose first that $D_n\le1/32$. Monotonicity in (23.2) makes
Proposition 25.1 applicable at all earlier times. With
$q=\lfloor n/3\rfloor$, apply (23.3) and (25.2) at
$k=0,3,\ldots,3q-3$. Summing gives

$$
h(f_{3q})-h(f_0)\ge q\kappa-\frac{D_{3q}}{2\sigma^2}.
$$

Combining (26.1) and $D_{3q}\le D_n$ yields the useful finite-horizon
budget inequality

$$
\kappa\lfloor n/3\rfloor\le\ln W+\frac{D_n}{2\sigma^2}
\quad\text{whenever }D_n\le1/32.
\tag{26.2}
$$

Since $2\sigma^2=(32768W^{2/3})^{-1}$, this gives
$D_n\ge B_W(n)/(32768W^{2/3})$ in this case. If instead
$D_n>1/32$, use that deficit directly. In all cases,

$$
D_n\ge\Delta_W(n).
\tag{26.3}
$$

This is the model-specific entropy amortization: the at-most-$\ln W$
entropy increase is paid once, while barycentric merging charges every
subsequent three-step entropy production to the same cumulative
squared loss. There is no independent coercivity premise.

For the corresponding forward tuple, $x_{n,r}=p_n(r)u_n(r)$, so
Cauchy–Schwarz in the actual probability law gives

$$
\left(\sum_r\|x_{n,r}\|\right)^2
=\left(\mathbb E\|u_n(R_n)\|\right)^2
\le S_n=1-D_n\le1-\Delta_W(n).
\tag{26.4}
$$

The attained deterministic single-source maximum in Theorem 12.2 is
exactly $a_W(n)$, including its supremum over arbitrary normalized
initial tuples and all stochastic layers. Taking that maximum in
(26.4) proves the first part of (22.4).

For the pointwise energy bound, keep the original $f,r_0,y$ of
Definition 17.1, put $\beta=\|b_0(r_0)\|$, and use its own $p_k$.
If $\beta>0$, choose $t=b_0(r_0)/\beta$ in the preceding argument.
The same-history backward identity (17.3) and the inner-product
convention of Definition 14.1 imply

$$
\beta=\mathbb E\operatorname{Re}\langle y_{R_n},F_{H_n}\cdots F_{H_1}t\rangle
=\mathbb E\operatorname{Re}\langle y_{R_n},u_n(R_n)\rangle
\le\mathbb E\|u_n(R_n)\|.
$$

Thus $\beta^2\le S_n$. Reuse the exact occupation-weighted identity
(14.4), $\mathscr E=4(1-\beta^2)$, to obtain
$\mathscr E\ge4D_n\ge4\Delta_W(n)$, which is (22.5).
If $\beta=0$, the energy is four and the assertion is immediate.
Zero-occupation states never require division or a chosen conditional
mean. Taking the attained energy minimum (14.5) gives the second
part of (22.4), consistently with $\mathcal Q_W=4(1-a_W^2)$.
This does not replace a controller's occupations by those of an optimizer
for a different quantity.

To check the constants for every width, write $x=W^{2/3}\ge1$ and
$n=\lceil Cx\rceil$. Since $\lfloor n/3\rfloor\ge Cx/3-1$,

$$
\kappa\lfloor n/3\rfloor
\ge(2\kappa+2048)x-\kappa
\ge(\kappa+2048)x.
$$

Also $\ln W=(3/2)\ln x\le(3/2)x$. Hence
$B_W(n)\ge(\kappa+2048-3/2)x>1024x$, so
$\Delta_W(n)=1/32$. This proves the first inequality of (22.6).
Submultiplicativity from Lemma 4.2, with a contractive remainder,
proves its second inequality. No width is omitted and no finite
exception is absorbed without an estimate.

The randomization scope can be stated explicitly. For a fixed seed,
a stochastic table is the convex combination of deterministic maps
with weights $\prod_rT(f(r)\mid r)$. Expanding both label tables at
each time expresses the product of layers as a convex combination of
complete deterministic programs, with weights independent of acquired
labels. Decomposing an arbitrary tuple as $\sum_re_rx_r$ then reduces
the vector norm maximum to unit single-source inputs, precisely as in
Theorem 12.2. Thus the bound just proved is uniform over stochastic
layers and initial laws. For a measurable independent standard Borel
seed, pad to width $W$ on the common full-measure set for the finitely
many times and apply that same uniform bound at each seed. Bounded
measurable vector norms can be integrated. Neither a successful seed
nor conditional success is assumed. For a fixed stochastic controller's
backward fields its exact variance identity remains (14.7); the sharp
bound on the optimum needs no determinization of decoder error.

At $n=0$, $B_W(0)=0$, $D_0=0$, $a_W(0)=1$ and every unit-terminal
single-source energy is zero. At $W=1$, Proposition 12.3 gives exactly
$a_1(n)=2^{1-n}$ for $n\ge1$, including $a_1(1)=1$.
Throughout the lossless startup $W\ge2^{n-1}$, $n\ge1$, the new
positive part is zero: for $n=1$ its floor is zero, while for $n\ge2$,

$$
\kappa\lfloor n/3\rfloor\le n/64
\le(n-1)\ln2\le\ln W.
$$

Thus (22.4) preserves the exact startup and the width-two path of
Proposition 12.4. It asserts no strict loss at every step.
$\square$

## 27. The original sharp fixed-error operational rate

**Corollary 27.1 (All permitted controllers and full-space decoders).**
For every fixed original $0<\varepsilon<1/4$, put

$$
q_\varepsilon=\left\lfloor
 \frac{\ln(1-\varepsilon)}{\ln\alpha}\right\rfloor+1.
\tag{27.1}
$$

For all integers $n\ge2q_\varepsilon$,

$$
\left(\frac{n}{2q_\varepsilon C}\right)^{3/2}
\le W_n(\varepsilon)
\le\min\left\{2^n,28\pi^2
                 \left\lceil4\sqrt{n/\varepsilon}\right\rceil^3\right\}.
\tag{27.2}
$$

In particular $W_n(\varepsilon)=\Theta_\varepsilon(n^{3/2})$ and
$\lceil\log_2W_n(\varepsilon)\rceil=(3/2)\log_2n+O_\varepsilon(1)$.
At $n=0$ the width is one. The constants are for this fixed instrument,
with its proved positive spectral gap.

Proof. The integer $q_\varepsilon\ge1$ satisfies
$\alpha^{q_\varepsilon}<1-\varepsilon$, including when the ratio in
(27.1) is integral. Let $N_W=\lceil CW^{2/3}\rceil$.
A successful width $W$ must satisfy $1-\varepsilon\le a_W(n)$ by
Theorem 4.3. If $n\ge q_\varepsilon N_W$, (22.6) contradicts this.
Consequently

$$
n<q_\varepsilon\lceil CW^{2/3}\rceil
\le q_\varepsilon(CW^{2/3}+1).
$$

For $n\ge2q_\varepsilon$ this implies
$CW^{2/3}>n/q_\varepsilon-1\ge n/(2q_\varepsilon)$,
proving the lower bound in (27.2).

The converse used here keeps arbitrary terminal CPTP decoders on $M_5$:
Theorem 3.2 retracts each to $M_3$ without increasing encoded error.
For any unit $t\in T$, the norm-one complex coherence
$Z_t=|t\rangle\langle\xi|$ has actual branch image
$|F_ht\rangle\langle\xi|$. At almost every fixed seed, the decoded
output norm is at most the terminal sum of vector norms, hence at most
$a_W(n)$. A CPTP map contracts trace norm on this non-Hermitian operator
by its unital CP adjoint, Schwarz inequality and trace/operator duality,
as in Theorem 4.3. Integrating the uniform upper bound gives
$\|\mathcal C_n(Z_t)\|_1\le a_W(n)$; the averaged diamond criterion
gives $\|\mathcal C_n(Z_t)\|_1\ge1-\varepsilon$. No seed or history is
selected for success. The norm is unhalved and the reduction preserves
all untouched references. Full-$H$ decoding is allowed, while the
recovery inputs remain the embedded qutrit.

The upper bound is exactly Theorem 8.4, using its stochastic radial
lattice shell with a counted determinant bit. With
$m=\lceil4\sqrt{n/\varepsilon}\rceil\ge8$, its at-most-$28\pi^2m^3$
states carry all persistent information. The source's zero-mean lattice
rounding and radial normalization have mean bias at most $4/m^2$ and
second moment at most $4/m^2$. Their local averaged diamond error is
at most $12/m^2$ by Lemma 8.3. The actual weighted subchannels in (8.6)
sum to a channel, giving accumulated error at most
$12n/m^2\le3\varepsilon/4$. Only the terminal full-$H$ correction
(3.1) is executed. This is the existing source construction with its
relative phase and determinant coset preserved. Retaining all histories
supplies the alternative $2^n$ upper bound.

Finally $\lceil4\sqrt{n/\varepsilon}\rceil\le5\sqrt{n/\varepsilon}$
for $n\ge1$ gives a constant times $n^{3/2}$ upper bound. Together
with (27.2) it proves both asymptotic statements. $\square$

**Convention 27.2 (Source-relative attribution and precise boundary).**
The model-specific deduction in §§23, 25–26 is barycentric entropy
amortization of the actual conditional-mean flow, yielding (22.4)–(22.6)
and the unconditional sharp rate (27.2). Finite Gaussian-mixture
semiconvexity, KL nonnegativity, Hellinger comparison, conditional
expectation and entropy of a mixture are generic analytic ingredients;
their needed arguments are included inside these deductions. The group
density and actual forward-word comparison reuse §§6–7, with (24.4)
giving the exact correspondence. Their external deep input is solely
Bourgain–Gamburd's publisher-final Theorem 1, footnote 1 and normalization
(0.1), at the locators specified in §24. No assertion of exhaustive
literature novelty is attached to this synthesis.

The energy identity, arbitrary-tuple and stochastic reductions, and
operational converse are the existing results of §§4, 12–14 and 18.
The paid-parity construction of Theorems 17.2 and 18.2 remains a
width-$2W$ construction; its exact determinant
$\det F_h=\omega^n(-1)^{\sum h_k}$ is retained in the decoder table.
It is not necessary for the lower-bound direction of Corollary 27.1,
and no same-width operational sufficiency is inferred from vector
survival. In particular the width-one, horizon-one obstruction of
Proposition 17.3 still applies. The rounding upper bound is §8's result.
These reused inputs are not additional new standalone results here.

Theorem 22.2 establishes the constant-contraction condition of §19 and
Corollary 27.1 removes the fixed-error logarithmic gap in (9.2).
Neither proof assumes (16.2); the particular all-time exponential
formula with logarithmic startup in (16.2) is not asserted here.
A family (19.4) is excluded by (22.5): if its energies tend to zero,
then eventually $\mathscr E<1/8$, so
$\kappa\lfloor n/3\rfloor\le\ln W+8192\mathscr E W^{2/3}$.
After division by $W^{2/3}$ the right side stays bounded since
$(\ln W)/W^{2/3}\le3/(2e)$, contradicting
$n/W^{2/3}\to\infty$.

Peak width enters at every layer in Proposition 25.1 through its at most
$W$ actual centers. A terminal-only alphabet or a bound on the entropy
of the final record cannot supply that premise at earlier layers.
The terminal-entropy task permits unlimited intermediate memory and
actual erasure; the autonomous STOP task has a homogeneous internally
clocked controller and different seed and exact-error permissions.
Neither supplies a premise for this peak-width theorem. Smoothing is
solely an analytic potential and never replaces the singular finite-word
law by Haar or adds Gaussian physical noise.

Numerical values for the spectral gap and optimal constants, sharp
joint $n,\varepsilon$ asymptotics, static-table and inverse-control
precision, calibration, acquisition and communication costs remain
outside (27.2). The result concerns the specified mathematical model;
it gives no physical or QFT realization or Lean/kernel certification.
The original fixed-zero-error and $n=0$ endpoints retain their separate
statements in §§11 and 18.

## 追加锚（本行以下为增补区）

## 28. Joint horizon and accuracy below the deficit cap

**Convention 28.1 (Unchanged operational problem).** Retain Definitions
2.1–2.4: the actual fixed-$\pi/6$ measured instrument, the full complex
qutrit embedded in $H=\mathbb C^5$, and fully averaged unhalved diamond
error on every untouched finite reference. The minimum $W_n(\varepsilon)$
is over complete persistent peak width at every layer, allowing changing
many-to-one and stochastic updates, independent finite or standard Borel
free shared seeds, and arbitrary terminal full-$H$ CPTP decoders. Only one
terminal quantum correction is allowed. A prefix archive, persistent random
tape or history-dependent control information is counted memory; there is
no postselection, retained environment, reference access or intermediate
quantum control. The deterministic clock, nonuniform exact static tables
and inverse-control precision have exactly the separate-resource permissions
of Definition 2.3.

Use the fixed spectral constants of Definition 22.1, in particular
$\kappa=3\gamma/64$, $C=6+2^{17}/\gamma$,
$\alpha=\sqrt{31/32}$ and $c_*=1-\alpha$. The proved positivity of
$\gamma$ is sufficient below; no numerical lower bound for it is supplied.
All logarithms in §§28–32 are natural unless their base is displayed.
Define the error deficit

$$
d(\varepsilon)=1-(1-\varepsilon)^2=2\varepsilon-\varepsilon^2.
\tag{28.1}
$$

**Proposition 28.2 (Necessary budget at strictly subcap error).** For
all integers $n\ge0$ and $W\ge1$, every successful width-$W$ controller
with $0<\varepsilon<c_*$ satisfies

$$
\kappa\lfloor n/3\rfloor
\le\ln W+32768(2\varepsilon-\varepsilon^2)W^{2/3}.
\tag{28.2}
$$

Proof. Theorem 4.3 gives $1-\varepsilon\le a_W(n)$. Both sides are
nonnegative, so squaring and then applying Theorem 22.2 gives

$$
\min\left\{\frac1{32},
 \frac{[\kappa\lfloor n/3\rfloor-\ln W]_+}{32768W^{2/3}}\right\}
=\Delta_W(n)\le d(\varepsilon).
\tag{28.3}
$$

On $(0,1)$, $d$ is strictly increasing and $d(c_*)=1/32$.
Thus $d(\varepsilon)<1/32$, and the second entry in the minimum in
(28.3) must be at most $d(\varepsilon)$. Its denominator is positive.
If $\kappa\lfloor n/3\rfloor-\ln W\le0$, (28.2) already holds.
If that difference is positive, its positive part is the difference
itself, and multiplication by $32768W^{2/3}$ proves (28.2).
This is a direct algebraic application of Theorems 4.3 and 22.2,
including their full-decoder, stochastic and independent-seed scope.
$\square$

The strict threshold is essential to this deduction. At
$\varepsilon=c_*$, the inequality
$\min\{1/32,1/8\}\le d(c_*)$ holds although $1/8>d(c_*)$.
At larger errors the cap is also below $d(\varepsilon)$, so (28.3)
does not give an uncapped budget. This does not assert that (28.2)
is false above the threshold. The block contraction (22.6) remains
available there. The positive part and the term $\ln W$ also remain
essential: (28.2) is a necessary condition with startup, not a
fixed-$n$ lower bound diverging as $\varepsilon\downarrow0$.

## 29. A uniform matched regime including subexponential accuracy

**Theorem 29.1 (Joint bound with instrument-only constants).** Put

$$
\begin{aligned}
A&=3500\pi^2,&
K&=6\left(1+\frac{\ln A}{\kappa}\right),&K_0&=\max\{K,38\},\\
c_{\rm small}&=\left(\frac{\kappa}{393216}\right)^{3/2},&
c&=\min\left\{c_{\rm small},
                 \left(\frac{c_*}{38C}\right)^{3/2}\right\}>0.
\end{aligned}
\tag{29.1}
$$

For every real $0<\varepsilon<1/4$ and every integer $n\ge1$
satisfying

$$
n\ge K_0\bigl(\ln n+\ln(1/\varepsilon)+1\bigr),
\tag{29.2}
$$

one has

$$
c(n/\varepsilon)^{3/2}
\le W_n(\varepsilon)\le A(n/\varepsilon)^{3/2}.
\tag{29.3}
$$

The constants $c,A,K_0$ do not depend on $n$ or $\varepsilon$.
Their dependence on the fixed instrument includes its positive, not
numerically estimated, spectral gap.

Proof. Write $S=\ln n+\ln(1/\varepsilon)+1$ and
$W=W_n(\varepsilon)$. The integer minimum is attained as in
Definition 2.4. Since $x=\sqrt{n/\varepsilon}\ge1$,
$\lceil4x\rceil\le5x$. Theorem 8.4 therefore gives

$$
W\le28\pi^2(5\sqrt{n/\varepsilon})^3
=A(n/\varepsilon)^{3/2},\qquad
\ln W\le\ln A+\tfrac32(S-1)\le(\ln A)S.
\tag{29.4}
$$

The last inequality uses $S\ge1$ and $\ln A>3/2$.
First let $0<\varepsilon<c_*$. Proposition 28.2 and
$\lfloor n/3\rfloor\ge n/3-1$ imply

$$
\begin{aligned}
32768d(\varepsilon)W^{2/3}
&\ge\kappa n/3-\kappa-\ln W\\
&\ge\kappa n/3-(\kappa+\ln A)S\\
&\ge\kappa n/6.
\end{aligned}
\tag{29.5}
$$

Indeed $n\ge KS=6(\kappa+\ln A)S/\kappa$ proves the final step.
Since $d(\varepsilon)\le2\varepsilon$, (29.5) yields

$$
W\ge\left(\frac{\kappa n}{393216\varepsilon}\right)^{3/2}
=c_{\rm small}(n/\varepsilon)^{3/2}.
\tag{29.6}
$$

Now let $c_*\le\varepsilon<1/4$. The exact integer inequality
$16\cdot31^{19}<9\cdot32^{19}$ gives
$\alpha^{19}<3/4<1-\varepsilon$. If
$n\ge19\lceil CW^{2/3}\rceil$, (22.6) and Theorem 4.3 would give
$1-\varepsilon\le a_W(n)\le\alpha^{19}$, a contradiction.
Consequently, using $n\ge38$ from (29.2),

$$
\begin{aligned}
n&<19\lceil CW^{2/3}\rceil\le19(CW^{2/3}+1),\\
W&>\left(\frac{n}{38C}\right)^{3/2}
\ge\left(\frac{c_*}{38C}\right)^{3/2}(n/\varepsilon)^{3/2}.
\end{aligned}
\tag{29.7}
$$

This argument includes $\varepsilon=c_*$ without uncapping (28.3).
The two ranges and (29.4) prove (29.3). The proof reuses the source
rounding upper bound and block converse; the result is their quantitative
joint consequence with explicit uniformity. $\square$

**Corollary 29.2 (Every positive subexponential-error sequence).** For
every sequence $(\varepsilon_n)_{n\ge1}$ with
$0<\varepsilon_n<1/4$ and $\ln(1/\varepsilon_n)=o(n)$, there is
an integer $N$ such that for every $n\ge N$,

$$
c(n/\varepsilon_n)^{3/2}
\le W_n(\varepsilon_n)\le A(n/\varepsilon_n)^{3/2}.
\tag{29.8}
$$

Here $c,A,K_0$ are the same constants in (29.1); only $N$ may depend
on the sequence. This includes shrinking errors with subexponential
inverse accuracy, without restricting them to polynomial shrinkage.

Proof. The assumptions and $\ln n=o(n)$ give
$K_0(\ln n+\ln(1/\varepsilon_n)+1)/n\to0$. Thus (29.2) holds
for every sufficiently large $n$, and Theorem 29.1 applies at each
such $n$. No common $N$ over all these sequences is asserted.
$\square$

## 30. Exact prefixes followed by a single change to rounded memory

**Definition 30.1 (Delayed controller and its counted state).** Fix
$n\ge1$, $0<\varepsilon<1/4$ and an integer $0\le k<n$. Put

$$
L=n-k,\qquad m=\left\lceil4\sqrt{L/\varepsilon}\right\rceil\ge8,
\qquad N_m=2|\mathcal N_{1/m}|\le28\pi^2m^3.
\tag{30.1}
$$

For $0\le t\le k$, the entire persistent state is the exact binary
prefix $p=(h_1,\ldots,h_t)$, updated by deterministic appending. This
uses $2^t$ states at layer $t$. For a length-$k$ prefix write
$G_p=g_{p_k}\cdots g_{p_1}$, with $G_{\varnothing}=I_2$.
On acquiring label $j$ at step $k+1$, use one stochastic transition
from $(p,j)$ directly to the shell state $(d',q')$, where

$$
\begin{aligned}
Z&=g_jG_p,&
d'&=\left(\sum_{i=1}^k(1-p_i)+(1-j)\right)\bmod2,\\
z&=\Phi^{-1}(J^{d'}Z)\in S^3,&
a&=z+e,\qquad q'=a/\|a\|.
\end{aligned}
\tag{30.2}
$$

Coordinate rounding for $e$ is exactly Definition 8.1 with mesh $1/m$.
The determinant identity $\det Z=(-1)^{d'}$ makes $J^{d'}Z\in SU(2)$,
so the target is defined even when $G_p$ is not a shell point. Subsequent
steps use (8.1) on the shell state and the same mesh. Every rounding draw
is fresh conditional on the current state and next label, and is then
discarded. The determinant bit is updated exactly; the full signed
quaternion is stored, with $q$ and $-q$ distinct.

At the change of state set, there are $2^k$ persistent input states and
$2^{k+1}$ possible input-label pairs. The latter index rows of a static
transition kernel, each with at most $16$ nonzero rounded outputs. They
are not an additional persistent layer. Immediately after this transition,
the persistent state is only $(d',q')$: the prefix and its product are
not retained alongside it. Later layers have at most $N_m$ states.
Padding the time-dependent state sets to one common alphabet and using
the permitted deterministic schedule gives complete peak width at most

$$
\max\{2^k,N_m\}\le\max\{2^k,28\pi^2m^3\}.
\tag{30.3}
$$

In particular the exact prefix's $k$ bits are counted at every preceding
layer. The change in classical memory does not apply any quantum
operation.

**Theorem 30.2 (All-reference error of the delayed controller).** The
controller in Definition 30.1, with the terminal unitary specified below,
achieves

$$
\|\mathcal E_n-\iota\|_\diamond
\le12L/m^2\le3\varepsilon/4
\tag{30.4}
$$

with peak width (30.3). Its only quantum correction is at time $n$.
At $k=n$, instead retain the full history and recover exactly with
width $2^n$. At $n=0$ use width one, with error zero.

Proof. For analysis, let $G_t=g_{h_t}\cdots g_{h_1}$ be the actual
restricted product. Up to time $k$, assign to the counted prefix the
matrix $Y_t=G_t$. After time $k$, let $Y_t=J^{d_t}\Phi(q_t)$ be the
matrix represented by the counted shell state. Define

$$
E_t=1\oplus Y_t^\dagger G_t,\qquad
\mathcal M_t(r)=\mathbb E[
 \mathbf1_{\{R_t=r\}}\operatorname{Ad}_{E_t}],\qquad
\mathcal C_t=\sum_r\mathcal M_t(r).
\tag{30.5}
$$

Here $G_t$ and $E_t$ are analytic variables, not additional stored
registers. At time $k$, $E_k=I_3$ on every prefix and the actual fair
history law gives the exact initialization

$$
\mathcal M_k(p)=2^{-k}\operatorname{id}_3,
\qquad\mathcal C_k=\operatorname{id}_3.
\tag{30.6}
$$

For each $k\le t<n$, current counted state $r$ with represented
matrix $Y$, and next actual label $j$, put

$$
\mathcal L_{t,r,j}
=\mathbb E_{\rm fresh}\operatorname{Ad}_{1\oplus Y'^\dagger g_jY}.
\tag{30.7}
$$

At $t=k$, $Y=G_p$, and (30.2) rounds the arbitrary target $g_jG_p$
in its determinant coset. Thus the arbitrary-target clause of Lemma 8.3
applies at this first step; no shell membership of $G_p$ is required.
At $t>k$, (30.7) is the ordinary shell update. Uniformly in both cases,

$$
\|\mathcal L_{t,r,j}-\operatorname{id}_3\|_\diamond\le12/m^2.
\tag{30.8}
$$

This local estimate controls every finite reference and all complex
operators: the proof of Lemma 8.3 expands with
$B_{\rm err}=Y'^\dagger g_jY-I_2$, extended by zero on $\xi$, and
bounds left/right multiplication by $\|\mathbb EB_{\rm err}\|\le4/m^2$
and the quadratic term by $\mathbb E\|B_{\rm err}\|^2\le4/m^2$.
Tensoring these multipliers with an arbitrary reference identity changes
neither operator-norm bound. The local bound is averaged over fresh
rounding, not asserted on each rounded outcome.

Each $E_t$ is unitary. Actual labels are fair independently of the
input and reference by Theorem 2.2, and classical fresh draws have the
same independence. Consequently, if $p_t(r)=\Pr(R_t=r)$, then

$$
\mathcal M_t(r)^\dagger(I_3)=p_t(r)I_3,
\qquad\|\mathcal M_t(r)\|_\diamond=p_t(r),
\qquad\sum_rp_t(r)=1.
\tag{30.9}
$$

For $p_t(r)>0$, division by that probability makes $\mathcal M_t(r)$
a convex mixture of unitary channels and hence a channel of diamond norm
one; when $p_t(r)=0$ it is the zero map. This proves the norm statement
including unoccupied states.

The exact pathwise identity is

$$
E_{t+1}=(1\oplus Y'^\dagger g_jY)E_t.
\tag{30.10}
$$

Conditional on $(R_t,j)$, fresh rounding is independent of the past
relative error. The next actual label is independent of that past and
has probability $1/2$. Summing (30.10) therefore gives

$$
\mathcal C_{t+1}
=\frac12\sum_{r,j}\mathcal L_{t,r,j}\circ\mathcal M_t(r).
\tag{30.11}
$$

Subtract $\mathcal C_t=(1/2)\sum_{r,j}\mathcal M_t(r)$ and use
(30.8)–(30.9):

$$
\begin{aligned}
\|\mathcal C_{t+1}-\mathcal C_t\|_\diamond
&\le\frac12\sum_{r,j}\frac{12}{m^2}p_t(r)=12/m^2,\\
\|\mathcal C_n-\operatorname{id}_3\|_\diamond
&\le\sum_{t=k}^{n-1}12/m^2=12L/m^2\le3\varepsilon/4.
\end{aligned}
\tag{30.12}
$$

The actual CP probabilities, including the prefix probabilities (30.6),
are necessary for this normalization. Unweighted sums over states do not
give (30.12).

At termination let $\widehat Q=\lambda^n\oplus Y_n$ and apply the
single full-$H$ unitary

$$
U_{R_n}=B\widehat Q^\dagger B^\dagger+(I_5-P_R).
\tag{30.13}
$$

It is unitary by Corollary 3.3. For every actual history and rounding
trajectory its encoded relative unitary is exactly
$\widehat Q^\dagger Q_h=1\oplus Y_n^\dagger G_h=E_n$.
Thus $\mathcal E_n=\iota\circ\mathcal C_n$, and the all-reference
trace-norm isometry in Lemma 3.1 turns (30.12) into (30.4). The phase
is $\lambda^n$, not $\lambda^L$: using the latter leaves the relative
factor $\lambda^k$ on $\xi$, which need not be trivial relative to $T$.
Likewise the determinant and signed quaternion cannot be discarded as
projective data, because coherences with $\xi$ belong to the recovery
target. All $\mathcal C_t$ with $t<n$ are analysis channels; no
intermediate inverse or quantum correction is executed.

For $k=n$, the exact-prefix construction in Theorem 8.4 applies its
inverse only at the horizon and has peak $2^n$; it requires no formula
with $L=0$ or $m=0$. The empty-history case gives the stated $n=0$
endpoint. These upper constructions use no shared seed, and are legal
within the larger class allowing arbitrary terminal CPTP decoders and
independent standard Borel seeds. $\square$

**Convention 30.3 (Static descriptions and precision).** The exact-prefix
updates are deterministic tables. The change to shell memory has
$2^{k+1}$ labelled rows, each with at most $16$ nonzero entries. The
ordinary shell update has at most $2N_m$ labelled rows with the same
output bound and can be reused for the remaining steps. At the horizon
there are at most $N_m$ terminal unitary choices for $k<n$, or $2^n$
for exact history. Products $G_p$, determinant choices, shell indices,
real probabilities and exact inverse controls in these tables are fixed
before the run. They contain no additional run-dependent state.

Their description length, preparation time, arithmetic precision and
control precision can be large. Definition 2.3 separates these resources
from peak width; (30.3) does not bound them or claim an efficient
finite-bit implementation. The known deterministic clock supplies only
the scheduled layer. A hidden prefix archive, free persistent tape or
history-dependent clock would change the complete-state count and is
not used by this construction.

## 31. A globally capped joint guess fails at positive exponential accuracy

**Corollary 31.1 (Switching envelope is an upper bound).** For every
$n\ge1$ and $0<\varepsilon<1/4$,

$$
W_n(\varepsilon)\le
\min\left\{2^n,
 \min_{0\le k<n}
 \max\left\{2^k,28\pi^2
  \left\lceil4\sqrt{(n-k)/\varepsilon}\right\rceil^3\right\}\right\}.
\tag{31.1}
$$

The inner minimum is over integers. This follows by choosing any one
of the controllers of Theorem 30.2. The value at $k=0$ is the original
rounding construction. The minimum, equivalently the infimum over the
finite switch set, is only an upper bound; no optimality among all
permitted controllers follows.

**Proposition 31.2 (Explicit failure of a uniform capped law).** For
all sufficiently large integers $n$, set

$$
\varepsilon_n=n2^{-2n/3},\qquad
L_n=\lceil2\log_2n\rceil,\qquad k_n=n-L_n.
\tag{31.2}
$$

Then $0<\varepsilon_n<1/4$, $0\le k_n<n$, and

$$
\frac{W_n(\varepsilon_n)}{2^n}
\le\max\left\{n^{-2},A(L_n/n)^{3/2}\right\}\longrightarrow0,
\qquad
\min\{2^n,(n/\varepsilon_n)^{3/2}\}=2^n.
\tag{31.3}
$$

In particular there is no positive constant $b$, independent of $n$
and $\varepsilon$, for which
$W_n(\varepsilon)\ge b\min\{2^n,(n/\varepsilon)^{3/2}\}$
holds for all sufficiently large $n$ and every $0<\varepsilon<1/4$.

Proof. The sequence $\varepsilon_n$ tends to zero and
$L_n=O(\log n)$, so eventually $1\le L_n<n$. Apply Theorem 30.2
with $k=k_n$, $L=L_n$ and
$m_n=\lceil4\sqrt{L_n/\varepsilon_n}\rceil$.
Since $L_n\ge2\log_2n$,

$$
2^{k_n}/2^n=2^{-L_n}\le n^{-2}.
\tag{31.4}
$$

Eventually $x_n=\sqrt{L_n/\varepsilon_n}\ge1$, so
$m_n\le5x_n$. The shell part of (30.3) then satisfies

$$
\frac{28\pi^2m_n^3}{2^n}
\le\frac{3500\pi^2(L_n/\varepsilon_n)^{3/2}}{2^n}
=A(L_n/n)^{3/2},
\tag{31.5}
$$

because $\varepsilon_n^{-3/2}=n^{-3/2}2^n$.
Both terms on the right of (31.3) tend to zero. But
$(n/\varepsilon_n)^{3/2}=(2^{2n/3})^{3/2}=2^n$ exactly.
Thus any proposed positive uniform lower constant is contradicted by
(31.3). $\square$

This refutes the uniform global guess
$W_n(\varepsilon)\asymp\min\{2^n,(n/\varepsilon)^{3/2}\}$
with constants independent of both variables. It does not refute the
fixed-$\varepsilon$ theorem (27.2). Indeed
$\ln(1/\varepsilon_n)=(2\ln2/3)n-\ln n$ is linear in $n$ to
leading order, so this sequence is outside Corollary 29.2. Nor does
(31.3) determine the optimal width along this sequence: it is a
constructive upper bound, without a matching lower bound there.

## 32. Attribution and the unresolved exponential-precision transition

**Convention 32.1 (Sources and status of the deductions).** The actual
instrument, common eigenphase, full-space embedding and separate exact
zero-error result are supplied by [OWN][OWN] and [FIVE][FIVE] at the
fixed revision in Convention 1.2. Bourgain–Gamburd's spectral theorem
[BG][BG], with the normalization and actual-generator correspondence
specified in §24, supplies the positive $\gamma$ of Definition 22.1.
No numerical gap estimate is added.

Proposition 28.2 is the strict-cap algebraic consequence of Theorems
4.3 and 22.2. Theorem 29.1 and Corollary 29.2 are source-relative
quantitative consequences of that budget, (22.6) and Theorem 8.4;
the existing generic estimates are reused. Definition 30.1 supplies the
counted prefix-to-shell interface. Theorem 30.2 applies the arbitrary-target
clause of Lemma 8.3 at that interface and the probability-weighted CP
telescoping of Theorem 8.4 afterwards. Proposition 31.2 combines that
admissible construction with the explicit sequence (31.2). These are
ordinary mathematical deductions in the declared resource model, with
no claim of exhaustive literature novelty, physical or QFT realization,
or Lean/kernel certification.

**Question 32.2 (Sharp joint law at exponentially small positive error).**
Determine the optimal joint dependence of $W_n(\varepsilon)$ when
$\ln(1/\varepsilon)$ is comparable to or larger than $n$, including
its transition to the separate exact endpoint $W_n(0)=2^n$. A matching
lower bound for the sequence (31.2), or for the switching envelope
(31.1), has not been established here. The envelope is not asserted
to be sharp.

The specific missing estimate is an accuracy-dependent necessary bound
on averaged full-qutrit recovery for arbitrary complete changing,
many-to-one and stochastic peak-width controllers, independent standard
Borel seeds and full-$H$ terminal CPTP decoders, that stays informative
when $\kappa\lfloor n/3\rfloor\le\ln W$. In that range the positive
part in (28.3) can vanish and (28.2) need not constrain accuracy.
The constant-contraction estimate (22.6) alone does not recover the
missing dependence on exponentially small positive $\varepsilon$.
A sharp estimate must respect actual joint history/record laws and
phase-sensitive distinguishability, permit the legal delayed controller,
and remain compatible with the exact-history upper bound. The vector
converse is necessary only; the width-one, horizon-one obstruction and
the separate exact endpoints in §§11 and 18 prevent promoting vector
survival to same-width operational sufficiency.

Theorem 29.1 settles the stated uniform matched regime, not this full
joint question. Corollary 27.1 retains its fixed-error quantifiers;
$W_0(\varepsilon)=1$ and $W_n(0)=2^n$ retain their separate meanings,
without evaluating a positive-error rounding formula at zero. Numerical
gap constants, optimal static-table size, finite-precision inverse
control, calibration, acquisition and communication costs also remain
outside these width results.

## 追加锚（本行以下为增补区）
