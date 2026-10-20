# AURIC–FIB approximate online recovery memory II: a common-tester bracket at three steps

## 1. The instrument, resource class and finite question

**Definition 1.1 (Actual encoded instrument).** Let $H=\mathbb C^5$ with
ordered orthonormal basis $e_0,\ldots,e_4$, and let $B:\mathbb C^3\to H$
be the isometry with columns

$$
u=(e_0+e_3)/\sqrt2,\qquad v=(e_1+e_4)/\sqrt2,\qquad w=e_2.
$$

Write $\iota(X)=BXB^\dagger$ and $P_R=BB^\dagger$. The two unrotated
operators and the two fixed measured operators are

$$
\begin{aligned}
K^H_0&=|u\rangle\langle e_0|+2^{-1/2}|v\rangle\langle e_2|
                         +|w\rangle\langle e_4|,\\
K^H_1&=|u\rangle\langle e_1|+2^{-1/2}|v\rangle\langle e_2|
                         +|w\rangle\langle e_3|,\\
M_0&=(\sqrt3K^H_0+iK^H_1)/2,\qquad
M_1=(iK^H_0+\sqrt3K^H_1)/2.
\end{aligned}
$$

The instrument is $X\mapsto M_jXM_j^\dagger$, with its actual classical
outcome $j$. Its aggregate is CPTP. It is repeated unchanged, with fresh
environment preparations and the same outgoing measurement. On encoded
inputs $M_jB=BV_j/\sqrt2$, where

$$
V_0=\frac12\begin{pmatrix}\sqrt3&i&0\\0&0&\sqrt3+i\\i&\sqrt3&0\end{pmatrix},
\qquad
V_1=\frac12\begin{pmatrix}i&\sqrt3&0\\0&0&\sqrt3+i\\\sqrt3&i&0\end{pmatrix}.
$$

Both $V_j$ are unitary. At horizon three, a history $h=h_1h_2h_3$ has
chronological unitary and restricted branch operator

$$
Q_h=V_{h_3}V_{h_2}V_{h_1},\qquad 2^{-3/2}BQ_h.
$$

In particular, even for an entangled encoded input, its probability is
$1/8$, independent of input and reference. The first acquired bit is the
rightmost factor. These are the instrument and restrictions of Recovery
Definition 2.1 and Theorem 2.2; fairness is restricted to the encoded
subspace, rather than asserted for arbitrary inputs in $H$.

**Definition 1.2 (Online recovery and its error).** A controller has a
known horizon, complete persistent classical states $r_k$, and, conditional
on a free shared seed $s$, time- and label-dependent stochastic updates
$T_{k,j,s}(b\mid r)$. The seed is finite or standard Borel, independent
of the input and all acquired labels, and shared with the terminal
decoder. The conditional initial law is also independent of the input
and future labels. All kernels and decoder families are measurable.
Fresh discarded randomness is integrated into the kernels. Every private
persistent variable, tape, archive, buffer, history-dependent program
choice and decoder input is part of $r_k$.

The width bound is

$$
\operatorname*{ess\,sup}_s\max_{0\le k\le3}|\mathcal R_{k,s}|\le6.
$$

There is no intermediate quantum feedback, postselection, reference
access, retained environment, or input-dependent quantum side information.
The known horizon, deterministic schedule and nonuniform static tables
are fixed resources; they contain no additional information about a
particular run. Every terminal map $D^H_{r,s}:M_5\to M_5$ may be an
arbitrary system-only CPTP channel, including on singleton records.
For the terminal law $p_s(r\mid h)$ the recovered encoded channel is

$$
\mathcal E=\mathbb E_s\frac18\sum_{h,r}p_s(r\mid h)
       D^H_{r,s}\circ\iota\circ\operatorname{Ad}_{Q_h}.
$$

Here $\operatorname{Ad}_A(X)=AXA^\dagger$, including when $A$ is not
unitary. Let $\epsilon_{\rm op}(6,3)$ be the attained minimum of
$\|\mathcal E-\iota\|_\diamond$ in this class. The diamond norm is
unhalved:

$$
\|\Delta\|_\diamond
=\sup_{d<\infty}\sup_{X\ne0}
  \frac{\|(\Delta\otimes\operatorname{id}_{M_d})(X)\|_1}{\|X\|_1}.
$$

It acts on the averaged channel. There is no per-seed or per-history
success requirement. Every reference in the supremum remains untouched.
This is Recovery Definitions 2.3–2.4 and 18.1 at width six and horizon
three, with the attainment supplied by Recovery Theorem 18.2.

**Convention 1.3 (Exact use of the existing recovery interfaces).** The
CPTP retraction of Recovery Lemma 3.1 is

$$
C(X)=B^\dagger XB+
       \operatorname{Tr}((I_5-P_R)X)|0\rangle\langle0|,
\qquad C\iota=\operatorname{id}_3.
$$

Recovery Theorem 3.2 applies to the entire seed average: a full-space
decoder gives $D_{r,s}=CD^H_{r,s}\iota$, while a qutrit decoder lifts to
$D^H_{r,s}=\iota D_{r,s}C$. The first operation cannot increase encoded
error and the second preserves it exactly, with every finite reference.
Thus the optimization below is exactly the original full-$H$ optimum,
written with arbitrary qutrit CPTP decoders and target
$\operatorname{id}_3$. It concerns encoded qutrit input and target.

Recovery Theorem 13.1 replaces the whole averaged channel by a finite
independent mixture of deterministic full controller programs and
program-indexed CPTP decoders. This is channel equality, not selection of
one successful seed. Recovery Theorem 43.2 identifies the online and
offline feasible averaged-channel sets when $W\ge2^{n-1}$; here
$6\ge4$. Its realization retains prefixes through time two and makes
the desired record transition upon reading the third label. These
suppliers are reused with these parameters and operations; their general
proofs are not additional results of this volume.

## 2. All complete partitions and the exact Choi optimization

**Theorem 2.1 (The 266-partition feasible set).** Put
$\mathcal H_3=\{0,1\}^3$ and let $\Pi_6$ be its unlabeled partitions
into six nonempty cells. For $\pi\in\Pi_6$ define

$$
\mathcal K_\pi=
\left\{\frac18\sum_{C\in\pi}\sum_{h\in C}
           D_C\circ\operatorname{Ad}_{Q_h}:D_C\text{ CPTP}\right\}.
$$

The original feasible qutrit averaged-channel set is exactly

$$
\mathcal K=\operatorname{conv}\left(\bigcup_{\pi\in\Pi_6}
                                      \mathcal K_\pi\right).
\tag{2.1}
$$

There are 210 partitions consisting of two disjoint pairs and four
singletons, and 56 consisting of one triple and five singletons.

Proof. Apply the finite-program replacement in Convention 1.3. Each
deterministic program induces a partition with at most six terminal
cells. If it has fewer, split cells and duplicate the decoder on each
piece until there are six. This preserves the entire decoded channel.
Group equal partitions in the independent mixture and average their
record decoders, which remain CPTP. This gives the inclusion in (2.1).
Conversely, each partition and each independent mixture on its decoder
choices is legal by Recovery Theorem 43.2. Thus both inclusions preserve
the online peak bound as well as the averaged channel.

Six nonempty cells account for eight elements with excess two over
singleton sizes. The excess is either $1+1$ or $2$, giving precisely
the two shapes stated. Choosing four elements and their matching gives
$\binom84\,3=210$; choosing the triple gives $\binom83=56$. These
are complete partitions: all eight histories occur once. Each of the 28
pairs occurs in $\binom62=15$ matchings, and each of the 56 triples
occurs once. Consequently there are $420+56=476$ collision-cell
incidences and 84 distinct collision subsets. Equation (2.1) is a
convexification of channels; it does not replace their diamond distance
by the minimum of separately optimized partition errors. $\square$

**Theorem 2.2 (Exact aggregation into 85 decoder blocks).** Use the
unnormalized output-first Choi convention

$$
|A\rangle\!\rangle=\sum_{i,j}A_{ij}|i\rangle_{\rm out}|j\rangle_{\rm in},
\qquad J(D)=\sum_a|D_a\rangle\!\rangle\langle\!\langle D_a|.
$$

Thus a CPTP Choi matrix is positive with
$\operatorname{Tr}_{\rm out}J(D)=I_3$, and $J_{\rm id}=|I_3\rangle\!\rangle
\langle\!\langle I_3|$ has trace three. Define

$$
B_h=I_3\otimes Q_h^{\mathsf T},\qquad
\mathcal L_C(X)=\sum_{h\in C}B_hXB_h^\dagger.
\tag{2.2}
$$

Let $\mathcal M$ be the 210 two-edge matchings and $\mathcal C_3$ the
56 triples. Choose nonnegative $t_M,t_C$ with total one, and put

$$
a=\sum_{M\in\mathcal M}t_M,\qquad b=\sum_{C\in\mathcal C_3}t_C,
\qquad m_e=\sum_{M\ni e}t_M.
$$

Then $J_F$ ranges exactly over the Choi matrices of $\mathcal K$ when

$$
\begin{aligned}
X_e&\succeq0,&\operatorname{Tr}_{\rm out}X_e&=m_eI_3
                                           && (|e|=2),\\
X_C&\succeq0,&\operatorname{Tr}_{\rm out}X_C&=t_CI_3
                                           && (|C|=3),\\
Y&\succeq0,&\operatorname{Tr}_{\rm out}Y&=(4a+5b)I_3,\\
J_F&=\frac18\left[Y+\sum_{|e|=2}\mathcal L_e(X_e)
                         +\sum_{|C|=3}\mathcal L_C(X_C)\right].
\end{aligned}
\tag{2.3}
$$

The 28 pair blocks, 56 triple blocks and one singleton block are all
$9\times9$ positive matrices. The exact global optimum is the minimum
of $\lambda$ subject to (2.3) and a Hermitian $Z$ satisfying

$$
Z\succeq J_F-J_{\rm id},\qquad Z\succeq J_{\rm id}-J_F,\qquad
\operatorname{Tr}_{\rm out}Z\preceq\lambda I_3.
\tag{2.4}
$$

Proof. Before aggregation the variables are
$X_{\pi,C}=t_\pi J(D_{\pi,C})$, so
$\operatorname{Tr}_{\rm out}X_{\pi,C}=t_\pi I_3$. The vectorization
identity $|D_aQ_h\rangle\!\rangle=B_h|D_a\rangle\!\rangle$ proves
(2.2), with transpose on $Q_h$, not adjoint. Adding all occurrences of
the identical actual pair gives $X_e$. For the reverse direction, if
$m_e>0$ assign $t_MX_e/m_e$ to its occurrence in $M$. This has the
required partial trace $t_MI_3$. If $m_e=0$, positivity and zero trace
force $X_e=0$; no division is made. The same observation handles zero
triple weights.

For a singleton $h$, the channel $D_{\pi,h}\operatorname{Ad}_{Q_h}$
ranges over all CPTP maps, since the known unitary can be absorbed into
the unrestricted decoder. Add the subnormalized Choi matrices of these
transformed singleton maps to obtain $Y$. Conversely, put
$d=4a+5b\in[4,5]$. For every singleton occurrence in partition $\pi$,
assign transformed subnormalized Choi matrix $t_\pi Y/d$ and undo
$Q_h$ in its decoder. Its partial trace is $t_\pi I_3$, and summing
over all singleton occurrences recovers $Y$. In particular, singleton
inverses are not constraints in (2.3). Leakage channels are retained.

This proves the reversibility of the aggregation. It identifies repeated
actual subsets, not subsets with merely equal spectra. Finally (2.4) is
the Hermiticity-preserving diamond-norm epigraph, equivalently the finite
SDP dual of the tester formula in actual-word §66 with $d=3$ and
$J(\Delta)=J_F-J_{\rm id}$. Its partial trace is zero. No numerical
feasibility or optimization is needed for this exact representation.
$\square$

## 3. One common tester and the admissible covariance

**Theorem 3.1 (Global common-tester interface).** In the Choi coordinates
of Theorem 2.2 set

$$
\mathfrak T_3=\{(\rho,W):\rho\succeq0,\ \operatorname{Tr}\rho=1,
                         \ 0\preceq W\preceq I_3\otimes\rho\}.
$$

Here $\rho$ is the reference marginal; the physical system marginal of
$(I\otimes\sqrt\rho)|I_3\rangle\!\rangle$ is $\rho^{\mathsf T}$.
For a collision cell define its unnormalized support

$$
q_C(W)=\max_{X\succeq0,\ \operatorname{Tr}_{\rm out}X=I_3}
                       \operatorname{Tr}(W\mathcal L_C(X)),
\qquad
q_1(W)=\max_{X\succeq0,\ \operatorname{Tr}_{\rm out}X=I_3}
                       \operatorname{Tr}(WX).
$$

Then, with disjointness referring to actual histories,

$$
\begin{aligned}
H(W)=\frac18\max\bigg\{&4q_1(W)+
               \max_{e\cap f=\varnothing}[q_e(W)+q_f(W)],\\
                       &5q_1(W)+\max_{|C|=3}q_C(W)\bigg\},\\
\epsilon_{\rm op}(6,3)
&=2\max_{(\rho,W)\in\mathfrak T_3}
             [\operatorname{Tr}(WJ_{\rm id})-H(W)].
\end{aligned}
\tag{3.1}
$$

Each support has the exact dual

$$
q_C(W)=\min_{Y_C=Y_C^\dagger}
 \{\operatorname{Tr}Y_C:I_3\otimes Y_C\succeq\mathcal L_C^*(W)\},
\quad
\mathcal L_C^*(W)=\sum_{h\in C}B_h^\dagger WB_h,
\tag{3.2}
$$

and the singleton version replaces $\mathcal L_C^*(W)$ by $W$.

Proof. Reuse actual-word Theorem 66.2's unhalved tester formula (66.6)
for $\operatorname{id}_3-F$. The set (2.1) is compact and convex:
each $\mathcal K_\pi$ is a compact convex image of finitely many CPTP
Choi sets, and there are finitely many $\pi$. Finite-dimensional convex
minimax therefore exchanges its minimum with the tester maximum.
At fixed $W$, support of the convex hull is the largest partition
support, and support within a partition separates over its decoders.
Absorb singleton unitaries as in Theorem 2.2. This gives exactly $H(W)$.
The factor two comes from the trace-zero channel-difference tester, not
from a halved distance convention. Equation (3.2) is the CPTP Choi
support dual; its primal has the strictly positive feasible point
$X=I_9/3$, so its finite SDP duality has no gap.

Explicitly, choose one common $(\rho,W)$ and the 85 dual matrices in
(3.2). A scalar $z_0$ must satisfy all 210 inequalities

$$
8z_0\ge4\operatorname{Tr}Y_1+
                \operatorname{Tr}Y_e+\operatorname{Tr}Y_f
\qquad(e\cap f=\varnothing)
$$

and all 56 inequalities

$$
8z_0\ge5\operatorname{Tr}Y_1+\operatorname{Tr}Y_C.
$$

The objective is $2[\operatorname{Tr}(WJ_{\rm id})-z_0]$.
Every support minimum can be attained simultaneously, because these
dual variables are independent at fixed $W$. This is the all-controller
lower interface; separately optimized testers for different cells or
partitions cannot replace it. $\square$

**Theorem 3.2 (Phase covariance and the 29-protocol bound).** Put
$P=|\xi\rangle\langle\xi|$, $P_T=I_3-P$, and
$U_\theta=P+e^{i\theta}P_T$. There is an optimal feasible channel
covariant under all $U_\theta$. Its Choi matrix has charge-block sizes
$5,2,2$, and its trace-preserving affine space has real dimension 28.
It can be realized as a mixture of at most 29 phase-covariant partition
protocols.

Proof. Every $Q_h$ preserves the same decomposition
$\mathbb C\xi\oplus T$, so commutes with $U_\theta$. Conjugating the
input and output of each decoder by $U_\theta$ preserves its partition
and all permissions. It gives the corresponding conjugation of $F$;
the target identity is invariant and the diamond distance is unchanged.
Averaging over $\theta$ preserves feasibility and cannot increase the
distance. Each averaged decoder is still a CPTP decoder for that same
partition, so this averaging can be performed before seed mixing.

The Choi action is $U_\theta\otimes\overline{U_\theta}$. Its zero
charge space is
$(\mathbb C\xi\otimes\overline{\mathbb C\xi})\oplus
(T\otimes\overline T)$ of dimension five. The two nonzero charge
spaces have dimension two each. The real Hermitian dimension of the
commutant is $5^2+2^2+2^2=33$. The partial trace maps onto the
Hermitian input block-diagonal space of dimension $1+4=5$; surjectivity
follows by taking $I_3/3$ tensored with an arbitrary such input matrix.
Imposing the partial trace $I_3$ therefore leaves dimension $33-5=28$.
Carathéodory's finite-dimensional convex-hull theorem now gives 29
partition channels in this affine space. This dimension count uses only
the commuting $U(1)$ action. An arbitrary $SU(2)$ conjugation on $T$
does not commute with the actual words and is not a permitted symmetry
reduction here. Nor does the bound 29 establish optimality of two seeds.
$\square$
## 4. Signed chronological word geometry

**Definition 4.1 (The fixed line and the Pauli frame).** In qutrit
coordinates let

$$
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\quad
f_1=(1,-1,0)^{\mathsf T}/\sqrt2,\quad
f_2=(1,1,-2)^{\mathsf T}/\sqrt6.
$$

Use $(f_1,f_2)$ on $T=\xi^\perp$, with the usual Pauli matrices
$\sigma_x,\sigma_y,\sigma_z$. The restrictions of $V_0,V_1$ are

$$
A=\frac14\begin{pmatrix}\sqrt3-i&3+i\sqrt3\\
                         3-i\sqrt3&-\sqrt3-i\end{pmatrix},
\qquad J=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\qquad g_1=AJ.
$$

Since $V_j\xi=e^{i\pi/6}\xi$, at horizon three
$Q_h=iP\oplus G_h$, with
$G_h=g_{h_3}g_{h_2}g_{h_1}$. Set

$$
K_j=A^{-j}JA^j=n_j\cdot\sigma\quad(0\le j\le2),\qquad
\tau=\frac{3\sqrt3}{8},\quad c=\frac{\sqrt{13}}4,\quad
r=\sqrt{1+\tau}.
$$

Here the $K_j$ are two-dimensional reflections, distinct from the
full-space instrument operators $K^H_j$.

**Theorem 4.2 (Actual signed Gram data).** The eight words obey

$$
G_h=A^3R_h,\qquad R_h=K_2^{h_3}K_1^{h_2}K_0^{h_1}.
\tag{4.1}
$$

Their Pauli vectors are

$$
n_0=(0,0,-1),\qquad
n_1=(-\sqrt3/4,3/4,1/2),\qquad
n_2=(-5\sqrt3/16,-9/16,-5/8).
\tag{4.2}
$$

Thus their Gram matrix and oriented volume are

$$
(n_i\cdot n_j)_{i,j=0}^2=
\begin{pmatrix}1&-1/2&5/8\\-1/2&1&-1/2\\5/8&-1/2&1\end{pmatrix},
\qquad \det[n_0,n_1,n_2]=-\tau.
\tag{4.3}
$$

For $h<k$ in lexicographic order, the normalized overlaps
$\operatorname{Tr}(G_h^\dagger G_k)/2$ have the following complete
classification.

| Histories that differ | Overlap | Number of unordered pairs |
| --- | --- | --- |
| In one bit | $0$ | $12$ |
| In two adjacent positions | $-1/2$ | $8$ |
| In the two outer positions, common middle bit $0$ | $5/8$ | $2$ |
| In the two outer positions, common middle bit $1$ | $-1/8$ | $2$ |
| $000/111$ and $001/110$ | $+i\tau$ | $2$ |
| $010/101$ and $011/100$ | $-i\tau$ | $2$ |

Proof. Moving the three factors $A$ to the left in the chronological
product gives (4.1). Direct Pauli decomposition starts from

$$
iA=\frac{I+i(3\sigma_x-\sqrt3\sigma_y+\sqrt3\sigma_z)}4
$$

and gives (4.2); dot products and the determinant then give (4.3).
To obtain the table, cancel common factors in $R_h^\dagger R_k$ and
use

$$
(a\cdot\sigma)(b\cdot\sigma)
 =(a\cdot b)I+i(a\times b)\cdot\sigma.
\tag{4.4}
$$

One-bit differences have trace zero; adjacent two-bit differences give
$n_0\cdot n_1$ or $n_1\cdot n_2$. Outer differences at middle bit zero
give $n_0\cdot n_2$. At middle bit one their trace is
$2(n_0\cdot n_1)(n_1\cdot n_2)-n_0\cdot n_2=-1/8$.
For complementary histories, the triple-product term in (4.4) gives
the two displayed signs. There are respectively 12, 8, 2, 2 and 4
pairs of these forms, totaling $\binom82=28$. No absolute-value
replacement has been made in the signed table. $\square$

**Theorem 4.3 (Repeated relatives and their actual axes).** The two good
pairs $\{000,101\}$ and $\{001,100\}$ have the identical relative
$1\oplus L_g$, where

$$
L_g=K_2K_0=
\begin{pmatrix}
5/8&-5\sqrt3/16+9i/16\\
5\sqrt3/16+9i/16&5/8
\end{pmatrix}.
$$

The first two complementary pairs in the table have identical relative
$1\oplus L_o$, where

$$
L_o=K_2K_1K_0=
\begin{pmatrix}
1/2+i\tau&5\sqrt3/16+3i/16\\
5\sqrt3/16-3i/16&-1/2+i\tau
\end{pmatrix}.
$$

Put $b_o=\sqrt{1-\tau^2}=\sqrt{37}/8$ and define the traceless
Hermitian unitaries on $T$

$$
N_g=\frac{K_2K_0-K_0K_2}{2i\sqrt{1-(5/8)^2}},\qquad
N_o=\frac{\operatorname{Re}L_o}{b_o}.
\tag{4.5}
$$

Then

$$
N_g=\frac{3\sqrt3\,\sigma_x-5\sigma_y}{2\sqrt{13}},\qquad
N_o=\frac{5\sqrt3\,\sigma_x-3\sigma_y+8\sigma_z}{2\sqrt{37}},
\qquad \gamma=\frac{\operatorname{Tr}_T(N_gN_o)}2
              =\frac{15}{\sqrt{481}}.
\tag{4.6}
$$

For all four complementary pairs, write the Hermitian part of the
ordered relative $T$-unitary as $v_j\cdot\sigma$. The first two use
$v_0$, and the last two use $v_2$, where

$$
\begin{aligned}
v_0&=-\tfrac12(n_0+n_2)-\tfrac58n_1
                 =(5\sqrt3,-3,8)/16,\\
v_2&=-\tfrac12n_0+\tfrac12n_2+\tfrac58n_1
                 =(-5\sqrt3,3,8)/16,\\
v_0\cdot n_0&=v_2\cdot n_0=-\tfrac12,\qquad |v_j|=b_o.
\end{aligned}
\tag{4.7}
$$

Proof. Substitute (4.1) for the indicated ordered pairs. Both good
relatives reduce to $K_2K_0$, and both first complementary relatives
to $K_2K_1K_0$. Expanding with (4.4) gives the matrices and (4.5)–(4.7).
For the last two complementary pairs the relative is
$v_2\cdot\sigma-i\tau I$, whereas the first two are
$v_0\cdot\sigma+i\tau I$. The norms of $v_j$ and the sign of their
$n_0$ projection are independent of this imaginary-trace sign.
The dot product in (4.6) follows from
$(3\sqrt3,-5,0)\cdot(5\sqrt3,-3,8)=60$.
These identities retain the actual axes; equality of trace magnitudes
alone would not establish them. $\square$

## 5. A full-rank common survival tester for every cell

**Definition 5.1 (The tester and summed cell scores).** For $0<p<1$ put
$q=1-p$ and

$$
\rho_p=pP+\frac q2P_T,\qquad
|\psi_p\rangle=\sqrt p\,|\xi\rangle|\bar\xi\rangle+
       \sqrt{q/2}\sum_{j=1}^2|f_j\rangle|\bar f_j\rangle.
$$

The physical system marginal is $\rho_p$; the reference marginal is
$\rho_p^{\mathsf T}$. Define

$$
f_p(F)=\langle\psi_p|(F\otimes\operatorname{id})
       (|\psi_p\rangle\langle\psi_p|)|\psi_p\rangle.
$$

In Theorem 3.1 this survival test has
$\rho=\rho_p^{\mathsf T}$ and
$W=|\rho_p\rangle\!\rangle\langle\!\langle\rho_p|$;
$0\preceq W\preceq I\otimes\rho_p^{\mathsf T}$ and
$\operatorname{Tr}(WJ_{\rm id})=1$. The rank of the physical input
density is three. For a cell decoder with Kraus operators $D_a$, let

$$
S_C(p;D)=\sum_{h\in C,a}|\operatorname{Tr}(\rho_pD_aQ_h)|^2.
\tag{5.1}
$$

This score is not divided by the cell size. The contribution to $f_p$
is $S_C/8$. Since the two-outcome survival measurement is admissible,

$$
\|F-\operatorname{id}\|_\diamond\ge2(1-f_p(F)).
\tag{5.2}
$$

The factor two is required for the unhalved trace norm.

**Theorem 5.2 (Arbitrary-CPTP support bounds and the two exact pair
scores).** Let $\Gamma_C$ be the $|C|\times|C|$ Gram matrix

$$
(\Gamma_C)_{hk}=\operatorname{Tr}(G_h^\dagger G_k)/2.
$$

For every qutrit CPTP decoder, including decoders that mix $T$ and
$\mathbb C\xi$,

$$
S_C(p;D)\le
 [\sqrt{|C|}\,p+q\sqrt{\lambda_{\max}(\Gamma_C)}]^2.
\tag{5.3}
$$

The exact maximum scores on a good pair and on a complementary pair are,
respectively,

$$
g(p)=2[p+cq]^2,\qquad
o(p)=2p^2+2rpq+(1+\tau)q^2.
\tag{5.4}
$$

For $0<p<1$, equality in either of these pair maxima forces its polar
unitary decoder as a channel. Singleton score is at most one, with
equality forcing the inverse channel $\operatorname{Ad}_{Q_h^\dagger}$.

Proof. Write $D_{a,T}=P_TD_aP_T|_T$. Since $Q_h=iP\oplus G_h$,
the trace in (5.1) splits into the line term
$ip\langle\xi|D_a|\xi\rangle$ and the plane term
$(q/2)\operatorname{Tr}(D_{a,T}G_h)$. The squared Euclidean norm of
all line terms, indexed by $(h,a)$, is at most $|C|p^2$, since
$\sum_a|\langle\xi|D_a|\xi\rangle|^2\le1$.
The Hilbert–Schmidt Gram matrix of $G_h^\dagger$ has largest
eigenvalue $2\lambda_{\max}(\Gamma_C)$, with conjugation of the
Gram coordinates leaving the eigenvalues unchanged. Thus

$$
\begin{aligned}
\sum_{h,a}|\operatorname{Tr}(D_{a,T}G_h)|^2
 &\le2\lambda_{\max}(\Gamma_C)
                           \sum_a\|D_{a,T}\|_{\rm HS}^2,\\
\sum_a\|D_{a,T}\|_{\rm HS}^2
 &\le\operatorname{Tr}\left(P_T\sum_aD_a^\dagger D_a\right)=2.
\end{aligned}
$$

Multiplication by $q^2/4$ bounds the plane contribution by
$q^2\lambda_{\max}(\Gamma_C)$. Euclidean triangle inequality now
proves (5.3). The column-norm inequality includes all leakage slack;
there is no assumption that the decoder preserves $T$.

For the exact scores, absorb the first actual branch into the decoder
and diagonalize $R=Q_h^\dagger Q_k$. Its eigenphases may be chosen as
$0,\theta,-\theta$ on a good pair, with $\cos\theta=5/8$, and
$0,\phi,\pi-\phi$ or their negatives on a complementary pair, with
$\sin\phi=\tau$ and $0<\phi<\pi/2$. In each case the phase range is
strictly shorter than $\pi$. Let the diagonal weights of $\rho_p$ be
$w_0=p,w_1=w_2=q/2$, and for absorbed Kraus operators $E_a$ set
$d_{aj}=e^{i\theta_j/2}(E_a)_{jj}$. The pair score expands to

$$
\sum_{i,j}2w_iw_j\cos((\theta_i-\theta_j)/2)
                        \sum_a d_{ai}\overline{d_{aj}}.
\tag{5.5}
$$

Every cosine coefficient is strictly positive, each diagonal-column norm
$\sum_a|d_{aj}|^2$ is at most one, and each real Gram entry in (5.5)
is at most one by Cauchy–Schwarz. Replacing them by one gives the
maximum, attained by $E=R^{-1/2}$ with this phase choice. These are
the same column-norm bounds used by actual-word §67, now retaining the
spectator weight $p>0$ and the actual odd relative phases.

On a good pair, $\operatorname{Tr}(\rho_pR^{1/2})=p+cq$.
On a complementary pair it is
$p+qr(1+i)/2$ or its conjugate, giving (5.4).
All $w_i$ are positive. Equality in (5.5) forces every diagonal-column
norm to be one and all corrected column vectors $(d_{aj})_a$ to
coincide. Trace preservation then leaves zero norm for every off-diagonal
Kraus entry. Hence $E_a=\alpha_aR^{-1/2}$ with
$\sum_a|\alpha_a|^2=1$, proving uniqueness as a channel, including
against nonunitary and leakage alternatives.

For a singleton, if $F_a=D_aQ_h$, then
$\sum_a|\operatorname{Tr}(\rho_pF_a)|^2\le
\sum_a\operatorname{Tr}(\rho_pF_a^\dagger F_a)=1$.
Equality for full-rank $\rho_p$ in this weighted Cauchy inequality
forces every $F_a$ to be scalar identity, so the decoded channel is
the identity. This proves the singleton assertion. $\square$

**Theorem 5.3 (All-pair and all-triple exclusion at the common tester).**
Define

$$
A_0=4c-2r,\qquad B_0=\tau-5/8,\qquad
p_0=\frac{B_0}{A_0+B_0},\qquad
L=1-[p_0+c(1-p_0)]^2.
\tag{5.6}
$$

Then $0<p_0<1/32$, $g(p_0)=o(p_0)$, and

$$
\max_{F\in\mathcal K}f_{p_0}(F)=\frac12+\frac{g(p_0)}4,
\qquad \epsilon_{\rm op}(6,3)\ge L.
\tag{5.7}
$$

Every maximizing partition consists of two pairs chosen from the two good
and four complementary pairs and four singleton records. All other pair
types and all triple partitions have strictly smaller survival score.

Proof. The elementary radical comparisons
$9/10<c$, $5/8<\tau<21/32$ and $r<13/10$ imply
$A_0>1$ and $0<B_0<1/32$. Therefore $p_0>0$ and
$A_0>31B_0$, giving $p_0<1/32$. Direct expansion yields

$$
g(p)-o(p)=q(A_0p-B_0q),
$$

so they agree at $p_0$. By the signed table, every pair other than a
good or complementary pair has $\lambda_{\max}(\Gamma_C)\le3/2$.
Its (5.3) bound is
$[\sqrt2p+q\sqrt{3/2}]^2<2[p+cq]^2$ for $q>0$.

For completeness, every triple satisfies
$\lambda_{\max}(\Gamma_C)\le17/8$. If it contains a complementary
edge, its other two edges have Hamming distances one and two: one overlap
vanishes and the other has magnitude at most $5/8$. The three Gram
eigenvalues are then $1,1\pm\sqrt{\tau^2+|z_0|^2}$, so the maximum
is at most
$1+\sqrt{\tau^2+25/64}=1+c<17/8$.
There are 24 such triples, since there are four complementary edges
and six choices of third vertex, with no triple containing two of these
disjoint edges. A triple with no complementary edge contains at most
one good edge, since the two good edges are disjoint; all its other
overlaps have magnitude at most $1/2$. The absolute row-sum bound is
therefore $1+5/8+1/2=17/8$. This covers the other 32 triples.

At $p=p_0$, (5.3) bounds any triple score by

$$
\begin{aligned}
[\sqrt3p+\sqrt{17/8}(1-p)]^2
 &<[2p+(47/32)(1-p)]^2\\
 &<(1521/1024)^2<9/4\le2g(p)-1.
\end{aligned}
\tag{5.8}
$$

Here $\sqrt3<2$, $\sqrt{17/8}<47/32$ and $p<1/32$ justify
the strict rational comparisons. The last inequality uses
$p+c(1-p)\ge c$, hence $g(p)\ge2c^2=13/8$.
Thus a two-pair partition scores at most $4+2g(p_0)$; a triple
partition scores strictly less than
$5+[2g(p_0)-1]=4+2g(p_0)$. Dividing by eight gives (5.7)'s upper
bound on survival. The good-pair partition displayed in §7 attains
this linear support, as does the odd-pair partition there, by their
polar decoders and singleton inverses. Seed averaging preserves the
same upper bound on this one linear functional. Finally (5.2) gives
$2[1-(1/2+g/4)]=1-g/2=L$. $\square$

## 6. Why the global lower endpoint is strictly unattainable

**Theorem 6.1 (Strict lower bound).** In the original operational class,

$$
L<\epsilon_{\rm op}(6,3).
\tag{6.1}
$$

Proof. Suppose a feasible $F$ had diamond error $L$. Both inequalities
in

$$
\|F-\operatorname{id}\|_\diamond
\ge2(1-f_{p_0}(F))\ge L
$$

would be equalities. Represent $F$ by (2.1). Linearity and the strict
gaps in Theorem 5.3 force every positive-weight component to maximize
the survival functional. It can contain only good or complementary
pairs, and its decoders are the unique polar channels and singleton
inverses of Theorem 5.2. Among these six possible pair edges there are
11 disjoint two-edge matchings: one good/good, six complementary/
complementary, and four mixed. Only the good/good partition has no
complementary cell.

Write $\sigma=(F\otimes\operatorname{id})(|\psi_{p_0}\rangle
\langle\psi_{p_0}|)$. The survival projector can attain the trace
distance from its target pure state only if $|\psi_{p_0}\rangle$ is
an eigenvector of $\sigma$. Indeed, equality in the trace-zero
variational formula requires that projector to be a maximizing spectral
test for $|\psi_{p_0}\rangle\langle\psi_{p_0}|-\sigma$, so its
off-diagonal block relative to that line must vanish.

This eigenvector condition fails whenever a complementary cell has
positive weight. To see it without identifying the four axes, write
the action of any component as

$$
\sigma|\psi_p\rangle=|M\sqrt{\rho_p}\rangle\!\rangle.
$$

For one polar-corrected conditional pair, its two residual unitaries
are $H,H^\dagger$ with equal probability, $H$ acting as one on
$\xi$. If $t_p=\operatorname{Tr}(\rho_pH)$, its contribution to
$M$ is

$$
M_C=\tfrac12(\overline{t_p}H+t_pH^\dagger).
\tag{6.2}
$$

For a complementary relative $v_j\cdot\sigma\pm i\tau I$, put
$N_j=(v_j\cdot\sigma)/b_o$ and $z=\sqrt{1-\tau}$. The principal
root has plane block

$$
H_T=\frac{(1\pm i)rI+(1\mp i)zN_j}{2},\qquad
t_p=p+\frac{qr(1\pm i)}2.
$$

Substitution into (6.2) gives traceless plane block
$pzN_j/2$. By (4.7) its Pauli vector has $n_0$ projection
$-pz/(4b_o)<0$. Each such conditional cell has actual mass $2/8=1/4$,
so its contribution to the same projection in $M$ is strictly negative
when its seed weight is positive. Good pairs and inverse singletons
give only scalar plane blocks in (6.2). Consequently positive
complementary contributions cannot cancel, even mixing all four
complementary pairs with their two opposite imaginary-trace signs.

Since $\rho_{p_0}$ is invertible, the relation
$|M\sqrt{\rho_{p_0}}\rangle\!\rangle\propto
|\sqrt{\rho_{p_0}}\rangle\!\rangle$ would require $M$ to be scalar
identity. Its nonzero traceless plane block excludes that relation.
Thus the survival measurement strictly undershoots the trace distance,
contradicting equality at $L$.

If there is no complementary contribution, the only component is the
good/good partition $\pi_g$ of §7 with its polar and inverse decoders.
Its $T$-Bell error is $3/16$. This is larger than $L$: using
$p_0>0$ and $c<1$ in (5.6) gives
$L<1-c^2=3/16$. This case also contradicts error $L$.
No feasible channel therefore has error exactly $L$. Compact attainment
from Recovery Theorem 18.2, or from (2.1), is essential for the final
step: the attained minimum is strictly greater than $L$. $\square$

## 7. Two legal online partitions and their full qutrit channels

**Definition 7.1 (Good and odd protocols).** Consider the complete
partitions

$$
\begin{aligned}
\pi_g&=\{\{000,101\},\{001,100\},\{010\},\{011\},\{110\},\{111\}\},\\
\pi_o&=\{\{000,111\},\{001,110\},\{010\},\{011\},\{100\},\{101\}\}.
\end{aligned}
\tag{7.1}
$$

On singleton $h$ use $\operatorname{Ad}_{Q_h^\dagger}$. For either
selected pair $\{h,k\}$ with $h<k$ put

$$
S_{hk}=(Q_h+Q_k)/2,\qquad
P_{hk}=S_{hk}(S_{hk}^\dagger S_{hk})^{-1/2},\qquad
D_{hk}=\operatorname{Ad}_{P_{hk}^\dagger}.
\tag{7.2}
$$

Use an independent shared seed to select $\pi_o$ with probability $s$
and $\pi_g$ with probability $1-s$. Denote its averaged qutrit channel
by $F_s$.

**Theorem 7.2 (Legal polar corrections and channel formula).** Every
protocol of Definition 7.1, $0\le s\le1$, is legal in the original
online peak-six model. Let

$$
\begin{aligned}
u_g&=3/32,& a_g&=(1-c)/2,\\
u_o&=(1-\tau)/4,& a_o&=(2-r)/4,\\
w_g&=(1-s)u_g,& w_o&=su_o,\\
u&=w_g+w_o,&a&=(1-s)a_g+sa_o,\qquad
\beta=s\sqrt{1-\tau}/4.
\end{aligned}
\tag{7.3}
$$

With $N_g,N_o$ extended by zero on $\xi$, its full block action is

$$
\begin{aligned}
F_s(P)&=P,\\
F_s(X)&=(1-u)X+w_gN_gXN_g+w_oN_oXN_o
                                      &&(X=P_TXP_T),\\
F_s(|v\rangle\langle\xi|)
 &=|[(1-a)I_T+\beta N_o]v\rangle\langle\xi|
                                      &&(v\in T).
\end{aligned}
\tag{7.4}
$$

The reverse coherence block is the adjoint of the last line, extended
complex linearly. In particular (7.4) specifies the entire qutrit
channel, including spectator coherences.

Proof. Retaining the actual prefix until time two uses widths $1,2,4$.
Upon the third bit, move directly to the cell of (7.1), giving width
six. The layer widths are $1,2,4,6$ for both seeds, with no transient
eight-state layer. This is the $n=3,W=6$ realization in Recovery
Theorem 43.2. The free seed is independent of the actual history and
input; it is not a private history archive.

For a selected pair write $R=Q_h^\dagger Q_k=1\oplus L_g$ or
$1\oplus L_o$. None of its eigenvalues is $-1$, and all phases in
Theorem 5.2 have half-phase cosine positive. Thus $S_{hk}$ is
invertible and its polar unitary is $P_{hk}=Q_hH$, where
$H=1\oplus R_T^{1/2}$ is the indicated principal root. The two actual
corrected branches are $H^\dagger$ and $H$, each with conditional
probability $1/2$. In particular, on $\xi$ the polar unitary carries
the original phase $i$ from $Q_h$. Removing that phase separately
from the plane would change the protocol.

For the good relative,

$$
H_{g,T}=cI_T+i\frac{\sqrt3}{4}N_g
       =\frac{2}{\sqrt{13}}(I_T+L_g).
\tag{7.5}
$$

It is unitary and squares to $L_g$, with positive real part $cI_T$.
Its equal-weight residual channel on $T$ is
$c^2\operatorname{id}+(1-c^2)\operatorname{Ad}_{N_g}$ and its
line-plane multiplier is $cI_T$.

For the odd relative, put $z=\sqrt{1-\tau}$. Since
$L_o=b_oN_o+i\tau I_T$, its root is

$$
H_{o,T}=\frac{(1+i)rI_T+(1-i)zN_o}{2}.
\tag{7.6}
$$

The identities $r^2+z^2=2$ and $rz=b_o$ prove both unitarity and
$H_{o,T}^2=L_o$. Its real part $(rI_T+zN_o)/2$ is positive because
$r>z>0$. Its equal-weight residual channel on $T$ is
$(r^2/2)\operatorname{id}+(z^2/2)\operatorname{Ad}_{N_o}$; the
mixed terms cancel, since the product of its two coefficients has zero
real part. Its line-plane multiplier is $(rI_T+zN_o)/2$.

Each of the two pair cells in a partition has mass $2/8=1/4$ and the
four singleton masses sum to $1/2$. The two relatives within each
partition are identical. Hence its recovered channel is one half
identity plus one half of the corresponding conditional pair channel.
Combining those channels with probabilities $1-s,s$ gives exactly
(7.3)–(7.4). This combines actual channels before evaluating their
error; it does not average separately maximized seed errors. Every
decoder is CPTP and lifts by Convention 1.3 to a legal whole-$H$
decoder with the same encoded error. $\square$

**Corollary 7.3 (The good protocol's exact error).** The protocol $F_0$
has diamond error $3/16$, and it is also optimal among all CPTP decoders
on that fixed partition $\pi_g$.

Proof. Reuse actual-word Theorem 67.1 with the two good relatives of
Theorem 4.3: both have plane eigenvalues $e^{\pm i\theta}$ with
$\cos\theta=5/8>0$, conditional probabilities $1/2,1/2$, masses
$1/4,1/4$, and the same plane $T$. Its formula gives
$2(1/4)(1-5/8)=3/16$; each singleton has mass $1/8$ and zero
conditional deficit on its inverse channel. The polar decoder (7.5)
is the midpoint correction in that theorem. Equivalently, (7.4) on
a $T$-Bell input gives traceless-axis noise of mass $u_g=3/32$,
which is orthogonal to the target and has trace-distance contribution
$2u_g=3/16$. The common-plane theorem supplies the all-reference
upper bound and arbitrary-decoder optimality for this fixed partition.
This application is not a global lower bound over other partitions.
$\square$

## 8. A balanced seed weight with exact error

**Definition 8.1 (Balance constants).** Define

$$
\begin{aligned}
d_0&=u_g-a_g=\frac{c(1-c)}2,&
e_0&=a_o-u_o=\frac{r(r-1)}4,&d_1&=d_0+e_0,\\
s_0&=\frac{d_0}{d_1},&
k&=u_g-u_o=\frac{B_0}{4},&u_0&=u_g-ks_0,\\
H_0&=u_0-s_0/4,&\alpha_0&=2d_1-k-1/4.
\end{aligned}
\tag{8.1}
$$

All constants are exact radical expressions. In particular $u_0$ is
the value of $u$ at seed probability $s_0$; it is distinct from $u_g$.

**Theorem 8.2 (Positivity and exact base-protocol norm).** The constants
obey

$$
d_1>1/8,\quad 0<k<1/128,\quad 0<s_0<1/3,\quad
0<H_0<3/32,\quad \alpha_0>0,
\tag{8.2}
$$

and the legal base protocol has

$$
\|F_{s_0}-\operatorname{id}_3\|_\diamond=2u_0.
\tag{8.3}
$$

Proof. The radical bounds used in Theorem 5.3, together with
$r>77/60$, prove all signs analytically. For the latter bound, use
$\sqrt3>2329/1350$, whose square is less than three; then
$1+3\sqrt3/8>(77/60)^2$. Also $c>9/10$ and $c<1$, so
$0<d_0<9/200$. Meanwhile
$e_0>(77/60)(17/60)/4=1309/14400>9/100>2d_0$, proving
$s_0<1/3$. Expanding $d_1$ gives

$$
d_1=c/2-5/32+\tau/4-r/4>1/8
$$

using $c>9/10$, $\tau>5/8$ and $r<13/10$. The bounds on $k$
follow from $0<B_0<1/32$.
Now $u_0-s_0/4>0$ is equivalent to
$s_0<1/(1+\sqrt3)$; indeed
$u_0-s_0/4=(3/32)(1-s_0)-(\tau/4)s_0$.
Since $s_0<1/3<1/(1+\sqrt3)$ this proves $H_0>0$, while
$H_0<u_0<u_g=3/32$. Finally

$$
\alpha_0=c+\frac{(r-1)^2}{4}-\frac{29}{32}
>\frac9{10}+\frac{289}{14400}-\frac{29}{32}>0.
$$

At $s=s_0$, subtracting the affine expressions in (7.3) gives
$a-u=-d_0+d_1s_0=0$. Evaluate $w_g,w_o,\beta$ at this $s$ and
extend both axes by zero on $\xi$. The following residual Kraus
operators have effect $u_0I_3$:

$$
\begin{aligned}
R_o&=\sqrt{w_o}N_o+\frac{\beta}{\sqrt{w_o}}P,\\
R_g&=\sqrt{w_g}N_g,\\
R_\xi&=\sqrt{u_0-s_0/4}\,P.
\end{aligned}
\tag{8.4}
$$

Indeed $w_g+w_o=u_0$ on $T$, and
$\beta^2/w_o=s_0/4$ on the line. Checking the line, plane and two
coherence blocks in (7.4) gives

$$
F_{s_0}=(1-u_0)\operatorname{id}+
       \operatorname{Ad}_{R_o}+\operatorname{Ad}_{R_g}
                                 +\operatorname{Ad}_{R_\xi}.
$$

The residual divided by $u_0$ is CPTP. Thus the diamond error is at
most $2u_0$ for all finite references. For the normalized $T$-Bell
input $|\Omega_T\rangle=2^{-1/2}\sum_j|f_j\rangle|\bar f_j\rangle$,
both axis residual outputs are orthogonal to the target, because
$\operatorname{Tr}_TN_g=\operatorname{Tr}_TN_o=0$; $R_\xi$ kills
this input. Their positive output has total trace $u_0$ and is
supported orthogonally to the negative target term of trace $-u_0$.
The output difference therefore has trace norm $2u_0$, proving (8.3).
$\square$

## 9. A signed three-Kraus certificate and its matching purification

**Definition 9.1 (The refined probability and exact protocol value).**
With (8.1) set

$$
\begin{aligned}
x&=\frac{H_0k}{2d_1^2},& s_1&=s_0+x,& u_1&=u_0-kx,\\
D&=H_0+\alpha_0x,& h&=d_1x,&
t&=\frac{h^2}{D},\\
\delta&=2t=\frac{2d_1^2x^2}{H_0+\alpha_0x},&
\eta&=u_1+t,& U&=2\eta=2u_1+\delta.
\end{aligned}
\tag{9.1}
$$

The $h$ in (9.1) is a positive scalar, not a history label.

**Theorem 9.2 (Identity domination by three signed Kraus operators).**
The seed probability $s_1$ is strictly between zero and one. For
$w_g,w_o,\beta$ at $s=s_1$, define

$$
\begin{aligned}
L_1&=\sqrt t\,P_T+\frac{t-h}{\sqrt t}P,\\
L_2&=\sqrt{w_o}N_o+\frac{\beta}{\sqrt{w_o}}P,\\
L_3&=\sqrt{w_g}N_g.
\end{aligned}
\tag{9.2}
$$

They satisfy

$$
\sum_{j=1}^3L_j^\dagger L_j=\eta I_3,\qquad
F_{s_1}=(1-\eta)\operatorname{id}+\sum_{j=1}^3\operatorname{Ad}_{L_j}.
\tag{9.3}
$$

Here $0<\eta<1$, and the line coefficient $t-h$ is negative.
Consequently

$$
\|F_{s_1}-\operatorname{id}\|_\diamond\le U
<2u_0-\frac{H_0k^2}{2d_1^2}<2u_0.
\tag{9.4}
$$

Proof. From (8.2),
$0<x<(3/32)(1/128)/(2(1/8)^2)=3/128$, so
$0<s_1<1/3+3/128<1$. The affine formulas give

$$
a(s_1)-u_1=d_1x=h,\qquad
u_1+2h-s_1/4=H_0+(2d_1-k-1/4)x=D>0.
\tag{9.5}
$$

All square roots and divisions in (9.2) are therefore legal. Since
$D>H_0$,

$$
\delta=\frac{2d_1^2x^2}{D}
 <\frac{2d_1^2x^2}{H_0}=kx.
$$

It follows that $U=2u_0-2kx+\delta<2u_0-kx$, giving the strict
improvement in (9.4). Also $u_1>0$, since it is the convex combination
of the positive $u_g,u_o$ at $s_1$, so $0<\eta<u_0<3/32<1$.

On $T$, the effect in (9.3) is $(t+w_o+w_g)I_T=\eta I_T$.
On the line it is

$$
\frac{(t-h)^2}{t}+\frac{\beta^2}{w_o}
 =t-2h+\frac{h^2}{t}+\frac{s_1}{4}
 =t-2h+D+\frac{s_1}{4}=t+u_1.
$$

There are no line-plane effect terms. For the channel identity, the
plane block of the right side of (9.3) is the second line of (7.4).
Its line block is fixed by the just-proved effect identity. On
$|v\rangle\langle\xi|$ the scalar coefficient is
$1-\eta+(t-h)=1-u_1-h=1-a(s_1)$, and the other coefficient is
$\beta N_o$. This proves all blocks in (9.3).

Thus $E=\eta^{-1}\sum_j\operatorname{Ad}_{L_j}$ is CPTP, and
$F_{s_1}-\operatorname{id}=\eta(E-\operatorname{id})$ has diamond
norm at most $2\eta=U$ for every untouched finite reference. Finally
$t/h=h/D<d_1x/H_0=k/(2d_1)<1/32$, so $t-h<0$. Replacing this
coefficient by its absolute value would change the coherence identity
and invalidate the certificate. The signs and PSD assertions here
come from exact Kraus identities, rather than eigenvalue rounding.
$\square$

**Theorem 9.3 (Full-rank purification attaining exactly $U$).** Let
$z=\sqrt{1-\tau}$, $\gamma=15/\sqrt{481}$, and

$$
p_* =\frac{t}{h}=\frac hD,\qquad
\rho_* =p_*P+
  \frac{(1-p_*)I_T-
           p_*(N_o-\gamma N_g)/(z(1-\gamma^2))}{2}.
\tag{9.6}
$$

This is a full-rank qutrit density matrix. Its canonical purification
on a three-dimensional untouched reference attains

$$
\|F_{s_1}-\operatorname{id}_3\|_\diamond=U.
\tag{9.7}
$$

Proof. The positivity proof in Theorem 9.2 gave
$0<p_*<k/(2d_1)<1/32$. The traceless Hermitian matrix
$N_o-\gamma N_g$ squares to $(1-\gamma^2)I_T$, by the Pauli
anticommutator and (4.6). Its two eigenvalues are therefore
$\pm\sqrt{1-\gamma^2}$, where
$1-\gamma^2=256/481>1/2$. Also $z^2=1-\tau>1/4$.
The two plane eigenvalues of $\rho_*$ are

$$
\frac12\left(1-p_*\pm
                     \frac{p_*}{z\sqrt{1-\gamma^2}}\right).
$$

They are positive: the perturbation is less than $3p_*<3/32$, while
$1-p_*>31/32$. The line eigenvalue is $p_*>0$, and the trace is
$p_*+(1-p_*)=1$.

The exact expectation identities are

$$
\operatorname{Tr}(\rho_*N_g)=0,\qquad
\operatorname{Tr}(\rho_*N_o)=-p_*/z.
\tag{9.8}
$$

For example the first uses
$\operatorname{Tr}_T[(N_o-\gamma N_g)N_g]=0$; the second uses
$\operatorname{Tr}_T[(N_o-\gamma N_g)N_o]=2(1-\gamma^2)$.
Consequently the three signed residuals obey

$$
\begin{aligned}
\operatorname{Tr}(\rho_*L_1)&=(t-hp_*)/\sqrt t=0,\\
\operatorname{Tr}(\rho_*L_2)&=
    -\sqrt{w_o}\,p_*/z+\beta p_*/\sqrt{w_o}=0,\\
\operatorname{Tr}(\rho_*L_3)&=0.
\end{aligned}
\tag{9.9}
$$

Here the middle equality uses the actual common weights
$w_o=s_1z^2/4$ and $\beta=s_1z/4$, hence
$\beta/w_o=1/z$.

Let $|\psi_*\rangle=|\sqrt{\rho_*}\rangle\!\rangle$, whose
system marginal is $\rho_*$ and reference marginal is
$\rho_*^{\mathsf T}$. Each residual output vector
$(L_j\otimes I)|\psi_*\rangle$ is orthogonal to $|\psi_*\rangle$
by (9.9). Their positive sum has total trace $\eta$, by (9.3).
The output difference on this input is therefore the sum of a negative
target term $-\eta|\psi_*\rangle\langle\psi_*|$ and an orthogonally
supported positive term of trace $\eta$. Its trace norm is
$2\eta=U$. The all-reference upper bound in Theorem 9.2 proves the
matching equality (9.7). This is an exact norm of the displayed
protocol, not a matching global lower certificate. $\square$

## 10. The finite bracket, exact enclosures and remaining boundaries

**Theorem 10.1 (Strict finite operational bracket).** For the actual
instrument, original controller class, arbitrary full-$H$ system-only
CPTP decoders and averaged unhalved all-reference error,

$$
\boxed{L<\epsilon_{\rm op}(6,3)\le U},
\tag{10.1}
$$

where $L$ is (5.6) and $U$ is (9.1). Rational enclosures are

$$
\begin{aligned}
\frac{183388067293}{10^{12}}&<L<\frac{183388067294}{10^{12}},\\
\frac{183475875518}{10^{12}}&<U<\frac{183475875519}{10^{12}}.
\end{aligned}
\tag{10.2}
$$

Proof. The strict lower statement is Theorem 6.1. Theorem 9.3 gives a
legal channel of exact error $U$, so gives the global upper statement
after the full-space lift in Convention 1.3.

For a rational enclosure of the radicals, let $N=10^{30}$. The following
integers bound each indicated number strictly between their quotient by
$N$ and the quotient of their successor by $N$:

| Number | Lower numerator |
| --- | --- |
| $\sqrt3$ | $1732050807568877293527446341505$ |
| $\sqrt{13}$ | $3605551275463989293119221267470$ |
| $r=\sqrt{1+3\sqrt3/8}$ | $1284336035793720531030183271578$ |

The first two bounds follow by squaring the integer endpoints and
comparing with $3N^2$ and $13N^2$. For the third, square its endpoints
and compare to $1+3\sqrt3/8$ using the first row's rational bounds.
Apply outward rational interval operations to (5.6), (8.1) and (9.1),
using the positive denominators proved above: for products take the
minimum and maximum of the four endpoint products, and for a positive
interval $[a,b]$ use reciprocal interval $[1/b,1/a]$. The resulting
intervals lie strictly inside the two intervals in (10.2). These are
enclosures of algebraic expressions, not exact decimal optima or PSD
certificates. $\square$

**Corollary 10.2 (Memory consequences without integer-bit saving).** For
the unchanged operational memory function of Recovery Definition 2.4,

$$
0<\varepsilon\le L\ \Longrightarrow\ W_3(\varepsilon)\ge7,
\qquad
U\le\varepsilon<1/4\ \Longrightarrow\ W_3(\varepsilon)\le6.
$$

Proof. The first follows because no width-at-most-six controller has
error at most $L$; the second uses the refined legal width-six
protocol. These are statements about numbers of classical records.
Under integer-bit accounting,
$\lceil\log_2 6\rceil=\lceil\log_2 8\rceil=3$, so they do not
give an integer-bit saving. $\square$

**Proposition 10.3 (Boundaries of the finite result).** The results here
do not identify the global exact optimum, justify offline counting
below the last-transition range, or determine the unbounded joint
$(n,\varepsilon)$ random-history memory law or critical-pair energy.

Proof. The global common-tester support (3.1) still optimizes all 266
partitions and their arbitrary decoders, whereas (9.7) evaluates just
one selected mixture. The lower tester of §5 is strictly non-tight by
§6; it cannot be turned into a matching certificate by reporting more
decimal places. A sufficient missing step is an exact feasible averaged
channel and one common tester with equal objectives, including all
210 matching and 56 triple inequalities and analytically positive cell
support slacks. Restricting singleton channels, using known-word
inverses where a collision hides the word, or collapsing different axes
on the basis of equal spectra would instead change this optimization.

Online feasibility cannot in general be inferred from terminal alphabet
size alone: Recovery Proposition 43.3's three-bit majority assignment
has residual-function layer counts $1,2,3,2$, so terminal size two
does not imply peak two. The present protocols satisfy the larger
last-transition hypothesis and explicitly use layers $1,2,4,6$.
Nor can convexity select one successful seed: the norm of an averaged
channel can be strictly below the average of its component norms.
The identities (7.4) and (9.3) retain that average before evaluating
error. Finally the argument fixes $n=3$ throughout and supplies no
horizon-uniform estimates or critical-energy limit. Those questions
remain open. $\square$

## 11. Mathematical sources and correspondence

**Convention 11.1 (Repository sources).** The supplier statements used
here are the following ordinary mathematical sources, with their
published forms at revision
`3af20bcb7bd0189f7a4462a9e98bb91fccd20947` providing a fixed reference.
This volume's source-specific derivations are `repo-derived` ordinary
finite-dimensional mathematics, with no worldwide-priority, physical
realization, or Lean/kernel-certification claim.

| Source | Exact correspondence and use |
| --- | --- |
| [Recovery](AURIC_FIB_APPROXIMATE_ONLINE_RECOVERY_MEMORY.md), §§2–3 | The same $B$, measured operators, chronological $Q_h$, fair $1/8$ masses and encoded input/target; Lemma 3.1 and Theorem 3.2 supply $C$ and the two typed decoder conversions in Convention 1.3. |
| Recovery Theorem 13.1 | Equality of the complete averaged channel under independent finite-program replacement; used in Theorem 2.1 without derandomizing error. |
| Recovery Definition 18.1 and Theorem 18.2 | The same threshold-free attained operational minimum; attainment turns exclusion of equality at $L$ into a strict lower bound. |
| Recovery Theorem 43.2 | $n=3,W=6\ge2^{3-1}$, same free seed and full-space decoder class; legitimizes every partition in (2.1), with no eight-state intermediate layer. |
| [Actual-word](AURIC_FIB_ACTUAL_WORD_PURITY_ARITHMETIC.md), §66 | Output-first unnormalized Choi and common-tester convention at $d=3$; Theorem 3.1 extends its fixed-record minimax to the exact seed-convexified partition set. |
| Actual-word Theorem 67.1 | Two good pairs, common $T$, positive cosine $5/8$, conditional probabilities $1/2$, masses $1/4$; supplies the fixed-partition exact value $3/16$, rather than a global converse. |
| This volume, §§2–6 | Reversible 266-partition/85-block aggregation, actual signed Gram and axis correspondence, common full-rank survival support and strict all-controller lower certificate. |
| This volume, §§7–10 | Actual good/odd protocol combination, exact base error, signed residual identity and full-rank purification proving exact refined-protocol error $U$, with the strict global bracket. |

Choi positivity, finite-dimensional SDP duality, polar decomposition,
convex minimax and the affine-dependence argument behind the
Carathéodory bound are established methods. Their use does not itself
constitute new mathematics. The additional content is their exact
parameter and operation correspondence to this resource class, the
specific signed word identities, and the displayed certificates.

**Convention 11.2 (Unverified bibliographic leads).** The following
primary-source identifiers are bibliographic leads only. Their cited
versions and specific theorem attributions are unverified here and
non-loadbearing; no result above imports a theorem from them. In
particular their existence or an advisory description does not certify
that this operational problem has been solved elsewhere.

| Lead | Candidate relation and boundary |
| --- | --- |
| R1: Regula–Takagi–Gu, [arXiv:2102.07773v3](https://arxiv.org/abs/2102.07773v3) | Diamond-norm positive-Choi programs; a norm representation does not optimize the encoder partition. |
| R2: Jenčová, [arXiv:1512.07016v2](https://arxiv.org/abs/1512.07016v2) | Postprocessing comparison of fixed flagged channels; optimizing the flag and independent seed still requires (2.1)–(3.1). |
| R3: Bény–Oreshkov, [arXiv:0907.5391v4](https://arxiv.org/abs/0907.5391v4) | Worst-case channel fidelity is a different objective from the present unhalved diamond norm. |
| R4: Gregoratti–Werner, [quant-ph/0209025v1](https://arxiv.org/abs/quant-ph/0209025v1) | Fine environment-assisted correction does not grant access to the hidden member of a compressed collision cell. |
| R5: Datta–Renes–Renner–Wilde, [arXiv:1304.2336v2](https://arxiv.org/abs/1304.2336v2) | Source-dependent quantum compression and distortion criteria do not supply error derandomization for the averaged-channel objective here. |
| R6: Buscemi–Chiribella–D’Ariano, [quant-ph/0611070v1](https://arxiv.org/abs/quant-ph/0611070v1) | Shannon information about an environment is a different resource from the original online peak alphabet of six complete records. |

## 追加锚（本行以下为增补区）
