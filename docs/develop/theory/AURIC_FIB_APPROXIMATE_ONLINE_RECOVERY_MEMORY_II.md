# AURIC–FIB approximate online recovery memory II: exact six-record recovery at three steps

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

The finite question has the exact answer

$$
\epsilon_{\rm op}(6,3)
=E^*:=1-\left[\frac{r-c}{r-1+\sqrt2(1-c)}\right]^2,
\qquad
\tau=\frac{3\sqrt3}{8},\quad c=\frac{\sqrt{13}}4,\quad r=\sqrt{1+\tau}.
$$

Sections 11–14 prove this equality with one anisotropic common tester
covering every partition and arbitrary decoder, and a legal two-branch
protocol with matching all-reference error. Sections 5–10 supply useful
intermediate bounds and exact protocol norms. Within
$0<\varepsilon<1/4$, peak width at most six is possible exactly when
$`\varepsilon\ge E^*`$. The full unbounded joint memory law and
critical-pair energy remain open.

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
reduction here. The bound 29 alone does not establish optimality of two seeds; that
requires the matching certificates of §§11–14.
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
p_{\rm ref} =\frac{t}{h}=\frac hD,\qquad
\rho_{\rm ref} =p_{\rm ref}P+
  \frac{(1-p_{\rm ref})I_T-
           p_{\rm ref}(N_o-\gamma N_g)/(z(1-\gamma^2))}{2}.
\tag{9.6}
$$

This is a full-rank qutrit density matrix. Its canonical purification
on a three-dimensional untouched reference attains

$$
\|F_{s_1}-\operatorname{id}_3\|_\diamond=U.
\tag{9.7}
$$

Proof. The positivity proof in Theorem 9.2 gave
$0<p_{\rm ref}<k/(2d_1)<1/32$. The traceless Hermitian matrix
$N_o-\gamma N_g$ squares to $(1-\gamma^2)I_T$, by the Pauli
anticommutator and (4.6). Its two eigenvalues are therefore
$\pm\sqrt{1-\gamma^2}$, where
$1-\gamma^2=256/481>1/2$. Also $z^2=1-\tau>1/4$.
The two plane eigenvalues of $\rho_{\rm ref}$ are

$$
\frac12\left(1-p_{\rm ref}\pm
                     \frac{p_{\rm ref}}{z\sqrt{1-\gamma^2}}\right).
$$

They are positive: the perturbation is less than $3p_{\rm ref}<3/32$, while
$1-p_{\rm ref}>31/32$. The line eigenvalue is $p_{\rm ref}>0$, and the trace is
$p_{\rm ref}+(1-p_{\rm ref})=1$.

The exact expectation identities are

$$
\operatorname{Tr}(\rho_{\rm ref}N_g)=0,\qquad
\operatorname{Tr}(\rho_{\rm ref}N_o)=-p_{\rm ref}/z.
\tag{9.8}
$$

For example the first uses
$\operatorname{Tr}_T[(N_o-\gamma N_g)N_g]=0$; the second uses
$\operatorname{Tr}_T[(N_o-\gamma N_g)N_o]=2(1-\gamma^2)$.
Consequently the three signed residuals obey

$$
\begin{aligned}
\operatorname{Tr}(\rho_{\rm ref}L_1)&=(t-hp_{\rm ref})/\sqrt t=0,\\
\operatorname{Tr}(\rho_{\rm ref}L_2)&=
    -\sqrt{w_o}\,p_{\rm ref}/z+\beta p_{\rm ref}/\sqrt{w_o}=0,\\
\operatorname{Tr}(\rho_{\rm ref}L_3)&=0.
\end{aligned}
\tag{9.9}
$$

Here the middle equality uses the actual common weights
$w_o=s_1z^2/4$ and $\beta=s_1z/4$, hence
$\beta/w_o=1/z$.

Let $|\psi_{\rm ref}\rangle=|\sqrt{\rho_{\rm ref}}\rangle\!\rangle$, whose
system marginal is $\rho_{\rm ref}$ and reference marginal is
$\rho_{\rm ref}^{\mathsf T}$. Each residual output vector
$(L_j\otimes I)|\psi_{\rm ref}\rangle$ is orthogonal to $|\psi_{\rm ref}\rangle$
by (9.9). Their positive sum has total trace $\eta$, by (9.3).
The output difference on this input is therefore the sum of a negative
target term $-\eta|\psi_{\rm ref}\rangle\langle\psi_{\rm ref}|$ and an orthogonally
supported positive term of trace $\eta$. Its trace norm is
$2\eta=U$. The all-reference upper bound in Theorem 9.2 proves the
matching equality (9.7). This is an exact norm of the displayed
protocol, not a matching global lower certificate. $\square$

## 10. An intermediate finite bracket and exact enclosures

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

## 11. The anisotropic tester and the full distinguished-cell duals

**Definition 11.1 (Exact candidate and common input).** To distinguish
scalars from the plane matrix $A$ of Definition 4.1, use the starred
notation

$$
\begin{aligned}
b&=1-\tau,\qquad z=\sqrt b,\qquad rz=\sqrt{37}/8,\\
p&=\frac{r-\sqrt2c}{r-\sqrt2c+\sqrt2-1},\qquad q=1-p,\qquad v=2rp,\\
A^*&=p+cq=\frac{r-c}{r-1+\sqrt2(1-c)},\qquad
E^*=1-(A^*)^2,\qquad g=2(A^*)^2,\\
R&=(qI_T+vJ)/2,\qquad \rho=pP+R.
\end{aligned}
\tag{11.1}
$$

The vector coefficient $v$ in (11.1) is a scalar; it is distinct from
the encoded basis vector $v$ in Definition 1.1. Throughout §§11–15,
$p,q,v,R,\rho$ denote these fixed anisotropic quantities, rather than
the variable isotropic tester of §5. Put $N_{o,0}=N_o$ and
$N_{o,2}=8(v_2\cdot\sigma)/\sqrt{37}$ using (4.7). Explicitly,

$$
\begin{aligned}
N_g&=\frac{1}{2\sqrt{13}}
 \begin{pmatrix}0&3\sqrt3+5i\\3\sqrt3-5i&0\end{pmatrix},\\
N_{o,0}&=\frac{1}{2\sqrt{37}}
 \begin{pmatrix}8&5\sqrt3+3i\\5\sqrt3-3i&-8\end{pmatrix},\\
N_{o,2}&=\frac{1}{2\sqrt{37}}
 \begin{pmatrix}8&-5\sqrt3-3i\\-5\sqrt3+3i&-8\end{pmatrix}.
\end{aligned}
\tag{11.2}
$$

All three operators are extended by zero on $\xi$. These are the
actual axes in the fixed $(f_1,f_2)$ frame, with

$$
\frac12\operatorname{Tr}_T(JN_g)=0,\qquad
\frac12\operatorname{Tr}_T(JN_{o,0})
=\frac12\operatorname{Tr}_T(JN_{o,2})=-\frac4{\sqrt{37}}.
\tag{11.3}
$$

The two complementary axes are distinct; (11.3) asserts their common
projection, not their equality or an arbitrary rotation symmetry.

**Lemma 11.2 (Positivity, phases and balancing identities).** The
marginal $\rho$ is full rank, and

$$
0<p<1/32,\qquad t_v:=v/q<1/16,\qquad
p+rq=\sqrt2A^*,\qquad
\operatorname{Tr}(RN_g)=0,\qquad
\operatorname{Tr}(RN_{o,j})=-p/z\quad(j=0,2).
\tag{11.4}
$$

Its normalized canonical purification is

$$
|\psi_\rho\rangle=
 \sqrt p\,|\xi\xi\rangle+
 \sqrt{(q-v)/2}\,|f_1f_1\rangle+
 \sqrt{(q+v)/2}\,|f_2f_2\rangle.
\tag{11.5}
$$

For a good pair the principal root of its actual relative is

$$
H_g=P+cP_T+i\frac{\sqrt3}{4}N_g.
\tag{11.6}
$$

For each complementary pair the root is

$$
H_{o,j}=P+\frac{r(1+\epsilon_j i)}2P_T
                 +\frac{z(1-\epsilon_j i)}2N_{o,j},
\quad (j,\epsilon_j)=(0,+1)\ \text{or}\ (2,-1).
\tag{11.7}
$$

The first two complementary pairs in Theorem 4.2 use $j=0$; the last
two use $j=2$.

Proof. Since $r^2-2c^2=\tau-5/8$, positive-square comparisons give

$$
0<\tau-5/8<1/40,\quad r<9/7,\quad \sqrt2c>5/4,\quad
\sqrt2-1>41/100>2/5.
$$

Consequently

$$
\frac pq=\frac{\tau-5/8}{(r+\sqrt2c)(\sqrt2-1)}<1/40,
\qquad
\frac{2r}{r+\sqrt2c}<\frac{72}{71}<\frac{41}{40}.
$$

The first inequality implies $p<1/41<1/32$. The second, together
with $\tau-5/8<1/40$ and $\sqrt2-1>41/100$, gives
$t_v=2rp/q<1/16$. Thus $p,(q-v)/2,(q+v)/2$ are positive and
sum to one. Formula (11.5) follows because $J=\operatorname{diag}(-1,1)$.
The definition of $p$ is precisely
$p+rq=\sqrt2(p+cq)$. Equations (11.3), $v=2rp$ and
$rz=\sqrt{37}/8$ give the two moment identities in (11.4).

Equations (11.6)–(11.7) retain the spectator value one. On $T$,
$H_g^2=K_2K_0$ by $c^2-3/16=5/8$ and
$2c\sqrt3/4=\sqrt{39}/8$. On a complementary pair,

$$
H_{o,j}^2=rzN_{o,j}+\epsilon_j i\tau I_T.
$$

Indeed $r^2+z^2=2$ and $r^2-z^2=2\tau$; the cross coefficient
is $rz$. The same identities give unitarity. Their real parts on
$T$ are respectively $cI_T$ and $(rI_T+zN_{o,j})/2$, both positive
because $r>z>0$. Hence these are the principal roots of the ordered
relatives in Theorem 4.3, including their opposite imaginary-trace
signs. $\square$

**Theorem 11.3 (Exact full-CPTP support of the six distinguished
pairs).** With the output-first convention of §2 set

$$
W=|\rho\rangle\!\rangle\langle\!\langle\rho|,\qquad
f_\rho(F)=\sum_a|\operatorname{Tr}(\rho F_a)|^2,
\qquad
H_C=\sum_{h\in C}|\rho Q_h^\dagger\rangle\!\rangle
                      \langle\!\langle\rho Q_h^\dagger|.
\tag{11.8}
$$

Then $0\preceq W\preceq I_3\otimes\rho$, the identity score is one,
and $f_\rho$ is the survival probability of (11.5). For an arbitrary
qutrit CPTP decoder define

$$
S_C=\max_D\sum_{h\in C}f_\rho(D\operatorname{Ad}_{Q_h}).
$$

Every singleton has $S_C=1$. Each good or complementary pair has
$S_C=g$, with explicit full nine-dimensional Choi duals below.

Proof. The matrix $\rho$ is real diagonal in the specified frame.
Whitening $|\rho\rangle\!\rangle$ by $I\otimes\rho^{-1/2}$
gives squared norm $\operatorname{Tr}\rho=1$, proving tester
admissibility. Also
$\langle\!\langle\rho|F_a\rangle\!\rangle
=\operatorname{Tr}(\rho F_a)$, proving its survival interpretation.
For any Hermitian $B_C$,

$$
I_3\otimes B_C\succeq H_C
\quad\Longrightarrow\quad
S_C\le\operatorname{Tr}B_C,
\tag{11.9}
$$

because a CPTP decoder has positive Choi matrix with output partial
trace $I_3$. Thus (11.9) includes decoders that transfer population or
coherences between the line and plane.

For a pair $C=\{a,b\}$ put $V_C=Q_aH$, where $H$ is its root
(11.6) or (11.7), and change decoder coordinates to $D V_C$.
The two known corrected branches become $H^\dagger,H$. Define

$$
C_g=P+cP_T,\quad S_g=\frac{\sqrt3}{4}N_g,\qquad
D_o^{\rm op}=P+rP_T,\quad E_{o,j}^{\rm op}=P+zN_{o,j}.
$$

The corrected support matrices are exactly

$$
\begin{aligned}
H_g^{\rm corr}
 &=2|\rho C_g\rangle\!\rangle\langle\!\langle\rho C_g|
   +2|\rho S_g\rangle\!\rangle\langle\!\langle\rho S_g|,\\
H_{o,j}^{\rm corr}
 &=|\rho D_o^{\rm op}\rangle\!\rangle
                     \langle\!\langle\rho D_o^{\rm op}|
   +|\rho E_{o,j}^{\rm op}\rangle\!\rangle
                     \langle\!\langle\rho E_{o,j}^{\rm op}|.
\end{aligned}
\tag{11.10}
$$

For the second identity, the real and imaginary parts of (11.7) on
the full qutrit are $(D_o^{\rm op}+E_{o,j}^{\rm op})/2$ and
$\epsilon_j(D_o^{\rm op}-E_{o,j}^{\rm op})/2$. This explains both
the spectator term in $E_{o,j}^{\rm op}$ and the absence of a sign
change in its support.

Choose the positive $3\times3$ matrices

$$
B_g=(2A^*\rho C_g)^{\mathsf T},\qquad
B_o=((p+rq)\rho D_o^{\rm op})^{\mathsf T}.
\tag{11.11}
$$

In the ordered frame $(\xi,f_1,f_2)$ these are the actual diagonal
matrices

$$
\begin{aligned}
B_g&=\operatorname{diag}(2A^*p,A^*c(q-v),A^*c(q+v)),\\
B_o&=(p+rq)\operatorname{diag}(p,r(q-v)/2,r(q+v)/2).
\end{aligned}
\tag{11.12}
$$

Both traces equal $g$: the first is $`2A^*(p+cq)`$ and the second
is $(p+rq)^2$. To verify the full inequalities
$I_3\otimes B_g\succeq H_g^{\rm corr}$ and
$I_3\otimes B_o\succeq H_{o,j}^{\rm corr}$, whiten the two
support vectors by the indicated positive $9\times9$ matrix. For
$N$ a Hermitian unitary on $T$, write

$$
T_N=\operatorname{Tr}(R^{-1}NR^2N).
$$

Their two-vector Gram matrices are exactly

$$
\operatorname{diag}\left(1,\frac{3T_{N_g}}{16cA^*}\right),
\qquad
\operatorname{diag}\left(1,
             \frac{p+(b/r)T_{N_{o,j}}}{p+rq}\right).
\tag{11.13}
$$

For example the cross entries reduce to
$\operatorname{Tr}(\rho S_g)=0$ and
$\operatorname{Tr}(\rho E_{o,j}^{\rm op})
=p-4zv/\sqrt{37}=0$. The leading entries are one by
$\operatorname{Tr}(\rho C_g)=A^*$ and
$\operatorname{Tr}(\rho D_o^{\rm op})=p+rq$.
Direct $2\times2$ multiplication also gives

$$
T_{N_g}=\frac{q(q^2+3v^2)}{q^2-v^2},\qquad
T_{N_{o,j}}=\frac{q(37q^2+47v^2)}{37(q^2-v^2)}.
\tag{11.14}
$$

Alternatively, for either axis and indeed any such $N$,

$$
T_N\le\|R^{-1}\|\operatorname{Tr}R^2
=\frac{q(1+t_v^2)}{1-t_v}<2q.
$$

Thus the second good Gram eigenvalue is strictly less than
$3q/(8cA^*)\le6/13<1$. The second complementary eigenvalue is
strictly less than one because $2b<r^2$. A whitened sum of two
rank-one matrices is bounded by identity exactly when this two-vector
Gram is; this proves the PSD slacks on all nine dimensions.

Identity decoding in corrected coordinates attains the traces in
(11.11). Its two good traces are $A^*,A^*$; for a complementary
pair they are $(p+rq)(1+\epsilon_j i)/2$ and its conjugate, since
$\operatorname{Tr}(\rho E_{o,j}^{\rm op})=0$. Their squared
moduli sum to $g$. Hence these support bounds are exact.
In original decoder coordinates the dual is

$$
B_C=\overline{V_C}B_g V_C^{\mathsf T}
\quad\text{or}\quad
B_C=\overline{V_C}B_o V_C^{\mathsf T}.
\tag{11.15}
$$

Indeed right multiplication of a vectorized matrix by $V_C^\dagger$
acts as $I\otimes\overline{V_C}$, so (11.15) preserves the full
PSD inequality and trace.

For a singleton the corrected support is $W$, its dual is
$\rho^{\mathsf T}=\rho$, and its original dual is
$\overline{Q_h}\rho^{\mathsf T}Q_h^{\mathsf T}$. This proves
score at most one for unrestricted singleton decoders; its inverse
unitary attains one. $\square$

## 12. Uniform full-Choi supports for all remaining pairs and triples

**Lemma 12.1 (An explicit dual from a weighted plane Gram bound).** For
any cell of size $m$ define

$$
\lambda_C=\lambda_{\max}
 \left([\operatorname{Tr}(R^2G_h^\dagger G_k)]_{h,k\in C}\right).
$$

If $\lambda_C\le\Lambda$ with $\Lambda>0$, put
$a_C=\sqrt m\,p$, $d_C=\sqrt{2\Lambda}$ and

$$
B_C=(a_C+d_C)\left(a_CP+\frac{d_C}{2}P_T\right).
\tag{12.1}
$$

Then $I_3\otimes B_C\succeq H_C$ on the full Choi space and

$$
S_C\le\operatorname{Tr}B_C
       =(\sqrt m\,p+\sqrt{2\Lambda})^2.
\tag{12.2}
$$

Proof. Each vector $|\rho Q_h^\dagger\rangle\!\rangle$ is the
orthogonal sum of its spectator component and its plane component.
The spectator-vector Gram has norm $mp^2$. The literal plane-vector
Gram is the transpose of the matrix defining $\lambda_C$; transpose
does not change its eigenvalues. Whitening by $I_3\otimes B_C$
therefore gives a Gram norm bounded by

$$
\frac{mp^2}{(a_C+d_C)a_C}
+\frac{\Lambda}{(a_C+d_C)d_C/2}
=\frac{a_C+d_C}{a_C+d_C}=1.
$$

The positive matrices in (12.1) are invertible since $p>0$ and
$\Lambda>0$. The rank-one Gram criterion used in Theorem 11.3 now
proves the full PSD inequality, and (11.9) gives (12.2). No
block-preserving restriction is imposed on the decoder. $\square$

**Theorem 12.2 (All other pair supports are strictly smaller).** Every
pair outside the two good and four complementary pairs has $S_C<g$.

Proof. Put

$$
a_2=\operatorname{Tr}R^2=(q^2+v^2)/2,\qquad
\mu=\frac{qv}{a_2}=\frac{2t_v}{1+t_v^2}
                <\frac{32}{257}<\frac18.
\tag{12.3}
$$

Multiplying plane words by scalar phases does not change the spectrum
of their weighted Gram. Make their relatives $SU(2)$, writing an
ordinary relative as $\kappa I+i\ell\cdot\sigma$, where
$\kappa^2+|\ell|^2=1$. The signed table in Theorem 4.2 gives
$|\kappa|\le1/2$ for each remaining pair. Its normalized weighted
overlap has the form
$\kappa+i\mu\,n_0\cdot\ell$, so

$$
\begin{aligned}
\lambda_C
 &\le a_2\left[1+
       \sqrt{\kappa^2+\mu^2(1-\kappa^2)}\right]\\
 &\le a_2\left[1+\sqrt{1/4+3\mu^2/4}\right]
 <\frac{25}{16}a_2
 <\frac{6425}{8192}q^2<\frac{13}{16}q^2.
\end{aligned}
\tag{12.4}
$$

Here $\sqrt{1/4+3/256}=\sqrt{67}/16<9/16$ and
$a_2<(257/512)q^2$ by $t_v<1/16$. Apply (12.1) with
$m=2$, $\Lambda=(13/16)q^2$. Its trace is

$$
[\sqrt2p+\sqrt{13/8}\,q]^2
=2[p+cq]^2=g.
$$

To retain strictness, the strict bound on $\lambda_C$ in (12.4)
allows a strictly smaller positive $\Lambda$; (12.2) then gives
$S_C<g$. Thus this is a strict support exclusion, including leakage
decoders, for all 22 remaining pairs. $\square$

**Theorem 12.3 (All 56 triple supports).** Every triple has

$$
S_C\le T_3:=
 [\sqrt3p+\sqrt{(17/8)(q^2+v^2)}]^2<2g-1.
\tag{12.5}
$$

Proof. It suffices to bound its weighted Gram eigenvalue by
$(17/8)a_2$. The following classification exhausts the 56 triples.

| Parity and complementary edges | Count | Unweighted overlap structure |
| --- | --- | --- |
| Mixed parity, no complementary edge | $24$ | One nonzero edge, magnitude at most $5/8$ |
| Mixed parity, one complementary edge | $24$ | Two nonzero edges, magnitudes $\tau$ and at most $5/8$ |
| Same parity | $8$ | Three real edges $-1/2,-1/2,d$, with $d=5/8$ in four triples and $d=-1/8$ in four |

There are $2\binom43=8$ same-parity triples. Of the other 48,
exactly $4\cdot6=24$ contain a complementary edge; the four
complementary edges are disjoint, so no triple contains two. A
mixed-parity triple has one same-parity edge of Hamming distance two.
Its opposite-parity edges have distance one or three, giving exactly
the first two rows by Theorem 4.2. Within each four-vertex parity
class, the two outer-bit edges have values $5/8$ and $-1/8$;
every triple contains one of them and two adjacent-position edges
of value $-1/2$. Each outer edge occurs twice, giving the final row.

For the mixed rows, remove the common left factor $A^3$ in (4.1)
and multiply odd-parity $R_h$ by $-i$ to obtain $SU(2)$ words.
The unweighted normalized Gram becomes a real symmetric matrix $M_0$.
The weighted normalized matrix is

$$
M=M_0+i\mu B,
\tag{12.6}
$$

where $B$ is real skew-symmetric and each of its three independent
entries is a component $n_0\cdot\ell$ of an $SU(2)$ relative,
so has absolute value at most one. A real skew $3\times3$ matrix
has norm equal to the Euclidean norm of these three entries, hence
$\|B\|\le\sqrt3$.
The first two rows' unweighted largest eigenvalues are at most
$1+5/8$ and $1+\sqrt{\tau^2+25/64}=1+c$, respectively.
Consequently all 48 mixed-parity triples obey

$$
\lambda_C/a_2\le1+c+\mu\sqrt3
 <1+\frac{29}{32}+\frac{56}{257}<\frac{17}{8}.
\tag{12.7}
$$

The strict rational comparisons use $c<29/32$, $\sqrt3<7/4$
and (12.3); they follow by squaring positive quantities.

For each same-parity triple, precisely one edge differs in positions
$h_2,h_3$. Its weighted imaginary part is $\pm\mu\tau$;
the other two edges have no imaginary part. To check this directly,
the former relative is $K_2K_1$ or its conjugate by $K_0$, whose
Pauli vector has $n_0$ component of magnitude $\tau$ by (4.3).
The other relatives have the form $KK_0$ or $K_0K$, whose vector
is perpendicular to $n_0$. Up to a simultaneous permutation of rows
and columns the actual normalized matrix is therefore

$$
M=\begin{pmatrix}
1&-1/2+i\epsilon\mu\tau&-1/2\\
-1/2-i\epsilon\mu\tau&1&d\\
-1/2&d&1
\end{pmatrix},\qquad \epsilon\in\{+1,-1\}.
\tag{12.8}
$$

The matrix $(17/8)I-M$ has diagonal $9/8$. Its two-by-two principal
minors are $(9/8)^2-1/4$, $(9/8)^2-1/4-\mu^2\tau^2$ and
$(9/8)^2-d^2$, all positive for $\mu<1/8$. Its determinant is

$$
\det((17/8)I-M)=
\begin{cases}
(56-243\mu^2)/512,&d=5/8,\\
(464-243\mu^2)/512,&d=-1/8.
\end{cases}
\tag{12.9}
$$

For example expand
$(9/8)^3-(9/8)(1/2+d^2+\mu^2\tau^2)-d/2$
and use $\tau^2=27/64$. Both determinants are positive for
$\mu<1/8$. Positive principal minors prove the full Hermitian
matrix is positive definite, covering all eight same-parity triples.
Together with (12.7), this proves $\lambda_C\le(17/8)a_2$ for
every triple. Lemma 12.1 supplies its actual full-Choi dual (12.1)
with $m=3$ and $\Lambda=(17/16)(q^2+v^2)$.

Finally,

$$
\frac{17}{8}\frac{257}{256}<\left(\frac{47}{32}\right)^2,
\qquad
\sqrt{T_3}<2p+\frac{47}{32}q
 <\frac{1521}{1024}<\frac32.
$$

The first comparison is $4369/2048<4418/2048$, and the second
uses $p<1/32$ and $\sqrt3<2$. Since $`A^*=p+cq\ge c`$,
$g\ge2c^2=13/8$. Thus $T_3<9/4\le2g-1$, as required.
$\square$

## 13. The common lower certificate for every online controller

**Theorem 13.1 (Global anisotropic lower bound).** Every channel in the
original operational class has unhalved diamond error at least
$`E^*=1-(A^*)^2`$.

Proof. Use the single input and measurement (11.5), (11.8) for every
partition in (2.1). For a two-pair partition, unrestricted singleton
support is at most four and pair support at most $2g$, by Theorems
11.3 and 12.2. For a triple partition, Theorem 12.3 gives total
support at most $5+T_3<4+2g$. Thus all 210 and 56 partition
inequalities in Theorem 3.1 hold with

$$
z_0=\frac{4+2g}{8}=\frac{1+(A^*)^2}{2}.
\tag{13.1}
$$

These inequalities have explicit $9\times9$ PSD slacks: (11.11),
(11.15) for the six distinguished pairs, (12.1) for all other pairs
and triples, and the singleton dual following (11.15). They bound
all cell decoders simultaneously, including arbitrary nonunitary
singleton maps and maps with line-plane leakage.

Theorem 2.1 already includes every stochastic online controller and
arbitrary input- and history-independent shared seed permitted by
Definition 1.2. Refinement duplicates decoders on split cells, and
finite-program replacement preserves the entire averaged channel.
Since $f_\rho$ is one fixed linear functional of that channel,
convexification preserves $f_\rho(F)\le z_0$. It is not a minimum
over separately chosen partition errors.

The survival measurement on (11.5) then gives

$$
\|F-\operatorname{id}_3\|_\diamond
\ge\|(F\otimes\operatorname{id})(|\psi_\rho\rangle
       \langle\psi_\rho|)-|\psi_\rho\rangle\langle\psi_\rho|\|_1
\ge2[1-f_\rho(F)]\ge E^*.
\tag{13.2}
$$

The middle inequality is the two-outcome measurement bound for a
trace-zero difference. Its factor two is the unhalved convention.
For an arbitrary full-$H$ decoder, compose its averaged encoded channel
with $C$ as in Convention 1.3. Complete trace-norm contraction yields

$$
\|\mathcal E-\iota\|_\diamond
\ge\|C\mathcal E-\operatorname{id}_3\|_\diamond\ge E^*.
$$

The input remains the encoded qutrit and the reference is untouched;
no assertion about arbitrary unencoded $H$ input is used. $\square$

## 14. A legal matching channel and its all-reference norm

**Definition 14.1 (Optimal seed probability).** Retain the actual
partitions and polar decoders of Definition 7.1, with the principal
roots (11.6) and (11.7). Set

$$
\begin{aligned}
D_g&=(1-c)^2/2,\qquad D_o=(r-1)^2/4,\qquad
\alpha=D_o-D_g=\alpha_0,\\
D(s)&=(1-s)D_g+sD_o,\qquad h(s)=a(s)-u(s)=-d_0+d_1s,\\
s^*&=\frac{d_0+pD_g}{d_1-p\alpha},\qquad
F^*=F_{s^*}.
\end{aligned}
\tag{14.1}
$$

Here $D_o$ is a positive scalar, distinct from the operator
$D_o^{\rm op}$ in §11. In (14.1) and below, $u(s),a(s)$ are
exactly the averaged coefficients in (7.3).

**Lemma 14.2 (Scalar balance and legal probability).** The constants
satisfy

$$
\begin{aligned}
D(s)&=u(s)+2h(s)-s/4>0\quad(0\le s\le1),\\
k&=2d_1p-\alpha p^2,\qquad \alpha>0,\\
0&<s^*<1,\qquad h(s^*)=pD(s^*).
\end{aligned}
\tag{14.2}
$$

Proof. On the good branch,
$u_g+2(a_g-u_g)=D_g$, using $c^2=13/16$. On the odd branch,
$u_o+2(a_o-u_o)-1/4=D_o$, using $r^2=1+\tau$.
Affinity proves the first identity, and $D_g,D_o>0$ prove positivity.
Its slope is $2d_1-k-1/4=\alpha$, agreeing with (8.1);
Theorem 8.2 proves $\alpha>0$.

The balance relation follows by expanding
$(p+rq)^2=2(p+cq)^2$. More explicitly,

$$
\begin{aligned}
k-2d_1p+\alpha p^2
 &=kq^2+\frac{r-2c}{2}pq-\frac14p^2\\
 &=\frac{(p+rq)^2-2(p+cq)^2}{4}=0,
\end{aligned}
$$

where $k=(\tau-5/8)/4$ and
$d_1=c/2-5/32+\tau/4-r/4$.
The numerator of $`s^*`$ is positive. Its denominator minus that
numerator equals

$$
e_0-pD_o=\frac{(r-1)[r-p(r-1)]}{4}>0,
\tag{14.3}
$$

since $p<1$. Hence the denominator is positive and $`s^*`$ lies
strictly between zero and one. Solving
$-d_0+d_1s=p(D_g+\alpha s)$ gives the stated balance at $`s^*`$.
$\square$

**Theorem 14.3 (Signed residual certificate and exact global value).**
The original operational minimum is

$$
\boxed{\epsilon_{\rm op}(6,3)=E^*
=1-\left[\frac{r-c}{r-1+\sqrt2(1-c)}\right]^2}.
\tag{14.4}
$$

It is attained by $`F^*`$ with its legal independent two-branch seed.
The exact error is the unhalved diamond norm over every finite
untouched reference, also after lifting to the encoded full-$H$ problem.

Proof. Theorem 7.2 gives the complete actual channel, with plane block
and spectator multiplier

$$
\begin{aligned}
F^*|_{M(T)}&=(1-u)\operatorname{id}
                 +(1-s^*)u_g\operatorname{Ad}_{N_g}
                 +s^*u_o\operatorname{Ad}_{N_{o,0}},\\
\text{line-plane multiplier}&=(1-a)I_T+\frac{s^*z}{4}N_{o,0}.
\end{aligned}
\tag{14.5}
$$

All coefficients here are evaluated after averaging the actual
channels. Put $D=D(s^*)$, $u=u(s^*)$, $\eta=u+p^2D$, and

$$
\begin{aligned}
L_1&=\sqrt D\,(pP_T-qP),\\
L_2&=\frac{\sqrt{s^*}}2(P+zN_{o,0}),\\
L_3&=\sqrt{(1-s^*)3/32}\,N_g.
\end{aligned}
\tag{14.6}
$$

The spectator coefficient of $L_1$ is $-q\sqrt D<0$. On the plane,
the sum of their effects is
$[p^2D+s^*b/4+(1-s^*)3/32]I_T=\eta I_T$.
On the line it is $Dq^2+s^*/4$. The identities (14.2) give

$$
Dq^2+s^*/4
=D(1-2p+p^2)+s^*/4=u+p^2D=\eta.
$$

Thus there are no cross-effect terms and

$$
\sum_jL_j^\dagger L_j=\eta I_3.
\tag{14.7}
$$

The channel identity on all nine matrix units is

$$
F^*=(1-\eta)\operatorname{id}_3+\sum_{j=1}^3\operatorname{Ad}_{L_j}.
\tag{14.8}
$$

Indeed on $M(T)$ the identity coefficient is
$1-\eta+p^2D=1-u$, and the other coefficients are exactly those
in (14.5). On $P$ the coefficient is $1-\eta+Dq^2+s^*/4=1$.
On $|x\rangle\langle\xi|$, $x\in T$, it is

$$
[1-\eta-pqD]x+\frac{s^*z}{4}N_{o,0}x
=[1-u-pD]x+\frac{s^*z}{4}N_{o,0}x
=[1-a]x+\frac{s^*z}{4}N_{o,0}x.
$$

The reverse coherence block follows by adjoint and complex linearity.
This proves (14.8) on the line, four plane units and both pairs of
coherence units. Replacing the negative spectator coefficient in
(14.6) by its absolute value would invalidate this identity.

All three residual moments against the common input vanish:

$$
\begin{aligned}
\operatorname{Tr}(\rho L_1)&=\sqrt D(pq-qp)=0,\\
\operatorname{Tr}(\rho L_2)&=\frac{\sqrt{s^*}}2
                    [p+z\operatorname{Tr}(RN_{o,0})]=0,\\
\operatorname{Tr}(\rho L_3)&=0.
\end{aligned}
\tag{14.9}
$$

On $|\psi_\rho\rangle$ the positive residual output in (14.8)
is therefore orthogonal to the target and has trace $\eta$, by
(14.7). The difference has trace norm exactly $2\eta$.
For the matching upper bound, let
$\mathcal R=\eta^{-1}\sum_j\operatorname{Ad}_{L_j}$. It is CPTP
and $\eta>0$. Complete trace-norm contractivity gives
$\|\mathcal R\|_\diamond=\|\operatorname{id}_3\|_\diamond=1$,
so for every finite untouched reference, and arbitrary operators in
the diamond-norm definition,

$$
\|F^*-\operatorname{id}_3\|_\diamond
=\eta\|\mathcal R-\operatorname{id}_3\|_\diamond\le2\eta.
\tag{14.10}
$$

It remains to identify this exact protocol norm with the common lower
bound. Its four singleton contributions have score four. In either
branch the two actual pair corrections attain $g$ by Theorem 11.3.
Consequently

$$
f_\rho(F^*)=\frac{4+2g}{8}=\frac{1+(A^*)^2}{2}.
$$

Equations (14.8)–(14.9) also give $f_\rho(F^*)=1-\eta$.
Thus $2\eta=1-(A^*)^2=E^*$, with $0<\eta<1$. This proves
both all-reference norm equality and the matching value in (14.4),
using Theorem 13.1 for the all-controller lower bound.

Operationally, the seed chooses the two complete partitions (7.1)
with probabilities $1-s^*,s^*$. Retaining prefixes through time two
and transitioning directly into their six cells uses the actual layer
widths $1,2,4,6$. The pair decoder is
$\operatorname{Ad}_{H^\dagger Q_a^\dagger}$ and a singleton uses
$\operatorname{Ad}_{Q_h^\dagger}$; these depend only on the retained
cell, horizon and independent seed. The fixed pair polar unitary is
$Q_aH$, not an inverse selected using the hidden member of the pair.
Each qutrit decoder lifts as $\iota D C$, and Convention 1.3 gives

$$
\|\iota F^*-\iota\|_\diamond
=\|F^*-\operatorname{id}_3\|_\diamond=E^*.
$$

This exact lift and the contraction in Theorem 13.1 cover arbitrary
system-only full-$H$ decoders in both directions, with encoded input
and target fixed. $\square$

## 15. The family equality condition, strict improvement and threshold

**Theorem 15.1 (General family norm identity and unique fixed-family
minimizer).** For $s\in[0,1]$ put
$p_s=h(s)/D(s)$, $q_s=1-p_s$. If

$$
p_s\ge0,\qquad 2rp_s\le1-p_s,
\tag{15.1}
$$

then

$$
\|F_s-\operatorname{id}_3\|_\diamond
=2\left[u(s)+\frac{h(s)^2}{D(s)}\right]
=E^*+2D(s)(p_s-p)^2.
\tag{15.2}
$$

The unique minimizing seed weight in the entire fixed family
$\{F_s:0\le s\le1\}$ is $`s^*`$. This uniqueness concerns the
specified two partitions and their polar/inverse decoders, rather than
all protocols attaining the global value.

Proof. For a weight satisfying (15.1), use

$$
\begin{aligned}
\rho_s&=p_sP+[(1-p_s)I_T+2rp_sJ]/2,\\
L_{1,s}&=\sqrt{D(s)}[p_sP_T-(1-p_s)P],\\
L_{2,s}&=\sqrt s(P+zN_{o,0})/2,\qquad
L_{3,s}=\sqrt{(1-s)3/32}\,N_g,\\
\eta_s&=u(s)+p_s^2D(s).
\end{aligned}
\tag{15.3}
$$

The condition (15.1) states exactly the required nonnegativity of the
line weight and both plane eigenvalues of $\rho_s$; its trace is one.
The effect, block and zero-moment calculations (14.7)–(14.9) apply
with $p_s,q_s$ because $h(s)=p_sD(s)$. They require no inverse of
$\rho_s$, so also cover equality in (15.1). In particular the
spectator coefficient remains negative, since
$p_s\le1/(1+2r)<1$. The canonical purification gives output trace
norm $2\eta_s$, and the residual channel gives the upper bound for
all finite references. This proves the first equality in (15.2).

For the second, $u(s)+2ph(s)-p^2D(s)$ is affine in $s$ with
slope $-k+2pd_1-p^2\alpha=0$ by (14.2). Its value at $`s^*`$
is $E^*/2$ by Theorem 14.3. Completing the square gives

$$
u(s)+\frac{h(s)^2}{D(s)}-\frac{E^*}{2}
=D(s)\left(\frac{h(s)}{D(s)}-p\right)^2.
\tag{15.4}
$$

At $`s^*`$ the inequalities in (15.1) are strict by Lemma 11.2.
They remain strict on an open interval about that weight. Moreover
for $s_2>s_1$ in $[0,1]$,

$$
p_{s_2}-p_{s_1}
=\frac{(d_1D_g+\alpha d_0)(s_2-s_1)}{D(s_2)D(s_1)}>0.
\tag{15.5}
$$

Thus (15.4) is strictly positive in that neighborhood except at
$`s^*`$. On the whole interval, the map $s\mapsto F_s$ is affine
and $s\mapsto\|F_s-\operatorname{id}_3\|_\diamond$ is convex.
Another minimizing weight would force equality on the entire segment
to $`s^*`$, contradicting the strict local inequality. This proves
uniqueness throughout the fixed family without assuming an endpoint
norm formula or deducing uniqueness just from a matching global value.
$\square$

**Corollary 15.2 (Strict exact improvement over the refined value).**
The value $U$ of (9.1) is the exact norm of its protocol and satisfies

$$
L<E^*<U,\qquad
U-E^*=2D(s_1)(p_1-p)^2>0,
\qquad
p_1=\frac{kd_1}{2d_1^2+\alpha k}.
\tag{15.6}
$$

Proof. Since $s_1=s_0+H_0k/(2d_1^2)$,
$h(s_1)=d_1x$ and $D(s_1)=H_0+\alpha x$, giving the stated
$p_1$. The positive constants in (8.2) and (14.2) give

$$
0<p_1<\frac{k}{2d_1}<p.
$$

The last strict inequality follows from
$k=2d_1p-\alpha p^2$ with $\alpha>0$. Thus
$2rp_1<2rp<1-p<1-p_1$, so (15.1) holds strictly at $s_1$.
Formula (15.2) applies and its first expression is exactly (9.1)'s
$U$. Formula (15.4) proves the strictly positive factor in (15.6).
This is exact sign evidence, independent of a rounded decimal gap.
The strict lower comparison follows from Theorem 6.1 and (14.4).
$\square$

**Corollary 15.3 (Exact finite threshold and record cost).** In the
original range $0<\varepsilon<1/4$, a legal protocol of peak width
at most six and error at most $\varepsilon$ exists if and only if
$`\varepsilon\ge E^*`$. In particular,

$$
0<\varepsilon<E^*\ \Longrightarrow\ W_3(\varepsilon)\ge7,
\qquad
E^*\le\varepsilon<1/4\ \Longrightarrow\ W_3(\varepsilon)\le6.
\tag{15.7}
$$

Proof. Theorem 13.1 excludes every such protocol below $E^*$;
Theorem 14.3 attains the endpoint and hence every larger error
allowance. The full record convention is unchanged. Under integer-bit
accounting, six and eight records both cost three bits:
$\lceil\log_2 6\rceil=\lceil\log_2 8\rceil=3$. $\square$

**Corollary 15.4 (Rational enclosures of the exact value and gap).**

$$
\begin{aligned}
\frac{183475875370782602}{10^{18}}
 &<E^*<\frac{183475875370782603}{10^{18}},\\
\frac{148012572}{10^{18}}
 &<U-E^*<\frac{148012573}{10^{18}}.
\end{aligned}
\tag{15.8}
$$

For orientation, $`E^*\approx0.183475875370782602048620`$.

Proof. Use the positive radical formulas (11.1), (14.1) and (9.1).
The outward rational interval procedure of Theorem 10.1, with
$N=10^{90}$ and integer-square-root endpoints for each positive
radical, gives intervals strictly inside (15.8). All denominators
have the positive lower bounds proved above. For the gap use the
exact nonnegative expression (15.6), whose nonzero factor has already
been proved, rather than subtracting displayed decimal approximations.
The inequalities in (15.8) enclose scalar algebraic expressions; PSD
and norm equality follow from the displayed analytic certificates.
$\square$

## 16. Residual boundaries of the exact finite result

**Proposition 16.1 (Scope beyond the finite threshold).** The exact
value (14.4) does not determine the whole $W_3$ curve, justify offline
counting below the last-transition range, or determine the unbounded
joint $(n,\varepsilon)$ random-history memory law or critical-pair
energy. Physical realization and literature priority are unresolved.

Proof. The lower certificate optimizes the original peak-six class,
and the matching channel attains that class's minimum. This settles
precisely the existence threshold in (15.7). It does not optimize all
other width classes, so does not determine every value of $W_3$.
Online feasibility cannot in general be inferred from terminal
alphabet size alone: Recovery Proposition 43.3's three-bit majority
assignment has residual-function layer counts $1,2,3,2$, so terminal
size two does not imply peak two. The present protocols explicitly
satisfy the last-transition hypothesis with layers $1,2,4,6$.

Nor does convexity select one successful seed: the norm of an averaged
channel can be below the average of its component norms. The identities
(7.4) and (14.8) retain the actual average before evaluating error.
The only covariance used is the commuting phase action of Theorem
3.2; no arbitrary $SU(2)$ twirl or replacement of the two actual
complementary axes is justified. The whole-$H$ correspondence always
keeps the encoded qutrit input and target, rather than changing to an
arbitrary-$H$ input problem.

Finally the proof fixes horizon three and provides no horizon-uniform
joint memory estimate or critical-energy limit. Its channels and
record accounting are mathematical constructions in the stated model;
no physical implementation, integer-bit saving, Lean/kernel
verification or worldwide originality certificate follows. Those
extensions require their own evidence. $\square$

## 17. Mathematical sources and correspondence

**Convention 17.1 (Repository sources).** The supplier statements used
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
| This volume, §§7–10 | Actual good/odd protocol combination, exact base error, signed residual identity and full-rank purification proving exact refined-protocol error $U$, and the intermediate strict global bracket. |
| This volume, §§11–13 | Actual common projection of both complementary axes, positive anisotropic marginal, full nine-dimensional cell duals, uniform weighted pair/triple bounds and the all-266-partition lower certificate. |
| This volume, §§14–15 | Legal seed weight, signed residual effect and channel identities, all-reference matching norm, exact global value, strict improvement over $U$, unique optimum in the fixed family and the exact peak-six threshold. |
| This volume, §16 | Remaining width-curve, unbounded-law, critical-energy, physical-realization and priority boundaries. |

Choi positivity, finite-dimensional SDP duality, polar decomposition,
convex minimax and the affine-dependence argument behind the
Carathéodory bound are established methods. Their use does not itself
constitute new mathematics. The additional content is their exact
parameter and operation correspondence to this resource class, the
specific signed word identities, and the displayed certificates.

**Convention 17.2 (Unverified bibliographic leads).** The following
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
