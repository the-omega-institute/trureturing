# Native joint transfer–coherence interface geometry

> This reference volume gives ordinary conditional mathematics, without Lean
> kernel verification. Its coefficient and interface applications are
> `repo-derived`; the generic positive-matrix, factor-width-two and
> quantum-operation structures used in their proofs are mature mathematics.
> The append convention is `generic-v1`: corrections and extensions belong
> after the final append anchor once the preceding text is admitted.

## 1. The original experiment and the joint question

**Convention 1.1 (scope).** All comparisons use the common-channel,
normalized reached-cut experiment of [Complete Continuation Gap][CG],
Definitions 2.3, 3.1, 3.2 and 4.2. The finite comparison test is CG.155;
its contraction is a necessary test of the original complete output.
The zero-transfer results of [Explicit Zero-Transfer Loss][ZG] and the
quantitative results CG26–28 are inherited results. The additional
application here characterizes their simultaneous live restriction by
finite coefficient inequalities, and distinguishes it from requirements
on a particular complete output and on an actual acquisition cut.

The full complex algebra, all twelve histories, unnormalized branch masses
and all exact-time output sectors are retained. The original unrestricted
common-CPTP benchmark is already supplied by CG16. The joint restricted
optimum and the original native acquisition/control problem remain distinct
questions.

**Definition 1.2 (original path and calibration premises).** For a base
$b=(X,Y,Z)$, put $r=1-Z$, with $0<Z<1$ and $0<X,Y<r$, and define

$$
\begin{aligned}
J_b&=(\max(0,X+Y-r),\min(X,Y)),\\
\pi_b(k)&=(r-X-Y+k,X-k,Z,Y-k,k),\\
\mathbf d&=(1,-1,0,-1,1),\qquad
I_b(k)=\sum_{i\in\{0,1,3,4\}}\pi_b(k)_i^{-1},\\
w_b(k)_i&=\frac{\mathbf d_i}{\pi_b(k)_i I_b(k)}.
\end{aligned}
\tag{JG.1}
$$

The original histories have finite duration $T\geq0$, continuous real
coordinates $k,\chi$, strict $k(t)\in J_b$, finite phase variation, and
either absolute continuity of both coordinates or the stated finite
piecewise-$C^1$ alternative with rates continuous on each closed piece.
Their calibrated normalized live vectors are

$$
\psi_i(t)=\sqrt{\pi_b(k(t))_i}\exp\left(-i\left[\theta_i+
  \int_0^t w_b(k(s))_i\chi'(s)\,ds\right]\right).
\tag{JG.2}
$$

Real lifts, signed integer winding $\chi(T)-\chi(0)=2\pi m$, and literal
chronological composition are part of these premises. They are the
source laws credited in CG2–4 and ZG2–3; their nested control and
instrument suppliers are not additional hypotheses proved here.

In the fixed experiment,

$$
c=\frac14,\quad Z=\frac12,\quad b=(c,c,Z),\quad
 a=\frac1{16},\quad h=\frac{11}{256},\quad d=\frac6{256},\quad L=1.
\tag{JG.3}
$$

Thus $J_b=(0,c)$, $\pi_b(k)=(k,c-k,Z,c-k,k)$, and
$w_b(k)=((c-k)/(2c),-k/(2c),0,-k/(2c),(c-k)/(2c))$.
The calibrated isometry $\iota:\mathbb C^3\to\mathbb C^5$ has columns

$$
|+\rangle=(e_0+e_4)/\sqrt2,\qquad
|-\rangle=(e_1+e_3)/\sqrt2,\qquad |2\rangle=e_2.
\tag{JG.4}
$$

Write $V=\operatorname{range}\iota$ and $\Pi=\iota\iota^\dagger$.
Within three-dimensional matrices, indices $0,1,2$ mean $(+,-,2)$;
$P_i=|i\rangle\langle i|$. They never rename the five stopped labels,
whose index $4$ retains the original name mode $13$.

**Definition 1.3 (actual catalogue and reached cut).** The histories have
$x=y/256$, $y\in\{5,16,27\}$, $\beta\in\{0,\pi\}$ and $m\in\{0,1\}$.
They start from one common preparation at $a_0=1/8$, with $\theta=0$.
For $q_0=1/16$ and $B=8\beta-4\pi m$, their credited six-leg realization
is the following; every leg has unit duration and affine coordinates.

| Leg | Height | Real phase coordinate |
| --- | --- | --- |
| 1 | $a_0$ | $0\longrightarrow2\pi m$ |
| 2 | $a_0\longrightarrow q_0$ | $2\pi m$ |
| 3 | $q_0$ | $2\pi m\longrightarrow2\pi m+B$ |
| 4 | $q_0\longrightarrow a_0$ | $2\pi m+B$ |
| 5 | $a_0$ | $2\pi m+B\longrightarrow2\pi m$ |
| 6 | $a_0\longrightarrow x$ | $2\pi m$ |

The residual lift is $(\beta,\beta-\pi m,0,\beta-\pi m,\beta)$.
Indeed its phase contribution is
$2\pi m\,w_b(a_0)+B(w_b(q_0)-w_b(a_0))$,
where $w_b(a_0)=(1/4,-1/4,0,-1/4,1/4)$ and the difference is
$(1/8,1/8,0,1/8,1/8)$. The height-only sixth leg adds no phase.
The source reach probabilities are respectively $32/177,2/9,32/111$.
They describe earlier execution, and are neither priors nor new
acceptance weights in the normalized experiment. Earlier stopped
archives remain absorbing.

At time six the processor receives ONE already reached normalized
specimen. The legal relative request is $k(t)=x+dt$ with unchanged old
phase, $0\leq t\leq1$. Its domain is
$(0,c-d)=(0,58/256)$ and its terminal heights are $11/256,22/256,33/256$.
For a general relative increment $A$ starting at zero and
$J_b=(\ell_b,u_b)$, the height domain is
$(\ell_b-\min A,u_b-\max A)$; this names no unknown-domain detector.
Known denial or mismatch retains its visible unexecuted rejection and
controller update. Literal composition neither reads nor resets the old
lift. Zero duration authorizes only matching zero displacement.
All heights here are internal; populations are at least $5/256$, height
speed at most $27/256$, phase speed at most $8\pi$, and phase variation
at most $16\pi$. No wall limit or infinite winding enters this catalogue.

**Definition 1.4 (one channel, states and complete error).** The available
metadata/blanks are a fixed common state: no-failure flag, aligned cut
clock, source/preparation/epoch identity, reference calibration, permissions
and controller state. They contain no acquired history, height or sign,
old waveform, generator word, callback, source programme, environment
input port, helper specimen or source-dependent installed processor.
Arbitrary independent ancillary spaces, randomness, computation, finite
adaptive instruments and retained records are allowed. Absorbing these
common inputs gives one history-independent CPTP map $\Phi$ on the whole
complex algebra. Every branch, including abort and rejection, is counted.
No success division, copy, retry or free entanglement bypass is introduced.

Set

$$
\begin{aligned}
p_y&=(y/128,(64-y)/128,1/2),&
a_y&=(\sqrt{p_{yi}})_i,&\rho_y&=a_ya_y^\dagger,\\
d_y&=\left(y/128,\frac{y(58-y)}{128(y+6)},\frac{y}{2(y+6)}\right),&
\xi_y&=(\sqrt{d_{yi}})_i,&B_y&=\xi_y\xi_y^\dagger,\\
s_y&=y/(y+6),& f_y(t)&=6y/(y+6t)^2,&
w&=(0,1/4,1/2,1/4,0).
\end{aligned}
\tag{JG.5}
$$

Here $U=\operatorname{diag}(e,n,1)$, $e=(-1)^{\beta/\pi}$,
$n=e(-1)^m$. The four original phase/parity choices give all four sign
pairs. The actual input is $U\rho_yU^\dagger$; its target $\Omega_{y,U}$
has live block $UB_yU^\dagger=s_yU\rho_{y+6}U^\dagger$ and, in EACH
original stopped sector $\ell=0,1,2,3,4$, the entire measure
$w_\ell f_y(t)dt\,P_f$, $P_f=|f\rangle\langle f|$.
Labels $1$ and $3$ remain separate, and mode $13$ keeps its zero ideal
measure. Time is exact elapsed $t\in[0,1]$, equivalently absolute $6+t$.
Since $\int f_y=1-s_y$, the full target has trace one.

For clarity, the credited calibrated law giving these targets has

$$
\begin{aligned}
K_x&=\operatorname{diag}\left(1,
 \sqrt{\frac{x(c-x-d)}{(x+d)(c-x)}},\sqrt{\frac{x}{x+d}}\right),\\
\mathcal I_{x,2}(dt)(A)&=\frac{dx}{(x+dt)^2}
 |f\rangle\langle2|A|2\rangle\langle f|\,dt,\\
\mathcal I_{x,\ell}(dt)(A)&=\frac{c}{2(c-x)}\frac{dx}{(x+dt)^2}
 |f\rangle\langle-|A|-\rangle\langle f|\,dt\quad(\ell=1,3),\\
\mathcal I_{x,0}&=\mathcal I_{x,4}=0.
\end{aligned}
\tag{JG.6}
$$

Their total effect is $I_V$. These are source-indexed target instruments;
they do not install the unknown $x$ in a common processor.

For normalized complete outputs, use half their complete cq trace norm,
and put

$$
E(\Phi)=\max_{y\in\{5,16,27\},\ e,n\in\{\pm1\}}
 \frac12\|\Omega_{y,U}-\Phi(U\rho_yU^\dagger)\|_{1,\mathrm{cq}},
\qquad E_\star=\inf_{\Phi\ \mathrm{common\ CPTP}}E(\Phi).
\tag{JG.7}
$$

The norm sums the coherent live trace norm and every labelled stopped
measure norm, plus every other sector norm. For arbitrary simulated
measures take densities with respect to a common dominating scalar
measure and integrate their trace norms. Atoms, singular-continuous
mass, wrong support, exceptional outcomes, abort and rejection are all
included, even with zero ideal weight. No time bins or finite-bit clock
are assumed. A fixed output interpretation may forget extra fields but
cannot delete an acquisition outcome or renormalize it. First executed
failure is absorbing, with no later positive-carrier operation, retry,
reversal, reset or replacement; old archives and controller updates remain
in their branches. All twelve actual targets stay in (JG.7).

## 2. An exact finite test for the simultaneous live restriction

**Definition 2.1 (supported live map and comparison matrix).** Let
$\Lambda:M_3(\mathbb C)\to M_3(\mathbb C)$ be the supported live
compression. It is zero-transfer in the calibrated basis when
$T_{ij}=\langle i|\Lambda(P_j)|i\rangle=0$ for $i\ne j$.
Use unnormalized output-input Choi order

$$
J_\Lambda=\sum_{i,j}\Lambda(|i\rangle\langle j|)\otimes|i\rangle\langle j|,
\qquad Se_i=|ii\rangle.
\tag{JG.8}
$$

The homogeneous cone $\mathfrak S_2$ consists of positive sums
$\sum_s|L_s\rangle\!\rangle\langle\!\langle L_s|$ with
$\operatorname{rank}L_s\leq2$, where
$|L\rangle\!\rangle=\sum_{a,i}L_{ai}|ai\rangle$.
Zero is included and no trace normalization is imposed. For a Hermitian
matrix $C$, write $d_i=C_{ii}$, $r_{ij}=|C_{ij}|$, and define

$$
M(C)_{ii}=d_i,\qquad M(C)_{ij}=-r_{ij}\quad(i\ne j).
\tag{JG.9}
$$

**Theorem 2.2 (finite joint coefficient characterization).** A supported
map is CP/TNI, zero-transfer, and has $J_\Lambda\in\mathfrak S_2$ if
and only if it is $\Lambda(A)=C\odot A$ on ALL complex matrices, for
one Hermitian $C$ with $0\leq d_i\leq1$ and $M(C)\succeq0$.
Equivalently its finite scalar test is

$$
\boxed{
\begin{gathered}
0\leq d_i\leq1\quad(i=0,1,2),\qquad
 d_i d_j\geq r_{ij}^2\quad(i<j),\\
d_0d_1d_2\geq d_0r_{12}^2+d_1r_{02}^2+d_2r_{01}^2
                         +2r_{01}r_{02}r_{12}.
\end{gathered}}
\tag{JG.10}
$$

If CP/TNI and zero transfer are already given, only $M(C)\succeq0$
is additional. All complex phases, zero coefficients, zero maps and
singular boundaries are included. Before the TNI upper bounds the
criterion is homogeneous. In particular $\operatorname{tr}J_\Lambda
=\sum_i d_i\in[0,3]$, rather than a prescribed unit trace.

Proof. The first reduction reuses the Schur/zero-transfer characterization
CG18.1 and ZG4.1. To fix its scope, a finite Kraus family has
$T_{ij}=\sum_a|(L_a)_{ij}|^2$. Vanishing off-diagonal transfers makes
every $L_a$ diagonal. With $L_a=\operatorname{diag}(v_a)$ this gives
$C=\sum_a v_av_a^\dagger\succeq0$ and $\Lambda(A)=C\odot A$,
including every non-Hermitian matrix unit. Conversely a positive
factorization of $C$ gives those Kraus operators. The coefficients are unique by the action on each matrix unit. Its effect is
$\Lambda^\dagger(I)=\operatorname{diag}(d)$, and its Choi matrix is
$SCS^\dagger$. TNI is exactly $d_i\leq1$.

Suppose this Choi matrix has a decomposition into vectorized matrices
of rank at most two. For $z\perp\operatorname{range}S$, positivity gives
$0=z^\dagger Jz=\sum_s|\langle z,L_s\rangle\!\rangle|^2$.
Every summand is supported on $\operatorname{range}S$, so every $L_s$
is diagonal. Its rank equals the number of its nonzero diagonal entries.
Consequently the Schmidt condition is precisely

$$
C=\sum_s v_sv_s^\dagger,\qquad |\operatorname{supp}v_s|\leq2.
\tag{JG.11}
$$

Vectorization proves the converse. The support argument is termwise
for positive countable sums and almost everywhere for positive integrals
by testing a finite basis of $(\operatorname{range}S)^\perp$.

For a decomposition (JG.11) and a real vector $q\geq0$, triangle
inequalities for the off-diagonal coefficients give

$$
q^TM(C)q\geq\sum_s\left[\sum_i |v_{si}|^2q_i^2
       -2\sum_{i<j}|v_{si}v_{sj}|q_iq_j\right]\geq0.
\tag{JG.12}
$$

Each singleton term is a square; each pair term is
$(|v_{si}|q_i-|v_{sj}|q_j)^2$. For any real $z$, nonpositive
comparison off-diagonals imply $z^TMz\geq|z|^TM|z|\geq0$.
Thus $M\succeq0$, also as a Hermitian matrix on complex vectors.
The inequalities also hold for the stated integrable positive sums.

For sufficiency assume $M\succeq0$. If $d_i=0$, its pair minors force
all incident $r_{ij}=0$; omit this isolated zero coordinate. On each
connected component of the remaining positive-diagonal graph, set
$D=\operatorname{diag}(d)$ and
$R_{ii}=0$, $R_{ij}=r_{ij}/\sqrt{d_i d_j}$, so
$M=D^{1/2}(I-R)D^{1/2}$. A top Rayleigh vector $u$ of the symmetric
nonnegative matrix $R$ can be chosen nonnegative, since taking absolute
values does not lower its Rayleigh quotient. It is an eigenvector for
the maximum eigenvalue $\lambda$. In a connected component a zero
coordinate in $u$ forces its neighbors to vanish by $Ru=\lambda u$,
and then forces $u=0$. Hence $u>0$. A singleton uses $u=1$, $\lambda=0$.
The maximum Rayleigh value is nonnegative, and $I-R\succeq0$ makes
$\lambda\leq1$. Put $s_i=u_i/\sqrt{d_i}>0$. Then
$Ms=(1-\lambda)D^{1/2}u\geq0$.

Allocate, for each nonzero edge $i<j$,

$$
b_{ij}=r_{ij}s_j/s_i,\qquad b_{ji}=r_{ij}s_i/s_j,
\qquad \eta_i=d_i-\sum_{j\ne i}b_{ij}\geq0.
\tag{JG.13}
$$

Their products are $b_{ij}b_{ji}=r_{ij}^2$. Choose a pair vector with
$v_i^{(ij)}=\sqrt{b_{ij}}$,
$v_j^{(ij)}=\overline{C_{ij}}/\sqrt{b_{ij}}$, and remaining coordinate
zero. Its cross coefficient is exactly $C_{ij}$, with diagonal costs
$b_{ij},b_{ji}$. Add the singleton $\sqrt{\eta_i}e_i$ whenever
$\eta_i>0$. These at most three pairs and three singletons sum exactly
to $C$. This proves CP and the Schmidt condition for arbitrary phases;
no separate positivity premise on $C$ is missing. Zero edges are skipped,
so no zero denominator occurs. At a singular connected boundary
$\lambda=1$ the residual is zero; isolated positive coordinates use
singletons and $C=0$ uses the empty sum.

Finally, the principal minors of $M$ are $d_i$, $d_id_j-r_{ij}^2$ and

$$
\det M=d_0d_1d_2-d_0r_{12}^2-d_1r_{02}^2-d_2r_{01}^2
                           -2r_{01}r_{02}r_{12}.
\tag{JG.14}
$$

They are necessary. For sufficiency, a zero diagonal and the pair
conditions remove all its incident edges and leave a positive two by
two matrix or a smaller diagonal matrix. Otherwise pivot on $d_0>0$.
The Schur complement has nonnegative diagonal entries by the two pair
conditions involving $0$, and determinant $\det M/d_0\geq0$.
A two by two Hermitian matrix with nonnegative diagonals and determinant
is PSD: a positive pivot proves it by a scalar Schur complement, and a
zero pivot forces its off-diagonal entry to vanish. Hence $M$ is PSD.
This uses all relevant principal minors, not just leading minors.
The two-coordinate positive decomposition and scaled diagonal allocation
are mature factor-width-two/scaled-diagonal-dominance structures; their
application to the homogeneous supported live intersection is the
specific statement proved here. $\square$

**Proposition 2.3 (one shared TP budget).** For the finite necessary test,
the exact joint feasible set is (JG.10) together with

$$
G_f,G_o\succeq0,\qquad \operatorname{diag}(d)+G_f+G_o=I_3.
\tag{JG.15}
$$

The effects can be complex and need not separately be diagonal. They
must belong to the SAME channel as $C$.

Proof. A channel with output
$(C\odot A,\operatorname{tr}(G_fA),\operatorname{tr}(G_oA))$ is CP
by its Kraus and positive-effect representations and is TP exactly
when (JG.15) holds. Conversely its effects must sum to identity.
In the output-input convention the identical condition is

$$
\operatorname{Tr}_{\rm out}(SCS^\dagger)+G_f^T+G_o^T=I_3,
\qquad\operatorname{Tr}_{\rm out}J_\Lambda=\Lambda^\dagger(I)^T.
\tag{JG.16}
$$

Only the live effect is diagonal. Its diagonality does not remove the
transposes on general $G_f,G_o$. Independently selected effects or
optimizers do not establish this joint identity. $\square$

## 3. Certificates, phases and the common diagonal budget

**Proposition 3.1 (finite separation on the supported cone).** If
$M(C)$ is not PSD, choose $q\geq0$ with $q^TM(C)q<0$ and phases
$\theta_{ij}$ of unit modulus satisfying $C_{ij}=r_{ij}\theta_{ij}$;
when $r_{ij}=0$ choose any unit phase. Set

$$
H_{ii}=q_i^2,\qquad H_{ij}=-q_iq_j\theta_{ij}\ (i<j),
\qquad H_{ji}=\overline{H_{ij}},\qquad
\delta=-\operatorname{tr}(HC)>0.
\tag{JG.17}
$$

Then every two-coordinate positive sum $X$ has
$\operatorname{tr}(HX)\geq0$, whereas
$\operatorname{tr}(HC)=q^TM(C)q<0$. In particular

$$
\|C-X\|_1\geq\delta/\|H\|_{\rm op}.
\tag{JG.18}
$$

Proof. A negative real quadratic-form vector exists for a non-PSD
real symmetric $M$; replacing it by its absolute values cannot increase
the quadratic form. Every two by two principal block of $H$ has
nonnegative diagonal and determinant zero, since its off-diagonal
modulus is $q_iq_j$. It is PSD, and therefore pairs nonnegatively with
each supported rank-one term of $X$. The trace pairing with $C$ has
cross terms $-2q_iq_jr_{ij}$, proving its stated value; this also fixes
the complex conjugation convention. Trace/operator-norm duality gives
(JG.18), with nonzero denominator because $\delta>0$.
This witness is restricted to $\operatorname{range}S$. It is not asserted
to be nonnegative on every unsupported Schmidt-two Choi vector: taking
a matrix's diagonal part can increase its rank. The distance is in
coefficient space and is not the original twelve-history error. $\square$

For a valid CP zero-transfer $C$ failing the test, a negative $q$ has a
finite coefficient construction. All $d_i>0$: otherwise positivity
would remove a row and column, leaving a positive two-coordinate
matrix, which passes. All one- and two-coordinate comparison blocks
are PSD, so failure means $\det M<0$. Put

$$
a=d_1-r_{01}^2/d_0,\qquad c=d_2-r_{02}^2/d_0,\qquad
b=r_{12}+r_{01}r_{02}/d_0.
\tag{JG.19}
$$

Then $a,c\geq0$, $b>0$ and $ac-b^2<0$. If $a>0$, take
$(q_1,q_2)=(b,a)$; if $a=0$, take $(q_1,q_2)=(c+b,2b)$.
In either case put $q_0=(r_{01}q_1+r_{02}q_2)/d_0$.
Completing the square in coordinate $0$ gives respectively
$q^TMq=a(ac-b^2)<0$ and $q^TMq=-4b^3<0$.
Every $q_i$ is positive, since a negative vector supported on at most
two coordinates would contradict its PSD principal block. This supplies
an obstruction also on singular pair boundaries, without optimization.

**Proposition 3.2 (phase geometry and a singular passing family).** When
all $d_i>0$, write $a=r_{01}/\sqrt{d_0d_1}$,
$b=r_{02}/\sqrt{d_0d_2}$ and $c=r_{12}/\sqrt{d_1d_2}$.
Then (JG.10), apart from the diagonal bounds, is exactly

$$
a^2+b^2+c^2+2abc\leq1.
\tag{JG.20}
$$

The unscaled test handles zero diagonals. Joint membership is equivalently
positivity for EVERY independent Hermitian assignment of edge phases
at the same diagonals and magnitudes.

Proof. Dividing (JG.14) by $d_0d_1d_2$ gives (JG.20); its nonnegative
summands also imply all pair bounds. This rescales coefficients and does
not normalize the Choi trace. If the edge product is nonzero and
$\phi=\arg(C_{01}C_{12}C_{20})$, ordinary CP instead uses

$$
\det C=d_0d_1d_2-\sum_i d_i r_{jk}^2
                         +2r_{01}r_{02}r_{12}\cos\phi,
\tag{JG.21}
$$

where each $jk$ is complementary to $i$. The comparison determinant
uses the worst sign $-2r_{01}r_{02}r_{12}$. The construction in Theorem
2.2 works for any chosen edge phases; conversely, positivity for all
assignments includes all-negative edges, which is precisely $M$.
Favorable cyclic phase can thus preserve CP while failing the common
pair budget, but cannot repair joint membership.

For $d_i=1$ and $r_{ij}=1/2$, the comparison is
$M=(3/2)I-(1/2)\mathbf1\mathbf1^\dagger\succeq0$ and is singular.
Three pair vectors, each with moduli $1/\sqrt2$ and the required conjugate
phase, construct every phase assignment. Here
$\det C=(1+\cos\phi)/4$ and every pair minor is $3/4$.
Hence $\operatorname{rank}C=2$ at $\phi=\pi$ and $3$ otherwise.
Every such live Choi has Schmidt number exactly two: a singleton-only
decomposition would make every off-diagonal coefficient zero.
Choi matrix rank therefore differs from required fibre dimension.
These phase assignments and consistent changes of coordinates are
mathematical comparisons, not supplied physical phase gates, arbitrary
rotations or an acquired reference frame. $\square$

**Proposition 3.3 (pairwise feasibility can exhaust the same budget).** The
matrix

$$
C=\frac25I+\frac35\mathbf1\mathbf1^\dagger
\tag{JG.22}
$$

defines a valid zero-transfer CP/TP live map, but fails the joint test,
even though all its pair minors are positive.

Proof. Its eigenvalues are $11/5,2/5,2/5$, its diagonal is one, and its
pair minors are $16/25$. Its comparison is
$M=(8/5)I-(3/5)\mathbf1\mathbf1^\dagger$, so $q=\mathbf1$ gives
$q^TMq=-3/5$. Equivalently any positive two-coordinate block supplying
an edge of modulus $3/5$ has diagonal sum at least $6/5$, by its
determinant inequality and AM–GM. In a decomposition, grouping all terms
on each pair gives those three costs, whose sum is at least $18/5$;
only trace $3$ is available. Singletons cannot reduce that cost.
Testing pairs with separate budgets therefore misses the obstruction.
$\square$

## 4. Live membership, some completion and a specified full channel

**Definition 4.1 (the jointly counted factorization model).** Reuse the
model CG21.2–21.3. In its finite form, the retained algebra at the cut is
$\mathcal B=\bigoplus_{\alpha\in A}M_{d_\alpha}(\mathbb C)$ with
finite $A$ and finite positive integer dimensions. Common CP encoders
$\mathcal E_\alpha$ and common full-output CPTP decoders
$\mathcal R_\alpha$ satisfy, on every complex matrix unit,

$$
\sum_\alpha\mathcal E_\alpha^\dagger(I_{d_\alpha})=I_3,
\qquad\Phi=\sum_\alpha\mathcal R_\alpha\mathcal E_\alpha,
\qquad p_\alpha(\rho)=\operatorname{tr}\mathcal E_\alpha(\rho).
\tag{JG.23}
$$

Only the encoder sum is TP. Each full decoder is TP; its supported live
compression is TNI. The same model permits countable $A$ when the CP
instrument sums converge and have total effect $I_3$. Its specified
integral version is

$$
\Phi=\int\mathcal R_\alpha\mathcal E_\alpha\,d\nu(\alpha),
\qquad\int\mathcal E_\alpha^\dagger(I)\,d\nu(\alpha)=I_3,
\tag{JG.24}
$$

with measurable finite integer dimensions, measurable encoder and
live-decoder Kraus fields, integrable effects and live Choi matrices,
and full decoders TP almost everywhere. Integral encoder densities
need not individually be TNI; the integrated instrument has the stated
budget. Low dimension means $d_\alpha\leq2$ everywhere or almost
everywhere. No disintegration of arbitrary quantum outputs is assumed.

For an ACTUAL cut, $\alpha$ is an actually generated classical record.
Every future-accessible quantum specimen, memory, controller part,
environment, returned system and entanglement share is counted jointly
in its fibre. A receiver's retained entanglement share is not an
independent blank. Passive inaccessible references remain allowed and
all identities tensor by their identity; later independent blanks remain
allowed. No later callback, helper specimen or uncounted bypass exists.
A coherent sum of putative branches is a quantum payload until an actual
classical direct sum is supplied. Neither a Kraus decomposition nor an
algebraic flag acquires that record. Acquisition duration and placement
in the aligned clock are implementation obligations, not extra time
supplied by (JG.23).

**Theorem 4.2 (existence of some low-dimensional full completion).** For a
zero-transfer live CP/TNI map, (JG.10) is equivalent to existence of SOME
full CPTP completion with that live map admitting a finite abstract
factorization (JG.23) with all fibres of dimension at most two. A
whole-complex five-mode completion can be specified as well. This
existence statement is about an abstract channel and not its native
availability.

Proof. Use the vectors $v_s$ of Theorem 2.2, with support $S_s$ of size
$k_s\in\{1,2\}$. In a carrier with orthonormal basis $q_i$ for
$i\in S_s$, set

$$
A_s=\sum_{i\in S_s}v_{si}|q_i\rangle\langle i|,\qquad
V_s=\sum_{i\in S_s}|i\rangle\langle q_i|.
\tag{JG.25}
$$

The encoder is $X\mapsto A_sXA_s^\dagger$; the full decoder is the
TP live isometry $Y\mapsto V_sYV_s^\dagger$.
Here $V_s^\dagger V_s=I_{k_s}$ and
$V_sA_s=\operatorname{diag}(v_s)$. Let
$D=I-\operatorname{diag}(d)\succeq0$. A scalar encoder
$X\mapsto\operatorname{tr}(DX)$, followed by a decoder that emits
original stopped mode $2$, stopped state $P_f$, and density
$h_0(t)=2/(1+t)^2$ on $[0,1]$, supplies the remainder. Since
$\int_0^1h_0=1$, that full decoder is TP. Its live part is zero.
The joint encoder effect is
$\sum_sA_s^\dagger A_s+D=\operatorname{diag}(d)+D=I$.
Thus the entire channel is

$$
\begin{aligned}
\Phi_{C,L}(X)&=C\odot X,\\
\Phi_{C,\ell}(X)(dt)&=\mathbf1_{\ell=2}
       \operatorname{tr}(DX)h_0(t)dt\,P_f,\qquad 0\leq\ell\leq4,
\end{aligned}
\tag{JG.26}
$$

with zero extra sectors. It is common and CPTP on every complex matrix,
including at passive reference amplification. All zero-weight stopped
labels remain named. Zero $D$ omits the stopped branch, and zero $C$
omits all live branches; neither case needs normalization of a branch.

For the full original input algebra take live output
$\iota\Lambda(\iota^\dagger X\iota)\iota^\dagger$, live encoders
$A_s\iota^\dagger$, and scalar stopped encoder effect

$$
D_5=I_5-\iota\operatorname{diag}(d)\iota^\dagger\succeq0.
\tag{JG.27}
$$

The total effect is $I_5$, all complementary-support mass is routed to
mode $2$, and cross-support operators have the specified zero image.
This proves a complete extension rather than presuming the unspecified
action of another channel outside $V$.

Conversely, encoder Kraus matrices $C_{\alpha u}$ and live-decoder
Kraus matrices $D_{\alpha v}$ yield live products
$L_{\alpha vu}=D_{\alpha v}C_{\alpha u}$ with
$\operatorname{rank}L_{\alpha vu}\leq d_\alpha$. If every fibre has
dimension at most two, their Choi sum belongs to $\mathfrak S_2$.
Zero transfer and Theorem 2.2 imply (JG.10). The same necessity holds
for the countable and stipulated integral models. To see the limiting
cone step, normalized rank-at-most-two vectorized matrices form a compact
set, as do their projectors and their finite-dimensional convex hull.
Its bounded homogeneous slices are compact, so positive integrable
sums remain in the cone. This is the mature product-rank bottleneck
argument already used in CG23, with the present exact supported test.
$\square$

**Theorem 4.3 (sufficiency for a particular reduced exact-time channel).**
Suppose the ENTIRE specified channel on $M_3$ consists of live map
$C\odot X$ and scalar nonlive record measures

$$
\mu_X(B)=\operatorname{tr}(E(B)X),\quad
K=\coprod_{\ell=0}^4(\{\ell\}\times[0,1])\sqcup\{o\},\quad
E(K)=I-\operatorname{diag}(d),
\tag{JG.28}
$$

where $E$ is a positive entrywise countably additive matrix-valued finite
Borel measure. Each stopped record has fixed state $P_f$; the other
point is scalar. For THIS full channel, (JG.10) is necessary and
sufficient for a factorization with fibres at most two in the specified
integral model. Finite or countably atomic $E$ permits the corresponding
finite or countable nonlive alphabet.

Proof. Keep the finite live encoders and TP decoders (JG.25). Define
$\nu(B)=\operatorname{tr}E(B)$, a finite positive measure. A positive
matrix with zero trace vanishes. Thus a $\nu$-null set and all its
subsets have zero $E$, and every component measure is absolutely
continuous with respect to $\nu$. Positivity bounds its component
variation, for a finite partition $(B_j)$, by

$$
\sum_j|E_{ab}(B_j)|\leq
 \sqrt{E_{aa}(K)E_{bb}(K)}.
\tag{JG.29}
$$

Entrywise scalar Radon–Nikodym representation therefore gives a
measurable Hermitian matrix density $F(z)$ with
$E(B)=\int_B F(z)d\nu(z)$. For a countable dense family of complex
vectors $v$, positivity of the measure $v^\dagger E v$ implies
$v^\dagger F(z)v\geq0$ outside a common null set; continuity in $v$
then gives $F(z)\succeq0$ almost everywhere. Also
$\operatorname{tr}F=1$ almost everywhere when $\nu\ne0$.

At each $z$ use the scalar encoder density
$X\mapsto\operatorname{tr}(F(z)X)$. Its full TP decoder prepares the
EXACT labelled record $z$ and $P_f$, or the isolated scalar other flag.
The output on every Borel $B$ is exactly $\operatorname{tr}(E(B)X)$.
Measurable encoder Kraus rows are the rows of the continuous positive
square root $F(z)^{1/2}$; their effect sum is $F(z)$. The nonlive
branches have zero live-decoder Kraus field. With the finite live tags
adjoined as discrete atoms, the integrated total effect is
$\operatorname{diag}(d)+\int Fd\nu=I$, and all effect and live Choi
integrals are finite. Delta-record preparation is a measurable decoder
on Borel events. If $E=0$ omit these branches. For atomic measures the
same construction is a sum over their atoms.

At reference amplification the scalar encoder outputs
$\operatorname{Tr}_{\rm in}[(F(z)\otimes I)X]$; its Kraus expression
shows positivity and the prescribed reference operation. Thus the
entire joint channel is reproduced, not just record probabilities.
Necessity is the product-rank proof in Theorem 4.2.

The measure representation used here is the mature scalar
Radon–Nikodym theorem applied to finitely many entries. General exact-time
measures require the explicitly stated integral alphabet; no automatic
finite/countable compression, finite-bit event storage or arbitrary
quantum-output disintegration follows. $\square$

The full-output hypothesis in Theorem 4.3 excludes extra accessible
quantum records, quantum wrong-support sectors, live-complement
coherences and unspecified five-mode action outside $V$. The canonical
target-fixing contraction of CG8.2 can remove such information while
preserving the live compression and contracting task error. It therefore
does not reverse the factorization inference for a particular actual
joint output. The next complete pair makes that distinction explicit.

## 5. Equal live maps, sector effects and task errors with different fibres

**Theorem 5.1 (a complete five-mode dimension-two/dimension-three pair).**
There are whole-complex five-mode CPTP channels with the same nonzero
passing zero-transfer live map, the same effects of every original
stopped sector and of the other sector, and identical original complete
errors on every actual history, whose minimum maximal abstract fibre
dimensions in Definition 4.1 are respectively TWO and THREE. The lower
bounds also hold in the countable and specified integral versions.

Proof. Fix $0<r<1$, let $\Delta(X)=\sum_iP_iXP_i$, and put

$$
C_b=(I+\mathbf1\mathbf1^\dagger)/2,\qquad
C=rC_b,\qquad\Lambda_r(X)=\frac r2(X+\Delta(X)).
\tag{JG.30}
$$

Its comparison is $r[(3/2)I-(1/2)\mathbf1\mathbf1^\dagger]$,
which is PSD and singular. Its live Kraus matrices are
$K_{ij}=\sqrt{r/2}(P_i+P_j)$, $i<j$.
Their effect sum is $rI$, and every off-diagonal input coefficient
is retained with factor $r/2>0$.

Take an output direct sum consisting of the terminal live algebra,
all five original exact-time stopped sectors, and an accessible quantum
other block $Q\simeq\mathbb C^3$. Let $W:\mathbb C^3\to Q$ be a fixed
isometry and $Q_0$ a fixed pure state in $Q$. All targets have zero
other mass. On $M_3$ define

$$
\begin{aligned}
\Phi_{g,L}(X)&=\Phi_{b,L}(X)=\Lambda_r(X),\\
\Phi_{g,\ell}(X)&=\Phi_{b,\ell}(X)=0\quad(\ell=0,1,2,3,4),\\
\Phi_{g,o}(X)&=(1-r)\operatorname{tr}(X)Q_0,\\
\Phi_{b,o}(X)&=(1-r)WXW^\dagger.
\end{aligned}
\tag{JG.31}
$$

These are CP at every reference amplification; the live effect is $rI$,
each stopped effect is zero, and the other effect is $(1-r)I$. Thus
both are TP and all sector effects agree.

The good channel factors through three dimension-two live tags given
by $K_{ij}$ and (JG.25), and one scalar other encoder
$X\mapsto(1-r)\operatorname{tr}X$ followed by $Q_0$ preparation.
All full decoders are TP and their effects sum to $I$.
A scalar-fibre factorization would give only rank-at-most-one live
Kraus products. Zero transfer would make them diagonal, hence supported
on single coordinates; their coefficient matrix would be diagonal.
This contradicts its off-diagonals $r/2$. Thus its minimum maximal
fibre dimension is exactly two.

For the bad channel, compression to $Q$ followed by $W^\dagger$ gives
$(1-r)\operatorname{id}_{M_3}$. Its Choi matrix is

$$
(1-r)|\Omega\rangle\langle\Omega|,\qquad
|\Omega\rangle=|00\rangle+|11\rangle+|22\rangle.
\tag{JG.32}
$$

In any positive rank-one decomposition of a nonzero rank-one positive
matrix, testing the perpendicular complement forces every summand into
its one-dimensional range. Every nonzero vector in this range reshapes
to a rank-three matrix. An all-fibres-at-most-two factorization would
instead yield rank-at-most-two products even after the $Q$ compression,
a contradiction. The same support test applies termwise for countable
sums and almost everywhere for the stipulated integrals. A dimension-three
other encoder $\sqrt{1-r}W$ and identity decoding, besides the same
three dimension-two live tags, realize the bad channel. Its minimum
maximal dimension is therefore exactly three.

Here is the FULL five-mode specification. Give both channels live output
$\iota\Lambda_r(\iota^\dagger X\iota)\iota^\dagger$ and zero stopped
measures, and set

$$
\begin{aligned}
\widehat\Phi_{g,o}(X)&=\operatorname{tr}((I_5-r\Pi)X)Q_0,\\
\widehat\Phi_{b,o}(X)&=(1-r)W\iota^\dagger X\iota W^\dagger
                +\operatorname{tr}((I_5-\Pi)X)Q_0.
\end{aligned}
\tag{JG.33}
$$

These CP maps both have total effect $I_5$, other effect $I_5-r\Pi$,
and the same specified zero cross-support images. The good other
encoder is scalar; the bad other encoder uses its dimension-three
supported branch and a scalar complementary-support branch. Live
encoders compose with $\iota^\dagger$. Restricting to $V$ preserves
the preceding lower obstructions, so their exact dimensions remain
two and three on the full input algebra.

Finally, for each original sign history at a fixed $y$, both channels
have EXACT full error

$$
\frac12\left[
 \left\|B_y-\frac r2(\rho_y+\operatorname{diag}(p_y))\right\|_1
                    +(1-s_y)+(1-r)\right].
\tag{JG.34}
$$

Live sign covariance gives the first term. The five ideal stopped
measure norms sum to $\sum_\ell w_\ell\int f_y=1-s_y$, because both
simulated laws there are zero. The positive other output has zero
ideal target and trace $1-r$ in each channel, regardless of its quantum
state. Thus their $E$ is the maximum of (JG.34) over $y=5,16,27$,
with all twelve inputs, labels, exact times and the entire other mass
counted. No branch normalization or changed readout occurs.

The block $Q$ is accessible OUTPUT, not an additional input specimen or
helper. If an interpretation traces it out, the interpreted channels
coincide, but their full joint payload requirements differ. A passing
live test together with equal effects and task errors therefore cannot
certify the low-dimensional factorization of a particular full output.
$\square$

## 6. A supported witness forces actual high-fibre mass on every input

**Theorem 6.1 (arbitrary failing-coefficient mass bound).** Let $C$ be a
valid zero-transfer CP/TNI live coefficient matrix strictly failing
$M(C)\succeq0$. Choose the positive $q$ and supported separator $H$
of Proposition 3.1, and $\delta=-q^TM(C)q>0$. Define

$$
\beta_j=\frac{\delta^2}
 {4q_j^2\left(\sum_{k\ne j}q_k\sqrt{d_k}\right)^2},
\qquad\beta=\min_{j=0,1,2}\beta_j>0.
\tag{JG.35}
$$

For ANY full channel with this live map and an ACTUAL fully counted
factorization (JG.23), or its countable or specified integral version,
let the high set be $A_{\geq3}=\{\alpha:d_\alpha\geq3\}$, and let
$p_{\geq3}^{\rm acq}(\rho)$ count its acquisition mass and
$p_{\geq3}^L(\rho)$ its later supported live mass. For EVERY positive
possibly subnormalized complex input $\rho$,

$$
p_{\geq3}^{\rm acq}(\rho)\geq p_{\geq3}^L(\rho)
                                      \geq\beta\operatorname{tr}\rho.
\tag{JG.36}
$$

These are unconditional masses on the received specimen; in particular
the bound holds on each of the twelve original inputs separately.

Proof. Split the actual live map into low- and high-fibre CP contributions.
Their positive Choi matrices sum to $SCS^\dagger$. Testing its orthogonal
complement forces both aggregates to have that support. Hence their
coefficient matrices satisfy $C=C_L+C_H$, $C_L,C_H\succeq0$.
The product-rank argument puts $C_L$ in the two-coordinate cone;
$\operatorname{tr}(HC_L)\geq0$, so
$\operatorname{tr}(HC_H)\leq-\delta$.
This support step is essential: $H$ is not a global Schmidt-two witness.

Put $x_i=(C_H)_{ii}$. The high live effect is
$\operatorname{diag}(x)$, and $0\leq x_i\leq d_i\leq1$.
For a fixed $j$, the complementary two by two block of $H$ is PSD and
pairs nonnegatively with the corresponding positive block of $C_H$.
Positivity also gives $|(C_H)_{jk}|\leq\sqrt{x_jx_k}$. Consequently

$$
\begin{aligned}
\operatorname{tr}(HC_H)
&\geq q_j^2x_j-2q_j\sqrt{x_j}\sum_{k\ne j}q_k\sqrt{x_k}\\
&\geq-2q_j\sqrt{x_j}\sum_{k\ne j}q_k\sqrt{d_k}.
\end{aligned}
\tag{JG.37}
$$

Combine with its negative upper bound and square nonnegative quantities
to obtain $x_j\geq\beta_j$. Thus
$\operatorname{diag}(x)\succeq\beta I$ and
$p_{\geq3}^L(\rho)=\operatorname{tr}(\operatorname{diag}(x)\rho)
\geq\beta\operatorname{tr}\rho$, without a real, diagonal, pure or
unit-trace restriction on $\rho$. Each full TP decoder has a TNI
supported live part; summing its trace inequalities gives
$p_{\geq3}^{\rm acq}\geq p_{\geq3}^L$.

All denominators are positive: in the failing CP case every $d_i>0$,
and a nonnegative negative-quadratic-form $q$ has every coordinate
positive, as proved after (JG.19). No quotient is assigned at $C=0$
or a passing singular boundary. In the integral model the dimension
sets are measurable and all low/high effects and live Choi fields are
positive and integrable. The support arguments hold almost everywhere,
the aggregate low cone is closed, and the same trace inequalities can
be integrated. Countable sums obey the same proof. A closure limit
without an actual cut has no acquired-probability interpretation.
$\square$

**Proposition 6.2 (homogeneity and a phase-adapted example).** For (JG.22),
one can take $q=\mathbf1$, $\delta=3/5$ and $d_i=1$, giving
$\beta=9/400$. Scaling $C$ by $0<\tau\leq1$ gives
$\beta=9\tau/400$. There are also failing maps with this bound which
the inherited fixed witness $W_3=|\Omega\rangle\langle\Omega|-2I_9$
does not detect.

Proof. In (JG.35) each unscaled denominator is $4\cdot2^2=16$,
so $\beta_j=(3/5)^2/16=9/400$. Scaling multiplies $\delta$ by
$\tau$ and $d_i$ by $\tau$, hence multiplies $\beta$ by $\tau$.
At $\tau=0$ the map passes and Theorem 6.1 is not invoked.

Let $\omega$ be a nontrivial cube root of unity and put

$$
g=(1,\omega,\omega^2)^T,\qquad
C_g=\frac25I+\frac35gg^\dagger.
\tag{JG.38}
$$

It is CP/TP with diagonal one and edge magnitudes $3/5$. Its comparison,
$\delta$ and $\beta$ equal those of (JG.22). The separator is now
phase-adapted: $H=2I-gg^\dagger$, with two-coordinate PSD blocks and
$\operatorname{tr}(HC_g)=-3/5$.
But $\mathbf1^\dagger g=0$, and therefore

$$
\operatorname{tr}(W_3SC_gS^\dagger)
 =\mathbf1^\dagger C_g\mathbf1-2\operatorname{tr}C_g
 =\frac65-6=-\frac{24}{5}.
\tag{JG.39}
$$

The fixed witness is nonpositive here, while the supported separator
still forces (JG.36) with $9/400$ for every actual realization.
Moreover the inherited inequality CG.222, applied with
$\eta=E(\Phi)-E_\star$, implies
$\delta_\star-2K\sqrt\eta\leq-24/5$ for any original channel with
this live map. Its inherited performance-based positive part is
therefore zero. This establishes a distinct map-specific application;
it neither improves an optimizer bound nor supplies a physical gauge
operation. The trace and positivity calculations are exact symbolic
identities. $\square$

## 7. Current inherited quantitative bounds and the unchanged error problem

**Premise 7.1 (the credited exact benchmark and algebraic data).** The
root isolation, nonsingular bordered Jacobian, ranks and margins in
CG13–16 are ordinary computer-assisted premises. In particular CG16.1
supplies

$$
E_\star=F(x_\star)=\delta_{27},\qquad
0.14817810291080132013<E_\star<0.14817810291080132014.
\tag{JG.40}
$$

This answers the enlarged common-CPTP minimax questions in CG7 and CG11;
it leaves the native-control correspondence separate. The decimal
center of its isolating box is not substituted for its exact algebraic
zero. All comparisons here with $E_\star$ and inherited constants are
conditional on these credited data, their calibration and theorem
premises. The coefficient criterion, completions, complete-channel pair
and supported mass theorem do not depend on that arithmetic certificate.

For exact notation, CG.112–CG.114 use
$x=(\lambda,\alpha_1,\alpha_2,\beta_1,\beta_2,z)$,
$v_5=(\alpha_1,\alpha_2,-1)^T$, $v_{27}=(\beta_1,\beta_2,1)^T$,
$R_y=v_yv_y^T/(v_y^Tv_y)$, $A_5=\lambda R_5$,
$A_{27}=(1-\lambda)R_{27}$, and

$$
\begin{aligned}
\zeta&=(z,\lambda p_{51},\lambda p_{52}),\qquad Z_d=\operatorname{diag}\zeta,\\
N&=A_5\odot\rho_5+A_{27}\odot\rho_{27},\qquad S_0=Z_d-N,\\
S_{ij}&=\begin{pmatrix}
\zeta_j-\sum_{y=5,27}(A_y)_{ii}p_{yj}&-N_{ij}\\
-N_{ij}&\zeta_i-\sum_{y=5,27}(A_y)_{jj}p_{yi}
\end{pmatrix},\\
S(x)&=S_0\oplus S_{01}\oplus S_{02}\oplus S_{12},\\
F(x)&=\operatorname{tr}(A_5B_5)+\operatorname{tr}(A_{27}B_{27})
                       -\operatorname{tr}Z_d+6\lambda/11,\\
g(x)&=(1000\det S_0,\det S_{01},\det S_{02}).
\end{aligned}
\tag{JG.41}
$$

The chart coordinates $\beta_1,\beta_2$ are unrelated to the original
history phase $\beta$. The exact $u_\star=(x_\star,\eta_\star)$ is the isolated zero of
$\Psi=(\nabla_x(F+\eta\cdot g),g)$ in the rational box of CG13.2.
The block order is $(00,11,22)$, $(01,10)$, $(02,20)$, $(12,21)$
in output-input Choi order. At that point put

$$
\begin{aligned}
H_\star&=1000\eta_{0,\star}\operatorname{adj}S_{0,\star},\\
Q_\star^{01}&=\eta_{1,\star}\operatorname{adj}S_{01,\star},\qquad
Q_\star^{02}=\eta_{2,\star}\operatorname{adj}S_{02,\star},\\
J_\star&=H_\star\oplus Q_\star^{01}\oplus Q_\star^{02}\oplus0,\\
\delta_\star&=\mathbf1^TH_\star\mathbf1-2\operatorname{tr}J_\star>19/10.
\end{aligned}
\tag{JG.42}
$$

The last margin is inherited from CG22, not recomputed. This starred
$H_\star$ is distinct from the supported separator $H$ of (JG.17).

**Definition 7.2 (the inherited stability modulus).** To distinguish
CG.204's scalar constant $C$ from the coefficient matrix $C$, call that
same scalar $K$. Every quantity below is evaluated at $x_\star$.
Let $P$ project onto $\ker S_\star$, and define

$$
\begin{aligned}
s&=\min\{\nu>0:\nu\text{ is an eigenvalue of }S_\star\},\\
c_f&=\zeta_{0,\star}-\lambda_\star p_{50},\qquad
z_{\min}=\min_i\zeta_{i,\star},\\
\mathcal B_0&=(1000\operatorname{adj}S_{0,\star})\oplus0\oplus0\oplus0,\\
\mathcal B_1&=0\oplus\operatorname{adj}S_{01,\star}\oplus0\oplus0,\\
\mathcal B_2&=0\oplus0\oplus\operatorname{adj}S_{02,\star}\oplus0,\\
M_j&=\partial_{x_j}S(x_\star)\quad(1\leq j\leq6),\qquad
L=\left(\sum_{j=1}^6\|M_j\|_{\rm op}^2\right)^{1/2},\\
b&=\left(\sum_{k=0}^2\|\mathcal B_k\|_1^2\right)^{1/2},\qquad
G=[\nabla g_0\ \nabla g_1\ \nabla g_2]_{x_\star},\\
\sigma&=\min_{u\in\mathbb R^3,\ \|u\|_2=1}\|Gu\|_2,\qquad
 a=2\sqrt{3/s},\\
r_\lambda&=\lambda_\star^{-1}+(1-\lambda_\star)^{-1}
                         +p_{50}/c_f+z_{\min}^{-1},\\
r_z&=c_f^{-1}+z_{\min}^{-1},\\
A&=\left(r_\lambda^2+r_z^2+
       \frac{16\lambda_\star}{\|v_{5,\star}\|_2^2}+
       \frac{16(1-\lambda_\star)}{\|v_{27,\star}\|_2^2}\right)^{1/2},\\
K&=a+\frac b\sigma(A+La).
\end{aligned}
\tag{JG.43}
$$

These are exactly CG.204's constants, with no new evaluation. Its
credited slack ranks $2,1,1,2$ make $s>0$. The credited margins give
$c_f,z_{\min}>0$, $0<\lambda_\star<1$, and nonzero $\mathcal B_k$.
The chart denominators and both $\|v_y\|_2$ are positive.
Nonsingularity of the bordered Jacobian implies $G$ injective:
$Gu=0$ would put $(0,u)^T$ in that Jacobian's kernel.
Compactness of the unit sphere then gives $\sigma>0$.
Thus (JG.43) is finite with $K>0$. The symbol $K$ here is a scalar
modulus, not the source-indexed operator $K_x$ in (JG.6).

**Convention 7.3 (reuse of ALL current stability, error and resource
consequences).** CG26.3 and CG27.1 already state, for the actual live
Choi matrix $J$ of ANY original common full channel with
$E(\Phi)\leq E_\star+\epsilon$, $0\leq\epsilon\leq1$,

$$
\begin{aligned}
\overline J&=\frac14\sum_{e,n}(U_{e,n}\otimes U_{e,n})
                         J(U_{e,n}\otimes U_{e,n})^\dagger,\\
\|\overline J-J_\star\|_1&\leq K\sqrt\epsilon,\\
|T_{ij}-\tau_{ij}|&\leq K\sqrt\epsilon\quad(0\leq i,j\leq2),\\
\operatorname{tr}(W_3J)&\geq\delta_\star-2K\sqrt\epsilon,
\qquad\tau_{ij}=\langle ij|J_\star|ij\rangle.
\end{aligned}
\tag{JG.44}
$$

The four values
$\tau_{01}=(Q_\star^{01})_{00}$,
$\tau_{10}=(Q_\star^{01})_{11}$,
$\tau_{02}=(Q_\star^{02})_{00}$,
$\tau_{20}=(Q_\star^{02})_{11}$ are positive.
These estimates also hold for every finite-test channel, with $E_c$
in the premise. Sign averaging fixes the Choi diagonal entries and
$W_3$, whose operator norm is $2$; this is why the bounds concern
actual transfers and actual witness pairing without identifying the
whole unaveraged channel.

The inherited proof CG.207–CG.220 controls the slack tail by
$\operatorname{tr}((I-P)\overline J)\leq\epsilon/s$ and positive
compression by
$\|\overline J-P\overline JP\|_1\leq a\sqrt\epsilon$,
using $\operatorname{tr}J\leq3$, with zero trace treated directly.
The compressed face is $\sum_k\widehat\eta_k\mathcal B_k$.
The SAME endpoint effect deficits bound the six-coordinate fixed-matrix
first differential by $A\sqrt\epsilon$; trace pairing contributes
$La\sqrt\epsilon$, and injectivity of $G$ bounds coefficient displacement
by $(A+La)\sqrt\epsilon/\sigma$. This gives precisely (JG.43),
without a new exact-time representation or a new strong-duality premise.
These are uses of CG26, not additional stability claims here.

For every ACTUAL fully counted factorization with these original error
hypotheses, CG27.2 already gives, on EVERY normalized complex $\rho$,

$$
p_{\geq3}^{\rm acq}(\rho)\geq p_{\geq3}^L(\rho)
 \geq\frac{D(\epsilon)^2}{24},\qquad
 D(\epsilon)=\max\{\delta_\star-2K\sqrt\epsilon,0\}.
\tag{JG.45}
$$

For positive subnormalized $\rho$, multiply the last right side by
$\operatorname{tr}\rho$; this follows by linearity, and zero input is
immediate. The exact-optimal case reuses CG24's
$\delta_\star^2/24>361/2400>3/20$. Its mechanism is the homogeneous
estimate $\operatorname{tr}(W_3J_H)\leq2\sqrt{6p_{\geq3}^L(P_\psi)}$
for every pure complex input of the same CP/TNI high submap, together
with the product-rank low-cone obstruction. It covers the finite,
countable and specified integral actual cuts in Definition 4.1.
A finite-test closure without such a cut has no probability reading.

With $\eta=E(\Phi)-E_\star\in[0,1]$, CG27.3 already supplies

$$
\begin{aligned}
J\in\mathfrak S_2&\ \Longrightarrow\
 \eta\geq\frac{\delta_\star^2}{4K^2},\\
T_{ij}=0&\ \Longrightarrow\
 \eta\geq\frac{\tau_{ij}^2}{K^2}
       \quad(ij\in\{01,10,02,20\}),\\
\eta&\geq\frac{[\max\{\delta_\star-
                  \sqrt{24p_{\geq3}^L(\rho)},0\}]^2}{4K^2}
 \quad\text{for each normalized }\rho\text{ in an actual cut}.
\end{aligned}
\tag{JG.46}
$$

The last line remains valid with the larger acquisition probability.
The witness inequality is nonpositive on $\mathfrak S_2$; inserting
that sign or a zero transfer into (JG.44) gives the first two lines.
Combining the high-submap estimate with the last line of (JG.44) and
rearranging before squaring gives the last line. These deductions and
their positive symbolic penalties are inherited from CG27. In particular
the dimension-two error penalty and the near-optimal resource theorem
are already quantitative current results. Theorem 6.1 addresses a
different, arbitrary failing $C$ by a phase-adapted supported witness;
it does not replace or sharpen these optimizer/performance results.

**Convention 7.4 (the inherited maximum on the joint class).** Let
$\epsilon_{\rm q}=\eta_{1,\star}\tau_{\rm q}/2>0$ be EXACTLY the
closed algebraic constant defined in ZG.23–ZG.29, with its ascent and
positivity proof ZG7–8. Let
$\epsilon_0=\mu_0-E_\star>0$ and
$\epsilon_2=\mu_2-E_\star>0$ be the finite-test minima and existential
gaps of CG.170 and CG.192. Every original full channel satisfying
the simultaneous restriction inherits

$$
\boxed{
E(\Phi)\geq E_\star+
 \max\left\{\epsilon_{\rm q},\frac{\delta_\star^2}{4K^2},
        \max_{ij\in\{01,10,02,20\}}\frac{\tau_{ij}^2}{K^2}\right\}.}
\tag{JG.47}
$$

It also inherits $E(\Phi)\geq E_\star+\max\{\epsilon_0,\epsilon_2\}$.
If desired all these applicable constants can be put in one maximum.
None is a new performance constant of this volume.

The justification is direct reuse: a joint map is zero-transfer, so
ZG8.2 and all four transfer penalties apply; it also belongs to
$\mathfrak S_2$, so the inherited Schmidt penalty applies. The same
bounds hold on their corresponding finite feasible sets. Taking their
minima there gives

$$
\epsilon_0\geq\max\left\{\epsilon_{\rm q},
           \max_{ij\in\{01,10,02,20\}}\tau_{ij}^2/K^2\right\},
\qquad\epsilon_2\geq\delta_\star^2/(4K^2).
\tag{JG.48}
$$

Thus an explicit source-dependent penalty is not asserted to dominate
an unknown restricted gap. No numerical ordering between
$\epsilon_{\rm q}$ and the CG27 constants has been established here.
Separate lower bounds give their maximum, not their sum. No strict
improvement above that maximum, joint restricted optimum, restricted
optimizer or sharp mass constant follows from intersecting classes.

**Definition 7.5 (the remaining simultaneous error constraints).** The
finite necessary optimization uses ONE $C,G_f,G_o$ satisfying (JG.10)
and (JG.15), and all twelve errors

$$
\begin{aligned}
E_c=\max_{y,U}\frac12\bigl(&\|UB_yU^\dagger
                       -C\odot(U\rho_yU^\dagger)\|_1\\
 &+|1-s_y-\operatorname{tr}(G_fU\rho_yU^\dagger)|
                    +\operatorname{tr}(G_oU\rho_yU^\dagger)\bigr).
\end{aligned}
\tag{JG.49}
$$

This is an exact finite description of the simultaneous live feasible
set in CG.155. It supplies constructions or obstructions for proposed
coefficients; it does not lift a finite-test optimizer to an optimal
complete exact-time channel.

For a reduced FULL candidate there must instead be ONE positive
countably additive effect measure $E$ on $K$ of (JG.28), with
$E(K)=I-\operatorname{diag}(d)$. Put
$\mu_{y,U}(B)=\operatorname{tr}(E(B)U\rho_yU^\dagger)$.
At a proposed error $e$, the exact full constraints are, for EVERY
$y=5,16,27$ and all four actual $U$,

$$
\frac12\left[
 \|UB_yU^\dagger-C\odot(U\rho_yU^\dagger)\|_1+
 \sum_{\ell=0}^4\|\mu_{\ell,y,U}-w_\ell f_y(t)dt\|_{\rm TV}
                         +\mu_{o,y,U}(\{o\})\right]\leq e.
\tag{JG.50}
$$

Every atom, singular-continuous part, zero-target label and other
mass is included. A general unreduced output uses the full quantum
cq norm (JG.7). The target-fixing canonical contraction CG8.2 keeps
$C\odot X$ and contracts all errors. Conversely the reduced law is
itself an abstract full candidate. Theorem 4.3 concerns the specified
reduced channel, not the additional accessible quantum records erased
by such a contraction. In particular neither (JG.18) nor (JG.36) substitutes
for the complete twelve-history objective (JG.50).

## 8. Mathematical correspondence and unresolved native bridges

**Convention 8.1 (precise inherited content and additional application).**
The references below use [CG] through §28 and [ZG] through §10.
They retain their original hypotheses; a source-reported arithmetic,
calibration or literature premise is not kernel authority.

| Source | Mathematical role and scope |
| --- | --- |
| CG1–4, CG.1–CG.20; ZG2–3 | Original paths, preparation, real lifts, finite durations and regularity, actual histories, reached-cut normalization, legal relative ramp, common resources, coherent successors and five full exact-time laws. Their nested suppliers are credited premises. |
| CG5–12, CG.21–CG.110 | Coherence-retaining lower tests, attainment in the enlarged class, strict nonoptimality of the earlier bound and scalar-live/fixed-filter feasible channels. These are prior results, not additional claims of this joint application. |
| CG13–16, CG.111–CG.154; ZG5 | Exact isolated algebraic point, nonsingular Jacobian, ranks/margins, whole-complex lower certificate, matching full-output instrument and solved $E_\star=F(x_\star)$. These conditional computer-assisted data enter only the inherited benchmark and performance comparisons. |
| CG17–18, CG.155–CG.170; ZG4 | One transposed Choi/effect budget, finite contraction, averaged optimizer rigidity, positive transfers, Schur characterization, existential zero-transfer gap and the precisely defined conditional diagonal closure. The new finite comparison criterion resolves the simultaneous Schmidt restriction on that support. |
| CG19–20, CG.171–CG.178; ZG9.1–9.2 | The earlier same-effects pair has identical branch/reference marginals and different successors, with inherited error separation. Its diagonal instrument, controlled swaps, support decomposition and physical time services remain conditional. Theorem 5.1 instead compares passing live maps with equal task errors and distinct quantum other outputs. |
| CG21–25, CG.179–CG.203; ZG9.3 and ZG10 | Actual jointly counted factorization, finite/countable/specified integral hypotheses, product-rank necessity, homogeneous Schmidt cone, all-optimizer Schmidt-three witness, existential dimension-two gap, every-input optimizer mass, abstract optimum factorization and counterexamples. Their separate class noninclusions and resource necessities are inherited. |
| CG26–28, CG.204–CG.225 | Square-root averaged stability, all-transfer deviations, explicit Schmidt-two and individual-zero-transfer penalties, near-optimal every-input high-fibre mass and inverse resource/error tradeoff. Equations (JG.43)–(JG.48) expressly reuse all these current quantitative conclusions. |
| ZG6–8, ZG.23–ZG.48 | The positive closed algebraic $\epsilon_{\rm q}$ and its original full-output zero-transfer loss, including the correct complex/transpose and norm direction. It is inherited on the smaller joint class without a new error estimate. |
| Theorems 2.2, 4.2–4.3, 5.1, 6.1 and Propositions 3.1–3.3, 6.2 | The additional application is the exact complex/singular homogeneous comparison criterion, shared allocation and phase-adapted certificates, justified completion/reduced-channel distinctions, complete five-mode equal-error dimension separation, and arbitrary-failing-map supported mass consequence. |

The generic two-coordinate positive cone is commonly called factor
width at most two and is related to scaled diagonal dominance.
Spectral maximization, Schur complements, Choi/Kraus vectorization,
product-rank compression, trace-norm duality, positive-effect budgets,
Cauchy–Schwarz and scalar Radon–Nikodym representation are mature tools.
Their needed applications are supplied inside the ordinary proofs above,
rather than claimed as invented general structures. The added statements
are `repo-derived` applications relative to the cited theory bodies;
no literature-wide originality, absence or priority claim is made.

CG18 and ZG4 report de Vicente–Streltsov's genuine-coherence/Schur
characterization. CG22 reports Terhal–Horodecki's Schmidt-number overlap
bound, Chruściński–Kossakowski's Choi/Kraus correspondence and Sekatski's
classical-assisted bottleneck formulation. CG14–16 report the
Heinosaari–Jivulescu–Reeb–Wolf finite CP-extension framework and
Nechita–Park's sign-covariant transfer/reverse-coherence structure.
CG28 reports complementary-face error-bound antecedents and identifies
its positive-compression and trace-pairing library inputs. These are
SOURCE-REPORTED attributions with the exact cited scopes, not an
independent authentication of external texts or a new formal application.
Sign covariance alone does not imply Schur form, and no finite-output
literature statement replaces the measure-level proofs here.

**Definition 8.2 (unresolved native realization obligation).** To realize
one of these abstract factorizations under the original permissions,
one must actually supply lawful acquisition of the sole unresolved
specimen, calibrated encoding, any generated classical record, retention
of the ENTIRE joint payload, and its permitted controlled decoding.
Five-mode completion additionally requires the calibrated support
correspondence. The cut's duration and placement must fit the original
aligned clock without extra execution time. All old archives, source
and epoch identity, permissions and controller updates must match.

A physical exact-time realization must make the FIRST absorbing event
occur at the required elapsed time, allow no later positive-carrier
action on failed branches, and supply terminal live output at time one.
The density $h_0$ in (JG.26) specifies a mathematical law; even its
inverse-CDF description $H_0(t)=2t/(1+t)$,
$H_0^{-1}(u)=u/(2-u)$ supplies neither finite-bit event storage nor that
physical event. A generated record destining a later failure or a
timestamp written after a different event is insufficient for this
contract.

The source-indexed $K_x$, a Kraus/Choi decomposition, abstract Stinespring
realization, equal effects, common reference marginals and a passing live
test do not supply these services. The conditional diagonal closure in
CG18.2 is not an exhaustive native menu: the source's original-control
predicate governs paths, and its probability-changing noncommuting
geometry does not identify all permitted operations with Schur maps.
Geometric reachability alone supplies neither arbitrary rotations nor
controlled swaps on an unknown specimen.

**Open problem 8.3 (the remaining mathematical and physical questions).**
The exact joint restricted full-error optimum, an attaining restricted
channel and any bound strictly above the inherited applicable maximum
are not determined by (JG.10). They require one joint full law satisfying
(JG.50) and a matching lower proof for that class. Sharp branch-mass
constants and a classification of arbitrary quantum-output measurable
channels remain outside the particular reduced-channel theorem.
An actual permitted native acquisition/storage/actuation and absorbing
first-failure timing interface must still supply Definition 8.2's
operations and correspondence, or establish a failure under an explicitly
defined original resource class. No global native impossibility follows
from either the conditional Schur closure or the live bottleneck.

All ordinary arguments retain their stated conditional status. Neither
source identity nor these proofs assert a new kernel result, whole-channel
optimizer uniqueness, physical efficiency, quantum capacity formula,
unconditional-prefix optimum, general neural-network or empirical-learning
claim. The continuing original threshold and native-control questions
remain active; this finite joint application is a bounded contribution.

[CG]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[ZG]: FIB_NATIVE_EXPLICIT_ZERO_TRANSFER_LOSS_GAP.md

## 追加锚（本行以下为增补区）
