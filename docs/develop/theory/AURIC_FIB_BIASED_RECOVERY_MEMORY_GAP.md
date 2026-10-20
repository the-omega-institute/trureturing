# AURIC FIB biased recovery: a quantitative memory gap

> This volume is an ordinary mathematical reference input. Its Markdown uses
> the `generic-v1` source convention. Established text is preserved under
> append-only continuation through the permanent append anchor. Statements
> and proofs here carry no Lean/kernel certification.

## 1. The measured model and its recovery interface

**Assumption 1.1 (Fixed instrument).** Let $H=\mathbb C^5$, let
$0<\eta<1$, and put $r=1-\eta$ and $q=2^{-1/2}$. In the original
orthonormal basis $e_0,\ldots,e_4$ define the isometric encoding

$$
\begin{aligned}
b_0&=\sqrt r\,e_0+\sqrt\eta\,e_3,&
b_1&=\sqrt r\,e_1+\sqrt\eta\,e_4,& b_2&=e_2,\\
B|i\rangle&=b_i,& \iota(X)&=BXB^\dagger,& R&=B\mathbb C^3.
\end{aligned}
\tag{1.1}
$$

The actual measured branches, with labels $0,1$ in the unrotated
orthonormal environment basis, are

$$
\begin{aligned}
A_0&=|b_0\rangle\langle e_0|+q|b_1\rangle\langle e_2|
             +|b_2\rangle\langle e_4|,\\
A_1&=|b_0\rangle\langle e_1|+q|b_1\rangle\langle e_2|
             +|b_2\rangle\langle e_3|.
\end{aligned}
\tag{1.2}
$$

Repeat this instrument a fixed finite number $n\ge0$ of times. Each step
uses a fresh pure environment, acquires its actual label and discards the
environment. Only classical processing is allowed between steps. There
is no retained quantum environment, intermediate quantum control,
postselection, access to an external reference, or additional
input-dependent side information. The target is $\iota$ on the entire
complex qutrit algebra, amplified by the identity on every untouched
finite reference. Identity on arbitrary full-$H$ inputs is not the task.
These are the assumptions of [Five Window, §§40–41][FW], with its
Definition 24.1 fixing the selected lift rather than just a population law.

**Definition 1.2 (Histories and Born weights).** In chronological order
$h=(j_1,\ldots,j_n)\in\mathscr H_n:=\{0,1\}^n$, use

$$
\begin{gathered}
A_jB=BL_j,\qquad L_j=U_jD_j,\\
U_0=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad
U_1=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix},\\
D_0=\operatorname{diag}(\sqrt r,\sqrt\eta,q),\qquad
D_1=\operatorname{diag}(\sqrt\eta,\sqrt r,q),\\
M_h=L_{j_n}\cdots L_{j_1}=P_hF_h,\qquad
P_h=U_{j_n}\cdots U_{j_1},\qquad
F_h=\operatorname{diag}(f_{h,0},f_{h,1},f_{h,2}).
\end{gathered}
\tag{1.3}
$$

Empty products are identities. The polar recursion of [Five Window,
Theorem 40.3][FW] is

$$
P_{hj}=U_jP_h,\qquad F_{hj}=P_h^\dagger D_jP_hF_h.
\tag{1.4}
$$

Thus all $f_{h,i}$ are strictly positive and
$\sum_hF_h^2=I_3$. Each is a product of $n$ entries chosen from
$\sqrt\eta,\sqrt r,q$. For a referenced input density $\rho$ the actual
history law is

$$
p_h(\rho)=\operatorname{Tr}[(F_h^2\otimes I)\rho]>0.
\tag{1.5}
$$

In particular the first-label probability is
$r\rho_{00}+\eta\rho_{11}+\rho_{22}/2$ after taking the reduced qutrit
density. No uniform distribution on histories is part of this model.
The unnormalized branch map $X\mapsto BP_hF_hXF_hP_h^\dagger B^\dagger$
already contains the Born weights; multiplying it by another history
probability would change the channel.

**Assumption 1.3 (Complete conditional terminal record).** A shared seed
$S$ has probability law $\mu$ on a standard Borel space and is independent
of the input and the acquired instrument labels. This independence is
possible because the quantum instrument has no seed-dependent feedback.
The seed is supplied without charge to the classical processor and
terminal decoder. For almost every $s$, the complete remaining terminal
view has a common measurable labeling $Y\in[W]=\{1,\ldots,W\}$, with
arbitrary measurable stochastic rows $q_s(y\mid h)$. The decoder assigned
to $(s,y)$ is a measurable full-$H$ CPTP map
$\mathcal D_{s,y}:M_5\to M_5$.

Every additional decoder-visible history-dependent program choice,
archive, buffer or metadata is included jointly in $Y$. Discarded
private randomness is averaged into the stochastic kernel or the CPTP
map. A history-correlated seed is not an independent free seed. The
bound $W$ is an essential conditional alphabet bound, shared across all
histories for each seed; it is neither an average support size nor an
entropy bound. Known $\eta,n$, deterministic clocks, fixed control
specifications, and label acquisition and communication are separate
resources, as in [Environment Record Memory, Definition 1.5][ERM] and
[Five Window, Assumption 41.1][FW].

A terminal kernel may use unrestricted intermediate classical memory.
An online peak bound additionally bounds the complete persistent
classical state at every cut, conditionally on the free seed. Such an
online protocol is a subclass of the terminal model, because all its
internal trajectories can be summed into $q_s(y\mid h)$. Neither model
counts only a selected register while leaving a decoder-visible archive
unaccounted for.

**Definition 1.4 (Averaged error).** The recovered channel and its
unhalved diamond error are

$$
\begin{aligned}
\Lambda(X)&=\int\sum_{h\in\mathscr H_n}\sum_{y=1}^W
 q_s(y\mid h)\,
 \mathcal D_{s,y}(BP_hF_hXF_hP_h^\dagger B^\dagger)\,\mu(ds),\\
\varepsilon&=\|\Lambda-\iota\|_\diamond.
\end{aligned}
\tag{1.6}
$$

The finite-dimensional integral is entrywise. Positivity, trace
preservation and complete positivity pass through the sum and integral,
using normalized rows and $\sum_hF_h^2=I_3$. The diamond norm is the
supremum of the amplified trace-norm ratio over arbitrary complex input
operators and all finite references. In particular it is unhalved, and
$\varepsilon$ is the error of the averaged channel, not the average of
individual seed errors.

## 2. The supplied optimum and a positive witness

**Definition 2.1 (Optimum and witness convention).** Reuse exactly the
all-history optimum of [Five Window, Theorem 40.5][FW]: the infimum
$e_*(\eta,n)$ of the error over one arbitrary full-$H$ terminal CPTP
map for each actual history. Its supplier gives

$$
\begin{gathered}
C_{n,ij}=\sum_h f_{h,i}f_{h,j},\qquad
C_n=\begin{pmatrix}1&A_n&B_n\\A_n&1&B_n\\B_n&B_n&1\end{pmatrix},\\
a=2\sqrt{\eta r},\quad \alpha=\sqrt{r/2},\quad\gamma=\sqrt{\eta/2},\\
A_0=B_0=1,\quad A_{n+1}=aB_n,\quad
B_{n+1}=\alpha A_n+\gamma B_n,\\
Q_n(w)=\sum_{i<j}(1-C_{n,ij})w_iw_j,\qquad
 e_*(\eta,n)=4\max_{w\in\Delta_3}Q_n(w),\\
x=1-A_n,\quad y=1-B_n,\qquad
 e_*(\eta,n)=
 \begin{cases}x,&x\ge2y,\\4y^2/(4y-x),&x<2y.\end{cases}
\end{gathered}
\tag{2.1}
$$

Here $\Delta_3$ is the probability simplex: $w_i\ge0$ and
$\sum_iw_i=1$. In particular $w$ is a probability vector, not the vector
of amplitudes. The referenced witness has amplitudes $\sqrt{w_i}$:

$$
\psi_w=\sum_i\sqrt{w_i}|i\rangle|i\rangle_Z,\qquad
\omega_w=|\psi_w\rangle\langle\psi_w|,\qquad
\Psi_w=(B\otimes I_Z)\psi_w.
\tag{2.2}
$$

This reference is an error witness, never a decoder resource. The two
copies of $\sqrt{w_i}$ in an overlap calculation produce $w_i$, which
is why the coefficients below are $w_if_{h,i}$.

The attaining controller supplied by [Five Window, Theorems 40.3 and
41.3][FW] retains the accumulated permutation and applies the full-space
unitary $BP_h^\dagger B^\dagger+I_5-BB^\dagger$ once at termination.
It realizes $\iota\mathcal E_n$, where $\mathcal E_n(X)=C_n\circ X$.
The supplied reachable-set and exact necessity arguments give

$$
m_0=1,\qquad m_1=2,\qquad m_2=4,\qquad m_n=6\quad(n\ge3).
\tag{2.3}
$$

These are also the optimum-attaining online peak widths. For the short
horizons, fixed time-dependent injections of the reachable prefix sets
into the final set give that peak; it is not necessary to reserve all
six states before they are reachable. The reachable sets are also owned
by [Environment Record Memory, Theorems 4.1 and 5.1][ERM]. They depend
on the actual permutations, not on $\eta$. The present quantitative
argument uses these suppliers without replacing their error optimum.

**Theorem 2.2 (A supported optimum witness and its scale).** One can
choose a maximizing $w$ in (2.1) whose active set
$I=\{i:w_i>0\}$ has size at least two. For any such choice set

$$
\nu=\min(\eta,1-\eta),\qquad
w_{\min}=\min_{i\in I}w_i,\qquad
k=\min_{h\in\mathscr H_n,\ i\in I}w_if_{h,i}.
\tag{2.4}
$$

Then $k\ge w_{\min}\nu^{n/2}>0$. A specific choice is
$w=(1/3,1/3,1/3)$ when $n=0$ or $\eta=1/2$; otherwise take
$(1/2,1/2,0)$ if $x\ge2y$, and

$$
w=\frac{(y,y,2y-x)}{4y-x}\quad\text{if }x<2y.
\tag{2.5}
$$

Proof. The witness maximization and its reduction to
$\max_{0\le t\le1}\{4yt-(4y-x)t^2\}$ are part of the optimum supplier
(40.11)–(40.12). The boundary maximizer $t=1$ and the interior maximizer
$t=2y/(4y-x)$ give the displayed choices by taking
$w_0=w_1=t/2$ and $w_2=1-t$. In the interior case $y>0$, $4y-x>0$
and $2y-x>0$, so all three coordinates are active. At the seam $x=2y$
use the two-coordinate choice and exclude its zero coordinate from
$w_{\min}$ and $k$.

For $n\ge1$ and $\eta\ne1/2$, the recurrence gives $A_n\le a<1$.
Consequently $Q_n(1/2,1/2,0)>0$, whereas every simplex vertex has value
zero. Every maximizer in this case has at least two active coordinates.
At the zero-error parameters the objective vanishes identically; a
nonvertex choice must be made explicitly, and the stated uniform choice
works. It is false that every maximizer there is nonvertex.

Finally $0<\nu\le1/2$, so each factor in (1.4) is at least
$\sqrt\nu$, including the factor $q$. Hence $f_{h,i}\ge\nu^{n/2}$.
There are finitely many histories and active indices, giving (2.4) with
a strictly positive minimum. $\square$

## 3. Quantifying coherent saturation on the full output space

**Theorem 3.1 (Exact deficit and operational normalization).** Fix the
witness of Theorem 2.2. Write $c_{h,i}=w_if_{h,i}$ for $i\in I$ and
$t_h=\sum_{i\in I}c_{h,i}$. For each full-$H$ CPTP map $\mathcal D$
there is an intrinsic nonnegative deficit $d_h(\mathcal D)$ with the
following description. For any Stinespring isometry
$V:H\to H\otimes E$ representing $\mathcal D$, put

$$
z_{h,i}=(\langle b_i|\otimes I_E)VBP_h|i\rangle,\qquad
G_h(\mathcal D)=\left\|\sum_{i\in I}c_{h,i}z_{h,i}\right\|^2,
\qquad d_h(\mathcal D)=t_h^2-G_h(\mathcal D).
\tag{3.1}
$$

Then

$$
\begin{aligned}
d_h(\mathcal D)
 &=t_h\sum_{i\in I}c_{h,i}(1-\|z_{h,i}\|^2)\\
 &\quad+\sum_{\substack{i<j\\i,j\in I}}
        c_{h,i}c_{h,j}\|z_{h,i}-z_{h,j}\|^2\ \ge0.
\end{aligned}
\tag{3.2}
$$

For the protocol (1.6), the measurable averaged deficit

$$
\Delta=\int\sum_{h,y}q_s(y\mid h)d_h(\mathcal D_{s,y})\,\mu(ds)
\tag{3.3}
$$

satisfies $\varepsilon\ge e_*(\eta,n)+2\Delta$.

Proof. The finite-dimensional Stinespring representation [Stinespring][STI]
can be obtained by stacking Kraus operators; trace preservation gives
$V^\dagger V=I_5$. No environmental dimension two is imposed on this
terminal decoder. The vectors $VBP_h|i\rangle$ are unit vectors, so
$\|z_{h,i}\|\le1$ even if the decoder leaks outside $R$. Apply
$V\otimes I_Z$ to the unnormalized branch vector
$\sum_i\sqrt{w_i}f_{h,i}BP_h|i\rangle|i\rangle_Z$ and project the
output-reference factors onto $\Psi_w$. The remaining environment
vector is precisely $\sum_iw_if_{h,i}z_{h,i}$. This proves that $G_h$
is the branch contribution to the target overlap, intrinsically a
linear functional of the decoder's Choi matrix. In particular $G_h$
and $d_h$ are continuous in that matrix and measurable in every allowed
decoder family.

For complex vectors and positive real $c_i$,

$$
\sum_{i<j}c_ic_j\|z_i-z_j\|^2
 =\left(\sum_i c_i\right)\sum_i c_i\|z_i\|^2
  -\left\|\sum_i c_i z_i\right\|^2.
\tag{3.4}
$$

Expanding both sides using $2\operatorname{Re}\langle z_i,z_j\rangle$
proves this identity with all complex phases intact. Adding the first
sum in (3.2) proves that formula and its nonnegativity.

Let $G=\langle\Psi_w|(\Lambda\otimes\operatorname{id}_Z)
(\omega_w)|\Psi_w\rangle$. Kernel normalization, (3.1) and the
history Gram formula give

$$
\begin{aligned}
G&=\sum_h t_h^2-\Delta=w^{\mathsf T}C_nw-\Delta,\\
w^{\mathsf T}C_nw
 &=1-2\sum_{i<j}(1-C_{n,ij})w_iw_j=1-e_*/2.
\end{aligned}
\tag{3.5}
$$

The actual output in this test is a density operator by completeness
and TP. The two-outcome measurement onto $\Psi_w$ gives ideal
probabilities $(1,0)$ and actual probabilities $(G,1-G)$. Its classical
trace-norm difference is $2(1-G)$. Trace-norm contraction for this
measurement and admissibility of $\omega_w$ in the diamond supremum
therefore yield

$$
\varepsilon\ \ge\ 2(1-G)\ =\ e_*+2\Delta.
\tag{3.6}
$$

This factor two uses the unhalved norm. The measurement only witnesses
error; it grants no reference access to the protocol.

For completeness, the full-space interface is also compatible with
the isometry/retraction supplier [Approximate Online Recovery Memory,
Lemma 3.1 and Theorem 3.2][APP]. With this volume's $B$, its formula is

$$
\mathcal C_B(T)=B^\dagger TB+
 \operatorname{Tr}[(I_5-BB^\dagger)T]|0\rangle\langle0|.
\tag{3.7}
$$

The same proof applies for every present $\eta$: Kraus operators are
$B^\dagger$ and $|0\rangle\langle v_a|$ for an orthonormal basis of
$R^\perp$, and their squared effects sum to $I_5$. Thus
$\mathcal C_B\iota=\operatorname{id}_3$. Conjugation by $B\otimes I_Z$
preserves all nonzero singular values, including on complex operators.
Consequently $\|\iota\Phi\|_\diamond=\|\Phi\|_\diamond$, and
postcomposition of $\Lambda-\iota$ by $\mathcal C_B$ cannot increase
error. Conversely qutrit decoders extend by
$\iota\mathcal D\mathcal C_B$ with equal encoded error. These facts
explain the full-space and qutrit norm interface; the deficit proof
itself already uses the arbitrary full-$H$ decoder and does not assume
that its output stays in $R$. $\square$

**Theorem 3.2 (Near-saturation coherence and a pair penalty).** For a
fixed decoder $\mathcal D$, choose its isometry $V$ and a fixed index
$i_0\in I$, and write $v_h=z_{h,i_0}$. For every $i\in I$,

$$
\|VBP_h|i\rangle-b_i\otimes v_h\|
 \le \frac{2\sqrt{d_h(\mathcal D)}}{k},\qquad \|v_h\|\le1.
\tag{3.8}
$$

If $P_h\ne P_{h'}$, one common full-$H$ decoder necessarily satisfies

$$
d_h(\mathcal D)+d_{h'}(\mathcal D)\ge\frac{k^2}{32}.
\tag{3.9}
$$

Proof. Each summand of (3.2) is nonnegative. Since $c_{h,i}\ge k$
and $t_hc_{h,i}\ge k^2$, it follows that

$$
1-\|z_{h,i}\|^2\le d_h/k^2,\qquad
\|z_{h,i}-z_{h,i_0}\|^2\le d_h/k^2\quad(i\ne i_0).
\tag{3.10}
$$

The second inequality is zero when $i=i_0$. The orthogonal projection
of $VBP_h|i\rangle$ onto $b_i\otimes E$ is
$b_i\otimes z_{h,i}$; its orthogonal remainder has squared norm
$1-\|z_{h,i}\|^2$. The triangle inequality and (3.10) bound the
remainder and the replacement of $z_{h,i}$ by $v_h$ by
$\sqrt{d_h}/k$ each. This proves (3.8). Full-space leakage is included
in that orthogonal remainder.

Use the same $V$ for $h,h'$, and let $c=\langle v_h,v_{h'}\rangle$,
which may be complex. Preservation of inner products by $V$ and $B$
gives, for $i,j\in I$,

$$
\left|(P_h^\dagger P_{h'})_{ij}-c\delta_{ij}\right|
 \le\frac{2(\sqrt{d_h}+\sqrt{d_{h'}})}{k}.
\tag{3.11}
$$

Indeed, set $u=VBP_h|i\rangle$, $u'=VBP_{h'}|j\rangle$,
$x=b_i\otimes v_h$ and $x'=b_j\otimes v_{h'}$. The identity
$\langle u,u'\rangle-\langle x,x'\rangle
=\langle u-x,u'\rangle+\langle x,u'-x'\rangle$, together with
$\|u'\|=1$ and $\|x\|\le1$, proves (3.11). There is no product of
the two approximation errors to discard.

Here is the source-specific separation used in (3.11). For every
nonidentity $Q\in S_3$, every two-element coordinate set $J$, and every
complex $c$,

$$
\|Q_{J,J}-cI_J\|_{\max}\ge\tfrac12,
\qquad \|T\|_{\max}:=\max_{i,j}|T_{ij}|.
\tag{3.12}
$$

If the two-by-two compression has a nonzero off-diagonal entry, that
entry is one, giving distance at least one. Otherwise the compression
is diagonal with entries zero or one. Both entries cannot be zero:
two distinct columns cannot both send their nonzero entry into the
one coordinate outside $J$. Both entries cannot be one: fixing two
coordinates of a three-point permutation fixes the third. Thus the
diagonal entries are zero and one, and
$1\le|c|+|1-c|$ proves (3.12), including complex scalars.

Choose any two active indices and apply (3.12) to
$Q=P_h^\dagger P_{h'}$. The maximum over $I$ in (3.11) is at least
that over the chosen pair. Therefore
$\sqrt{d_h}+\sqrt{d_{h'}}\ge k/4$. Squaring and using
$2\sqrt{d_hd_{h'}}\le d_h+d_{h'}$ gives
$k^2/16\le2(d_h+d_{h'})$, which is (3.9).

This quantitative scalar-compression obstruction follows the coherent
saturation argument in [Five Window, Theorem 41.2][FW]. The generic
Knill–Laflamme scalar cross-compression criterion [Knill–Laflamme,
Theorem 3.2][KL] is its standard exact-correction antecedent. No
exact-correction condition is imposed directly on the unequal filters
$F_h$. Rather, optimal-reference saturation first forces approximate
coherent inversion of the actual permutations. $\square$

## 4. The explicit insufficient-memory inequality

**Theorem 4.1 (Fixed-parameter stochastic memory gap).** Fix
$\eta\in(0,1)$, finite $n$, and an integer $1\le W<m_n$. Choose $w,I,k$
as in Theorem 2.2. Every protocol satisfying Assumptions 1.1 and 1.3
has averaged unhalved diamond error

$$
\boxed{\displaystyle
\varepsilon\ \ge\ e_*(\eta,n)+\frac{k^2}{16W}
 \ \ge\ e_*(\eta,n)+\frac{w_{\min}^2\nu^n}{16W}
 \ >\ e_*(\eta,n).}
\tag{4.1}
$$

The same inequality holds for every online protocol with conditional
persistent peak width at most $W$ under those permissions. At $n=0$
the interval of admissible $W$ is empty.

Proof. From each of the $m_n$ reached permutation classes choose one
history, forming a fixed finite set $\mathscr R_n$. This selection
depends only on the instrument and horizon. It does not depend on a
seed or an input. The counts in (2.3) come from the unchanged generators
$U_0=(12)$ and $U_1=(021)$: length two reaches
$\{I,U_1U_0,U_0U_1,U_1^2\}$, length three reaches all of $S_3$, and
left multiplication by either generator preserves all of $S_3$.
This is the reached-set supplier, not an extrapolation from sampled
histories.

For each fixed seed where the conditional labeling is valid, choose
for every $h\in\mathscr R_n$ a maximizing row entry
$q_s(y_h\mid h)\ge1/W$. There are more representatives than labels,
so two representatives $h,h'$ with distinct permutations have the same
chosen label $y$. Their common decoder is $\mathcal D_{s,y}$, and
(3.9) applies to it. Dropping all other nonnegative terms gives the
pointwise estimate

$$
\begin{aligned}
D(s)&:=\sum_{g\in\mathscr H_n}\sum_{z=1}^W
 q_s(z\mid g)d_g(\mathcal D_{s,z})\\
&\ge q_s(y\mid h)d_h(\mathcal D_{s,y})
    +q_s(y\mid h')d_{h'}(\mathcal D_{s,y})\\
&\ge\frac{d_h(\mathcal D_{s,y})+d_{h'}(\mathcal D_{s,y})}{W}
 \ge\frac{k^2}{32W}.
\end{aligned}
\tag{4.2}
$$

Sparse rows, tied maxima and zero weights elsewhere cause no problem.
The factor $1/W$ comes from the actual stochastic row maxima; replacing
stochastic processing by a deterministic-policy claim is unnecessary.

The intrinsic function $D(s)$ is measurable by Theorem 3.1. Although
(4.2) is established for every seed using some pair and some dilation,
neither the pair nor the dilation has to be selected measurably: the
inequality concerns the same measurable total $D(s)$ in every case.
Its constant $k^2/(32W)$ is independent of $s$. Integrating this
pointwise bound gives $\Delta\ge k^2/(32W)$. Combine (3.6) with
Theorem 2.2 to obtain (4.1).

This integrates a single fixed witness's nonnegative deficit. It does
not choose a favorable seed, infer equality of per-seed diamond errors,
or commute an infimum with a seed average. The online assertion follows
by the terminal relaxation in Assumption 1.3. $\square$

**Theorem 4.2 (Parameter qualifications and negative boundaries).**
The inequality includes $\eta=1/2$, excludes $\eta=0,1$, and depends
on the active support of the chosen optimum witness. With the uniform
zero-error witness its explicit half-parameter increment is
$2^{-n}/(144W)$. The support restriction and full complex compression
in Theorem 3.2 cannot be dropped.

Proof. At half all $D_j=2^{-1/2}I_3$, hence
$F_h=2^{-n/2}I_3$, $e_*=0$, and the chosen uniform witness has
$k=2^{-n/2}/3$. Formula (4.1) gives the stated increment, still for
$W<m_n$. At zero horizon there is one empty history and one reachable
permutation, so no positive integer violates the attaining alphabet.
At either excluded endpoint a diagonal entry of a one-step $D_j$
vanishes. Consequently a claimed positive minimum over every active
coordinate and every history can fail; this proof does not extend
endpoint necessity by continuity of the optimum.

The vertex $w=(1,0,0)$ is an optimum witness at half. Yet
$U_0\ne I_3$ fixes coordinate zero, and its compression to that one
coordinate is the scalar one. Thus a vertex witness cannot support
(3.12). Zero coordinates at $x=2y$ must be removed from the minimum,
rather than used to declare $k=0$ for an otherwise valid two-coordinate
witness. Near that seam a small positive third weight can make the
three-coordinate bound small; no optimality of these constants is
asserted. Along with the factor $\nu^n$, this explains why (4.1) is a
fixed-parameter estimate rather than a uniform estimate in the horizon
or across the interior parameter interval. $\square$

## 5. Exact finite-seed convexification

**Theorem 5.1 (At most 217 free seed values).** For fixed
$\eta,n$ and finite $W\ge1$, let $\mathcal K_W$ be the set of
seedless terminal-$W$ recovery channels (1.6). The channels achievable
with arbitrary independent standard Borel shared seeds are exactly
$\operatorname{conv}(\mathcal K_W)$. This set is compact. Every one
of its channels, including an error minimizer, is achieved by an
independent seed taking at most $217$ values, with at most $W$
terminal record values conditionally on each seed.

Proof. Parameterize a seedless protocol by one stochastic row in
$\Delta_W$ for each of the $2^n$ histories and by one full-$H$ decoder
Choi matrix for each of the $W$ labels. In the output-first convention
these decoder matrices belong to

$$
\mathcal J_5=\{J\in\operatorname{Herm}(H\otimes H):
                   J\succeq0,\ \operatorname{Tr}_{\rm out}J=I_5\}.
\tag{5.1}
$$

The Choi representation [Choi][CHOI] identifies these precisely with
full-$H$ CPTP maps. The set is closed, and $\operatorname{Tr}J=5$
bounds every eigenvalue and therefore its norm. It is compact. The
parameter space $(\Delta_W)^{2^n}\times\mathcal J_5^W$ is compact,
and the resulting channel entries are finite sums of products of its
coordinates and fixed branch entries. Thus its continuous image
$\mathcal K_W$ is compact. Boundary rows and arbitrary nonunitary
channels are included.

Count the dimension of the resulting recovery channel, not the
dimension of its decoder parameters. A Hermiticity-preserving map
$M_3\to M_5$ has a Hermitian Choi matrix on $\mathbb C^5\otimes
\mathbb C^3$, of real dimension $15^2=225$. The trace-preserving
condition is $\operatorname{Tr}_{\rm out}J=I_3$, giving nine
independent real affine constraints. Independence follows because
$J=(I_5/5)\otimes T$ maps to any given
$T\in\operatorname{Herm}(\mathbb C^3)$ under partial output trace.
The ambient trace-preserving affine space consequently has dimension

$$
225-3^2=216.
\tag{5.2}
$$

Its channel subset has that affine dimension as well, since
$(I_5/5)\otimes I_3$ is positive definite and remains positive under
sufficiently small Hermitian perturbations with zero partial trace.
The possibly smaller affine span of $\mathcal K_W$ only improves an
upper bound.

Apply the generic finite-dimensional Carathéodory theorem [Rockafellar,
Theorem 17.1][ROCK]: a point in a convex hull in dimension at most
$216$ is a convex combination of at most $217$ points. Its elementary
reduction removes one positive coefficient from any longer finite
combination using an affine dependence, while preserving the point and
nonnegativity; iteration gives the bound. In particular
$\operatorname{conv}(\mathcal K_W)$ is the continuous image of
$\Delta_{217}\times\mathcal K_W^{217}$, padding with zero
coefficients when necessary, and is compact rather than merely having
a compact closure.

For any allowed measurable seed family, its channel barycenter lies
in this convex hull. If it did not, finite-dimensional strict
separation from the compact convex hull would give an affine functional
whose value at the barycenter exceeds its maximum on $\mathcal K_W$.
Integrating that functional over the seed contradicts this inequality.
Conversely any finite convex combination is implemented by sampling
its index as a seed, independently of the input and instrument,
and using the corresponding seedless kernel and full-$H$ decoders.
Carathéodory therefore gives the exact same recovery channel with at
most $217$ seed values. The diamond error is a continuous function of
the channel in this finite-dimensional space, so it attains its minimum
on the compact convex hull.

The preserved resource is conditional $W$. The free seed is still
visible, and the complete information is $(S,Y)$. The cardinality assertion uses this declared free-seed convention;
no entropy, joint charged-memory or hardware-cost conclusion is asserted. The strict gap in
Theorem 4.1 was proved before convexification and does not depend on
compactness or norm convexity. $\square$

**Theorem 5.2 (Specified compact finite controllers).** Fix $n$ and a
complete state alphabet $[W]$. Consider exactly the controllers with
an initial distribution $\pi$ on $[W]$, stochastic transition rows
$T_t(m'\mid m,j)$ for $t=1,\ldots,n$ and the currently acquired label
$j\in\{0,1\}$, and a full-$H$ CPTP decoder $\mathcal D_m$ at
termination. The deterministic time $t$ is supplied by the declared
clock. All run-dependent information available at the next step is
contained in $m$. Arbitrary independent shared-seed mixtures of this
class have compact channel image and admit the same $217$-value seed
reduction, preserving peak width $W$.

Proof. For one seedless controller the probability of a classical
trajectory $m_0,\ldots,m_n$ given $h$ is

$$
\pi(m_0)\prod_{t=1}^nT_t(m_t\mid m_{t-1},j_t).
\tag{5.3}
$$

Summing these products over trajectories ending at $m$ gives exactly
the terminal kernel $q(m\mid h)$ in (1.6). The instrument is fixed
and there are no intermediate quantum operations, so these are also
the coefficients of its actual recovered channel; there is no separate
quantum feedback law to substitute. Initial and transition rows form
a finite product of closed simplices, and decoder matrices form
$\mathcal J_5^W$. The channel is a continuous polynomial image of
this compact parameter space. Apply the proof of Theorem 5.1 to that
image in the same $216$-dimensional channel space. Each retained point
is a controller of this exact class, so choosing among at most $217$
such controllers by a free independent seed preserves all its stage
widths.

Smaller stage alphabets can be padded to $[W]$. Restrictions such as
fixed homogeneous transitions can also be imposed when they define a
closed subset and the model corresponds exactly to that subset.
Correlated private randomness persisting between steps must be in the
state or in the explicitly independent shared seed; otherwise (5.3)
need not describe it. A transition depending on an unrecorded full
prefix is outside this complete-state controller model. Compactness of
the terminal relaxation alone does not establish an online
implementation with the same width. $\square$

## 6. A nonuniform-horizon boundary in the terminal model

**Theorem 6.1 (Three terminal values can approach the optimum).** Fix
$\eta\in(0,1)\setminus\{1/2\}$. There are deterministic terminal
kernels with $W=3$ and full-$H$ CPTP decoders such that their errors
$\widehat\varepsilon_n$ obey

$$
\widehat\varepsilon_n-e_*(\eta,n)\longrightarrow0
\quad(n\to\infty).
\tag{6.1}
$$

For every $n\ge3$ this width is strictly below $m_n=6$. Thus no
positive excess-error lower bound uniform in $n\ge3$ exists even at
this fixed biased parameter for terminal widths $3,4,5$.

Proof. For each actual history let $\ell(h)$ be a coordinate maximizing
$f_{h,i}$, with ties broken in a fixed order, and output only
$Y=\ell(h)$. Use the full-space replacement channel
$\mathcal D_i(T)=\operatorname{Tr}(T)|b_i\rangle\langle b_i|$.
It is CPTP on all $H$. The resulting channel is

$$
\widehat\Lambda_n(X)=\sum_i X_{ii}\sum_{j=0}^2
 a_{ji}^{(n)}|b_j\rangle\langle b_j|,\qquad
 a_{ji}^{(n)}=\sum_{h:\ell(h)=j}f_{h,i}^2.
\tag{6.2}
$$

Indeed $\operatorname{Tr}(P_hF_hXF_hP_h^\dagger)
=\sum_i f_{h,i}^2X_{ii}$, also for complex $X$. The columns of $a$
are probability vectors. If $\ell(h)=j\ne i$, then
$f_{h,i}\le f_{h,j}$, whence

$$
1-a_{ii}^{(n)}=\sum_{h:\ell(h)\ne i}f_{h,i}^2
 \le\sum_{j\ne i}\sum_{h:\ell(h)=j}f_{h,i}f_{h,j}
 \le\sum_{j\ne i}C_{n,ij}.
\tag{6.3}
$$

This is a likelihood classifier for the initial basis coordinate using
the actual history, with no fair-history surrogate.

Let $\mathcal P(X)=\sum_iX_{ii}|i\rangle\langle i|$ be qutrit
dephasing. For a complex referenced operator $X$ with diagonal blocks
$X_{ii}$, the output difference
$(\widehat\Lambda_n-\iota\mathcal P)\otimes\operatorname{id}(X)$
is $\sum_{j,i}(a_{ji}^{(n)}-\delta_{ji})
|b_j\rangle\langle b_j|\otimes X_{ii}$. Its trace norm is bounded
by

$$
\max_i\sum_j|a_{ji}^{(n)}-\delta_{ji}|\,
 \sum_i\|X_{ii}\|_1
 \le2\max_i(1-a_{ii}^{(n)})\|X\|_1.
\tag{6.4}
$$

The last inequality uses complete trace-norm contractivity of the
pinching map, whose block-diagonal output has norm
$\sum_i\|X_{ii}\|_1$. It holds for complex inputs by the amplified
CPTP contraction argument of [Five Window, Lemma 22.1][FW]. Basis inputs
show that the first maximum is also the exact diamond norm of this
classical channel difference. In particular (6.3) gives convergence
$\widehat\Lambda_n\to\iota\mathcal P$ in diamond norm, because
$A_n,B_n\to0$ at every fixed biased interior parameter by
[Five Window, Proposition 40.7][FW].

The same supplier gives $\mathcal E_n\to\mathcal P$ and
$e_*(\eta,n)\to4/3$. Norm continuity, or the triangle inequality
against the supplied attaining channel $\iota\mathcal E_n$, now gives

$$
0\le\widehat\varepsilon_n-e_*(\eta,n)
 \le\|\widehat\Lambda_n-\iota\mathcal P\|_\diamond
      +\|\mathcal E_n-\mathcal P\|_\diamond\longrightarrow0.
\tag{6.5}
$$

The first inequality is all-history optimality. At each finite
$n\ge3$, Theorem 4.1 still gives a strictly positive gap for this
classifier. There is no contradiction: its lower bound may shrink
with $n$. Padding the three labels gives the same counterexample to
uniform terminal bounds for widths four and five.

This kernel uses the full history to compute $\ell(h)$ before
termination. It establishes a terminal-alphabet upper bound with
unrestricted intermediate classical memory; it does not supply a
three-state online controller. At $\eta=1/2$ the histories carry no
information about the initial basis coordinate, and the decay used in
(6.3) fails. Nor does this proof decide uniform-in-horizon gaps for
$W=1,2$ or for the separately constrained online classes. $\square$

## 7. Suppliers and the mathematical scope

**Definition 7.1 (Source-relative content and attribution).** The
optimum curve, its weighted-reference witness, the actual positive
history recursion and the optimum-attaining controller are reused from
[Five Window, Theorems 40.3–40.5][FW]. Its Theorems 41.2–41.4 supply
the qualitative necessity and fixed-parameter compactness gap.
Theorems 3.2 and 4.1 here quantify that coherent equality obstruction;
Theorem 5.1 specializes generic convex geometry to the unchanged
stochastic recovery interface; Theorem 6.1 supplies a terminal-model
boundary. These are `repo-derived` mathematical syntheses, without a claim
of literature priority.

The general isometric decoder representation is credited to W. F.
Stinespring, *Positive Functions on C*-Algebras*, Proc. Amer. Math. Soc.
6, 211–216, DOI [10.1090/S0002-9939-1955-0069403-4][STI]; the explicit
Schrödinger representation is also given in Kretschmann, Schlingemann
and Werner, *The Information-Disturbance Tradeoff and the Continuity of
Stinespring's Representation*, [quant-ph/0605009v1, §III.A,
(10)–(11)][KSW]. No Stinespring continuity theorem supplies the constants
in (3.8)–(4.1); those follow from the displayed deficit identity.

The positive Choi description used in (5.1) is credited to M.-D. Choi,
*Completely positive linear maps on complex matrices*, Linear Algebra
Appl. 10, 285–290, DOI [10.1016/0024-3795(75)90075-0][CHOI]. The
finite convex-combination reduction is the standard Carathéodory
theorem, for example R. T. Rockafellar, *Convex Analysis*, Theorem 17.1,
DOI [10.1515/9781400873173][ROCK]. These generic tools are
`literature-attested` ingredients of the proofs, rather than new
standalone results. The exact scalar-compression antecedent is E.
Knill and R. Laflamme, *Theory of Quantum Error-Correcting Codes*,
[quant-ph/9604034v1, Theorem 3.2, (19)–(20)][KL]. Generic polar-fidelity
optimality is due to Gregoratti and Werner, *Quantum Lost and Found*,
[quant-ph/0209025v1, Proposition 8][GW]; it does not by itself supply
the biased weighted-reference diamond optimum.

The literature scope is the cited generic suppliers and the linked
repository results; no exhaustive external search for this precise
quantitative constant or the $217$-seed specialization is asserted.
There is no `suspected-novel` or global-priority classification.

**Assumption 7.2 (Limits of interpretation).** Every gap assertion uses
the actual unrotated instrument (1.2), finite $n$, interior $\eta$, the
encoded qutrit and full complex phase, independent shared seeds, the
complete conditional terminal view, and averaged unhalved diamond
error with untouched references. No conclusion is drawn for arbitrary
quantum lifts sharing a classical population law, rotated measured
Kraus labels, intermediate quantum feedback, hidden decoder-visible
history or endpoint filters. None is a physical, Hamiltonian, QFT,
entropy-rate or kernel-verified claim.

The fixed-angle problem in [Approximate Online Recovery Memory,
§§9, 16 and 21][APP] has a different measured instrument, scalar
restricted effects, phase-sensitive unitary histories and prescribed
positive-error online peak questions with $n^{3/2}$ growth bounds. Here
$\eta$ is a population parameter and the unrotated accumulated
permutation has at most six values; the unequal positive filters
create an unavoidable optimum error. The fixed-parameter excess above
that optimum, its vanishing terminal boundary in Theorem 6.1, and the
finite-seed convexification do not transfer those fixed-angle
asymptotics to this model.

[FW]: AURIC_FIB_FIVE_WINDOW_QUANTUM_MEMORY.md
[ERM]: AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md
[APP]: AURIC_FIB_APPROXIMATE_ONLINE_RECOVERY_MEMORY.md
[STI]: https://doi.org/10.1090/S0002-9939-1955-0069403-4
[CHOI]: https://doi.org/10.1016/0024-3795(75)90075-0
[ROCK]: https://doi.org/10.1515/9781400873173
[KSW]: https://arxiv.org/pdf/quant-ph/0605009v1
[KL]: https://arxiv.org/pdf/quant-ph/9604034v1
[GW]: https://arxiv.org/pdf/quant-ph/0209025v1

## 追加锚（本行以下为增补区）
