# AURIC FIB common-measurement compatibility, defect and recovery separation

## 1. States, common measurements and positive transports

**Convention 1.1 (Scope and suppliers).** All Hilbert spaces are finite-dimensional
and complex. A density matrix is positive semidefinite with trace one; strictly
positive means positive definite. A channel is a complex-linear completely
positive trace-preserving map (CPTP). Adjoint is denoted by $\dagger$,
$[A,B]=AB-BA$, and the unnormalized Frobenius norm is
$\|A\|_F^2=\operatorname{Tr}(A^\dagger A)$. The trace norm and operator norm
are $\|\cdot\|_1$ and $\|\cdot\|_{\mathrm{op}}$.

The root-fidelity and common measured-average definitions are those of
Theshani Nuradha, Hemant K. Mishra, Felix Leditzky and Mark M. Wilde,
*Multivariate Fidelities*, arXiv:2404.16101v3, [NMLW, Proposition 3.1, PDF p. 9;
equation (5.13), PDF p. 18; Definition 5.40, PDF p. 32, equation (5.90)][NMLW].
Their Proposition 5.44, PDF p. 34, equations (5.102)–(5.105), gives the
comparison $F_M\ge F_U$. These are **PDF equation numbers**; HTML equation
numbers differ. The positive-block SDP objective in their Proposition 5.10,
PDF equation (5.27), is a different optimization and is not used here.

The pairwise optimal-measurement and effect-eigenspace conditions are the
result of Christopher A. Fuchs and Carlton M. Caves, *Mathematical Techniques
for Quantum Communication Theory*, arXiv:quant-ph/9604001v1, [FC, §2, equations (7), (18)–(24)][FC], under their
finite-dimensional invertibility assumptions. The compatibility and
quantitative statements below are tuple deductions from that pairwise
interface, with their ordinary mathematical proofs supplied here. The
existing repository separation at $a=b=1/2$ is supplied by [SEP, Theorem 1.5][SEP]
and [PROBLEM]: $F_U<24/25\le F_M$, over every finite outcome count. That
existential separation is reused. No global priority assertion is attached
to the tuple deductions.

The actual instrument and exact retained-record results are supplied by
[REC]. Its precise input, reference, chronology and resource conventions
are retained in §§7–10. All proofs in this volume are ordinary
finite-dimensional mathematics; this volume supplies no Lean-kernel
certification, physical realization assertion or QFT conclusion.

**Definition 1.2 (One common finite POVM).** Fix integers $d\ge2$, $r\ge3$,
and strictly positive density matrices $\rho_0,\ldots,\rho_{r-1}$ on
$\mathbb C^d$. Put $q=\binom r2=r(r-1)/2$. A finite POVM is a family
$E=(E_x)_{x=1}^m$, for any finite $m\ge1$, satisfying
$E_x\succeq0$ and $\sum_xE_x=I_d$. Define

$$
\begin{aligned}
p_i(x)&=\operatorname{Tr}(E_x\rho_i),\\
F(\rho,\sigma)&=\|\sqrt\rho\sqrt\sigma\|_1,\\
C_{ij}(E)&=\sum_x\sqrt{p_i(x)p_j(x)},\\
\delta_{ij}(E)&=C_{ij}(E)-F(\rho_i,\rho_j),\\
F_U(\boldsymbol\rho)&=\frac1q\sum_{0\le i<j\le r-1}F(\rho_i,\rho_j),\\
F_M(\boldsymbol\rho)&=
\inf_{\substack{m\ge1,\ E_x\succeq0\\\sum_{x=1}^mE_x=I_d}}
\frac1q\sum_{0\le i<j\le r-1}C_{ij}(E),\\
\Delta(\boldsymbol\rho)&=F_M(\boldsymbol\rho)-F_U(\boldsymbol\rho),\\
G(E)&=\frac1q\sum_{i<j}C_{ij}(E)-F_U(\boldsymbol\rho)
     =\frac1q\sum_{i<j}\delta_{ij}(E).
\end{aligned}
\tag{1.1}
$$

The infimum is over **one POVM shared by every pair**, with arbitrary
finite outcome count. Separate pairwise choices do not define $F_M$.
The pairwise measurement representation [NMLW, Proposition 3.1,
PDF equation (3.2)][NMLW] gives $\delta_{ij}(E)\ge0$. Hence $\Delta\ge0$ and
$\Delta=\inf_EG(E)$. The same fidelity definitions apply to singular
density matrices when they occur as channel outputs in §§6–10; the
transport classification below assumes strict positivity.

**Definition 1.3 (Anchored positive transports).** For the fixed anchor
$\rho_0$, set

$$
T_i=\rho_0^{-1/2}
  (\rho_0^{1/2}\rho_i\rho_0^{1/2})^{1/2}\rho_0^{-1/2},
\qquad T_0=I_d.
\tag{1.2}
$$

Each $T_i$ is strictly positive and satisfies

$$
T_i\rho_0T_i=\rho_i,\qquad
\operatorname{Tr}(\rho_0T_i)=F(\rho_0,\rho_i).
\tag{1.3}
$$

Indeed $\rho_0^{1/2}T_i\rho_0^{1/2}$ is the positive square root of
$\rho_0^{1/2}\rho_i\rho_0^{1/2}$. Squaring proves the first identity;
taking the trace proves the second. Conversely any positive solution of
the first equation has that same congruence square root, proving
uniqueness. With the FC pair labels $(\rho_0,\rho_1)=(\rho_0,\rho_i)$,
our $T_i$ is their $N$ following equation (20), the inverse of their $M$
in equation (19); equivalently swap their two pair labels. This fixes
the direction of the probability ratios used below.

## 2. Residuals and finite-outcome attainment

**Theorem 2.1 (Exact anchored residual).** For every finite POVM in
Definition 1.2, delete its zero effects and put
$t_{ix}=\sqrt{p_i(x)/p_0(x)}$. These ratios are strictly positive. Then

$$
\delta_{0i}(E)=
\sum_x\frac{
\|\sqrt{E_x}(T_i-t_{ix}I_d)\sqrt{\rho_0}\|_F^2}{2t_{ix}}.
\tag{2.1}
$$

Consequently, simultaneous equality $\delta_{0i}(E)=0$ for all $i$ is
equivalent to

$$
\sqrt{E_x}T_i=t_{ix}\sqrt{E_x},\qquad
T_i\sqrt{E_x}=t_{ix}\sqrt{E_x}
\quad\text{for every nonzero effect and every }i.
\tag{2.2}
$$

Proof. Strict positivity of every state makes $p_i(x)>0$ for nonzero
$E_x\succeq0$. Let

$$
A_x=\sqrt{E_x}\sqrt{\rho_0},\qquad
B_{ix}=\sqrt{E_x}T_i\sqrt{\rho_0}.
$$

Cyclicity of trace and (1.3) give
$\|A_x\|_F^2=p_0(x)$ and $\|B_{ix}\|_F^2=p_i(x)$. Expanding gives

$$
\frac{\|B_{ix}-t_{ix}A_x\|_F^2}{2t_{ix}}
=\sqrt{p_0(x)p_i(x)}-
 \operatorname{Re}\operatorname{Tr}(A_x^\dagger B_{ix}).
$$

The sum of the final traces is
$\operatorname{Tr}(\rho_0\sum_xE_xT_i)
 =\operatorname{Tr}(\rho_0T_i)=F(\rho_0,\rho_i)$.
This proves (2.1). Every summand is nonnegative with a positive
denominator. Vanishing is therefore equivalent to vanishing of each
matrix residual. Cancel the invertible $\sqrt{\rho_0}$ on the right
and take adjoints to obtain (2.2). This is the repeated anchored
application of the FC pairwise equality relation. $\square$

**Theorem 2.2 (Attainment with at most $d^2$ rank-one effects).** For every
tuple in Definition 1.2, the infimum in (1.1) is attained. Some minimizer
has at most $d^2$ nonzero rank-one effects.

Proof. If $E=\sum_k E_k$ is a positive decomposition of one effect,
Cauchy–Schwarz gives, for each pair,

$$
\sum_k\sqrt{\operatorname{Tr}(E_k\rho_i)
                   \operatorname{Tr}(E_k\rho_j)}
\le\sqrt{\operatorname{Tr}(E\rho_i)\operatorname{Tr}(E\rho_j)}.
\tag{2.3}
$$

Thus spectral refinement into rank-one effects cannot increase the
common objective. Write the refined nonzero effects as $w_xP_x$, with
$w_x>0$ and $P_x$ trace-one rank-one orthogonal projections. Set

$$
h(P)=\frac1q\sum_{i<j}
\sqrt{\operatorname{Tr}(P\rho_i)\operatorname{Tr}(P\rho_j)}.
$$

The constraint and objective become

$$
\sum_xw_xP_x=I_d,\qquad \sum_xw_xh(P_x).
\tag{2.4}
$$

If there are more than $d^2$ nonzero weights, real linear dependence
in the $d^2$-dimensional space of Hermitian matrices supplies real
$a_x$, not all zero, with $\sum_xa_xP_x=0$. Traces give
$\sum_xa_x=0$, so the relation has both signs. Reverse its sign if
necessary so that $\sum_xa_xh(P_x)\le0$. For

$$
s_* =\min_{a_x<0}\frac{w_x}{-a_x}>0,
$$

replace $w_x$ by $w_x+s_*a_x$. The weights remain nonnegative,
at least one vanishes, the matrix constraint is unchanged, and the
objective does not increase. Repetition terminates at at most $d^2$
nonzero effects.

Pad with zero effects to exactly $d^2$ slots. The set

$$
\mathcal K_d=\{(E_1,\ldots,E_{d^2}):
E_x\succeq0,\ \operatorname{rank}E_x\le1,\ \sum_xE_x=I_d\}
\tag{2.5}
$$

is nonempty: take the $d$ coordinate projections and zeros. Positivity,
rank at most one, and the sum constraint are closed conditions;
$0\preceq E_x\preceq I_d$ bounds every coordinate. Hence $\mathcal K_d$
is compact. The objective is continuous, including at zero effects,
so it has a minimum on $\mathcal K_d$. Every finite POVM has a
no-larger competitor in $\mathcal K_d$, and every member of
$\mathcal K_d$ is a finite POVM. Their infima coincide. Removing the
zero slots proves the assertion. Rank **at most** one is essential for
this compactness argument; the set of exactly rank-one effects would
exclude its zero boundary. $\square$

## 3. Compatibility and every equality measurement

**Theorem 3.1 (Common-measurement compatibility).** Under Definition 1.2,
the following four conditions are equivalent:

1. $F_M(\boldsymbol\rho)=F_U(\boldsymbol\rho)$.
2. Some finite POVM attains the pairwise fidelity minimum for every
   unordered pair of states.
3. Some finite POVM attains the pairwise fidelity minimum for every
   anchored pair $(\rho_0,\rho_i)$.
4. $[T_i,T_j]=0$ for all $i,j$.

When these conditions hold, let $\{P_\alpha\}$ be the joint spectral
projections of $T_0,\ldots,T_{r-1}$, indexed by **distinct joint
eigenvalue tuples**, so

$$
T_iP_\alpha=\lambda_{i\alpha}P_\alpha,\qquad
\lambda_{i\alpha}>0.
\tag{3.1}
$$

The complete characterization of equality POVMs is: each nonzero
$E_x$ is supported in one joint block, and within each block the
effects sum to its projection:

$$
E_x=P_{\alpha(x)}E_xP_{\alpha(x)},\qquad
\sum_{x:\alpha(x)=\alpha}E_x=P_\alpha.
\tag{3.2}
$$

Effects inside a degenerate joint block may be arbitrary positive
operators satisfying this sum. They need not be projections or commute
with one another.

Proof. By Theorem 2.2, condition 1 has an attaining POVM. Its sum of
nonnegative pair deficits is zero, so every deficit is zero, proving 2.
Condition 2 implies 3. Under condition 3, (2.2) gives
$[T_i,T_j]\sqrt{E_x}=0$ for each effect. Right multiplication by
$\sqrt{E_x}$ and summation gives

$$
[T_i,T_j]=[T_i,T_j]\sum_xE_x=0,
$$

proving 4.

Conversely suppose 4 holds. The commuting positive Hermitian matrices
have a joint spectral PVM. For any $i,j$ the matrix

$$
S_{ij}=T_jT_i^{-1}=T_i^{-1}T_j
\tag{3.3}
$$

is positive definite, and

$$
S_{ij}\rho_iS_{ij}
=(T_jT_i^{-1})(T_i\rho_0T_i)(T_i^{-1}T_j)
=T_j\rho_0T_j=\rho_j.
\tag{3.4}
$$

Uniqueness in Definition 1.3, with anchor $\rho_i$, makes $S_{ij}$
the positive transport for that pair. It is scalar on every joint
block, with eigenvalue $\lambda_{j\alpha}/\lambda_{i\alpha}$.
The FC equality relation therefore applies to the **same** joint
PVM for every pair. More explicitly, if an effect is supported in
block $\alpha$, (3.4) implies
$p_j(x)=(\lambda_{j\alpha}/\lambda_{i\alpha})^2p_i(x)$,
and its pairwise residual is zero. Thus every POVM in (3.2)
attains all pairs, proving 2 and 1.

For completeness, necessity of (3.2) follows from (2.2): the range
of every effect consists of simultaneous eigenvectors with a single
joint eigenvalue tuple. Different tuples have orthogonal joint
subspaces. Compressing $\sum_xE_x=I_d$ to a given block gives its
sum condition. Sufficiency was just proved using every $S_{ij}$.
This includes all degeneracies. If every $T_i=I_d$, there is one
joint block and (3.2) permits every POVM. $\square$

For the maximally mixed anchor $\rho_0=I_d/d$, formula (1.2) gives
$T_i=\sqrt{d\rho_i}$, so the criterion is equivalent to pairwise
commutation of the remaining density matrices. For a general anchor
it concerns the transports. The positive, noncommuting density
matrices of Theorem 6.1 show that these conditions cannot be
interchanged.

## 4. A pointwise arbitrary-POVM commutator bound

**Theorem 4.1 (Quantitative defect).** Suppose, in addition to
Definition 1.2, that one common number $\mu$ satisfies

$$
0<\mu\le1/d,\qquad \rho_i\succeq\mu I_d\quad(0\le i<r).
$$

Set $L=1-(d-1)\mu$ and $M=\sqrt{L/\mu}$. For **every** finite POVM,
of any finite outcome count,

$$
G(E)\ge
\frac{\mu}{8M^3r(r-1)(r-2)}
\sum_{1\le i<j\le r-1}\|[T_i,T_j]\|_F^2.
\tag{4.1}
$$

In particular the entire common-measurement infimum satisfies

$$
\Delta(\boldsymbol\rho)\ge
\frac{\mu^{5/2}}
 {8[1-(d-1)\mu]^{3/2}r(r-1)(r-2)}
\sum_{1\le i<j\le r-1}\|[T_i,T_j]\|_F^2.
\tag{4.2}
$$

Proof. Trace one and the lower eigenvalue bound give
$\rho_i\preceq LI_d$. Equation (1.3) implies

$$
\mu T_i^2\preceq T_i\rho_0T_i=\rho_i\preceq LI_d,
\qquad \|T_i\|_{\mathrm{op}}\le M.
\tag{4.3}
$$

Independently, $p_i(x)\le L\operatorname{Tr}E_x$ and
$p_0(x)\ge\mu\operatorname{Tr}E_x$ imply $t_{ix}\le M$.
This ratio estimate does not require commuting operator factors.
Delete zero effects and form one shared isometry

$$
\begin{aligned}
V:\mathbb C^d&\longrightarrow\bigoplus_x\mathbb C^d,
&Vv&=(\sqrt{E_x}v)_x,\\
D_i&=\bigoplus_x t_{ix}I_d,
&K_i&=VT_i-D_iV.
\end{aligned}
\tag{4.4}
$$

Here $V^\dagger V=\sum_xE_x=I_d$, the $D_i$ commute, and
$\|D_i\|_{\mathrm{op}}\le M$. For any matrix $A$,
$\|A\sqrt{\rho_0}\|_F^2\ge\mu\|A\|_F^2$. Applying this
inside (2.1) gives

$$
\|K_i\|_F^2
=\sum_x\|\sqrt{E_x}(T_i-t_{ix}I_d)\|_F^2
\le\frac{2M}{\mu}\delta_{0i}(E).
\tag{4.5}
$$

Expand both sides using (4.4) and $D_iD_j=D_jD_i$ to obtain the
exact identity

$$
V[T_i,T_j]=D_iK_j-D_jK_i+K_iT_j-K_jT_i.
\tag{4.6}
$$

Left multiplication by $V$ preserves Frobenius norm. The product
norm inequalities and (4.3)–(4.5) therefore give

$$
\begin{aligned}
\|[T_i,T_j]\|_F
&\le2M(\|K_i\|_F+\|K_j\|_F),\\
\|[T_i,T_j]\|_F^2
&\le8M^2(\|K_i\|_F^2+\|K_j\|_F^2)\\
&\le\frac{16M^3}{\mu}
     (\delta_{0i}(E)+\delta_{0j}(E)).
\end{aligned}
\tag{4.7}
$$

Sum over $1\le i<j\le r-1$. Each anchored deficit appears exactly
$r-2$ times. Since all other deficits are also nonnegative,

$$
\begin{aligned}
\sum_{1\le i<j\le r-1}\|[T_i,T_j]\|_F^2
&\le\frac{16M^3(r-2)}{\mu}\sum_{i=1}^{r-1}\delta_{0i}(E)\\
&\le\frac{16M^3(r-2)q}{\mu}G(E)\\
&=\frac{8M^3r(r-1)(r-2)}{\mu}G(E).
\end{aligned}
\tag{4.8}
$$

This proves (4.1) before any optimization. Taking the infimum over
all finite POVMs gives (4.2), because $\mu/M^3=\mu^{5/2}/L^{3/2}$.
At $\mu=1/d$ every state is $I_d/d$, $M=1$, all transports are
identity, and both sides are zero. At any smaller admissible $\mu$,
a nonzero commutator yields a strict positive bound; if all commute,
Theorem 3.1 gives zero defect. $\square$

The shared isometry in (4.4) preserves the arbitrary-POVM quantifier.
A lower bound proved only for projective measurements would not imply
(4.1) or (4.2): restricting a minimization set can increase its infimum.
No optimality of the constant or its parameter order is asserted.

## 5. The signed Pauli family and its finite minimization

**Definition 5.1 (Pauli tuple).** In the standard qubit basis let

$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
$$

and for real $a,b$ with $|a|,|b|<1$ set

$$
R=I_2/2,\qquad A_a=(I_2+aZ)/2,\qquad B_b=(I_2+bX)/2,
\qquad
f(t)=\frac{\sqrt{1+t}+\sqrt{1-t}}2.
\tag{5.1}
$$

Both signs and zero parameters are included; the singular endpoints
$|a|=1$ or $|b|=1$ are outside this positive-definite family.

**Theorem 5.2 (Compatibility, explicit $F_U$ and uniform Pauli defect).**
For every parameter pair in Definition 5.1,

$$
\begin{aligned}
\|[T_A,T_B]\|_F^2
 &=2(1-\sqrt{1-a^2})(1-\sqrt{1-b^2}),\\
\Delta(R,A_a,B_b)=0&\quad\Longleftrightarrow\quad ab=0,\\
F_U(R,A_a,B_b)
 &=\frac13\left[f(a)+f(b)+
 \sqrt{\frac{1+\sqrt{(1-a^2)(1-b^2)}}2}\right],\\
\Delta(R,A_a,B_b)
 &\ge\frac1{24}\min\left\{
 \frac{a^2}{(1+|a|)^{3/2}},
 \frac{b^2}{(1+|b|)^{3/2}}\right\}.
\end{aligned}
\tag{5.2}
$$

Proof. The anchor is $R$, so
$T_A=\sqrt{I_2+aZ}$ and $T_B=\sqrt{I_2+bX}$. Write

$$
\sqrt{I_2+tZ}=\alpha_tI_2+\beta_tZ,\quad
\alpha_t=f(t),\quad
\beta_t=\frac{\sqrt{1+t}-\sqrt{1-t}}2,\quad
\beta_t^2=\frac{1-\sqrt{1-t^2}}2.
$$

The analogous formula holds with $X$. Since $[Z,X]=2iY$ and
$\|Y\|_F^2=2$, the commutator square is $8\beta_a^2\beta_b^2$,
which is the first formula. Theorem 3.1 proves the zero/strict
classification. When $a=0$ or $b=0$, at most two distinct states
remain; a pairwise optimal measurement simultaneously attains every
pair, giving attainment of zero directly.

For the displayed $F_U$, reuse the two-dimensional root-fidelity
identity

$$
F(\rho,\sigma)^2=
\operatorname{Tr}(\rho\sigma)+2\sqrt{\det\rho\det\sigma}.
\tag{5.3}
$$

This is the identity used inside [PROBLEM, Route, steps 4–5;
SEP, Theorem 1.5][PROBLEM]. Its parameters here give
$F(R,A_a)=f(a)$, $F(R,B_b)=f(b)$,
$\operatorname{Tr}(A_aB_b)=1/2$,
$\det A_a=(1-a^2)/4$ and $\det B_b=(1-b^2)/4$.
Substitution gives (5.2)'s $F_U$ formula without an assumption on
parameter signs.

For the lower bound, write any nonzero qubit effect uniquely as

$$
E_x=w_x(I_2+u_xX+v_xY+z_xZ),\quad w_x>0,\quad
u_x^2+v_x^2+z_x^2\le1.
\tag{5.4}
$$

Completeness gives $\sum_xw_x=1$ and
$\sum_xw_xu_x=\sum_xw_xv_x=\sum_xw_xz_x=0$. The probabilities are

$$
p_R(x)=w_x,\qquad
p_A(x)=w_x(1+az_x),\qquad p_B(x)=w_x(1+bu_x).
\tag{5.5}
$$

For $|t|<1$ define the endpoint chord and curvature constant

$$
\ell_t(z)=\frac{1+z}{2}\sqrt{1+t}
          +\frac{1-z}{2}\sqrt{1-t},\qquad
\kappa_t=\frac{t^2}{8(1+|t|)^{3/2}}.
\tag{5.6}
$$

On $[-1,1]$,

$$
\frac{d^2}{dz^2}\sqrt{1+tz}
=-\frac{t^2}{4(1+tz)^{3/2}}\le-2\kappa_t.
$$

Thus $\sqrt{1+tz}-\ell_t(z)-\kappa_t(1-z^2)$ is concave and
vanishes at both endpoints, so it is nonnegative throughout.
The zero weighted means make
$\sum_xw_x\ell_a(z_x)=f(a)$ and
$\sum_xw_x\ell_b(u_x)=f(b)$. Therefore

$$
\begin{aligned}
\delta_{RA}(E)&\ge\kappa_a\sum_xw_x(1-z_x^2),\\
\delta_{RB}(E)&\ge\kappa_b\sum_xw_x(1-u_x^2).
\end{aligned}
\tag{5.7}
$$

Since $u_x^2+z_x^2\le1$, their sum is at least
$\min(\kappa_a,\kappa_b)\sum_xw_x(2-u_x^2-z_x^2)
\ge\min(\kappa_a,\kappa_b)$.
Add $\delta_{AB}(E)\ge0$, divide by three, and take the infimum
over every finite POVM. This proves the final line of (5.2), including
$t=0$, where the corresponding curvature constant vanishes. $\square$

At the existing repository witness $a=b=1/2$, the exact substitution is

$$
\begin{aligned}
F_U(R,A_{1/2},B_{1/2})
 &=\frac{2\sqrt6+2\sqrt2+\sqrt{14}}{12},\\
\Delta(R,A_{1/2},B_{1/2})&\ge\frac1{72\sqrt6},\\
F_M(R,A_{1/2},B_{1/2})
 &\ge\frac{2\sqrt6+2\sqrt2+\sqrt{14}}{12}
       +\frac1{72\sqrt6}.
\end{aligned}
\tag{5.8}
$$

These are lower bounds on $F_M$, not its exact value.

**Theorem 5.3 (A real minimizer with at most three outcomes).** For every
signed or zero parameter pair in Definition 5.1, some global minimizer
has at most three nonzero real rank-one effects.

Proof. In (5.4), replace every $v_x$ by zero. Positivity is preserved
because $u_x^2+z_x^2\le1$, completeness is preserved, and (5.5)
shows that all probabilities and the objective are unchanged. The
resulting effects are real symmetric. Real spectral refinement cannot
increase the objective by (2.3). Apply the weight-elimination argument
of Theorem 2.2 in the three-dimensional real vector space
$\operatorname{span}_{\mathbb R}\{I_2,X,Z\}$. It leaves at most three
nonzero real rank-one effects. Zero padding to three slots gives a
nonempty compact set of real positive effects of rank at most one
summing to $I_2$, on which the objective attains its minimum.
Every finite POVM has a no-larger competitor there. $\square$

This is an existence statement. It does not classify every minimizer
in the positive-gap regime or determine the exact general or Pauli
$F_M$.

## 6. Fidelity equality and classical recovery are different conditions

**Theorem 6.1 (Zero defect without a common measurement–preparation
inverse).** There are strictly positive noncommuting density matrices
with commuting anchored transports and $\Delta=0$, but no finite
measurement followed by one CPTP preparation fixes all of them. One
such tuple is

$$
\begin{gathered}
\sigma_0=\begin{pmatrix}1/2&1/4\\1/4&1/2\end{pmatrix},\qquad
D_+=\operatorname{diag}(\sqrt{3/2},1/\sqrt2),\qquad
D_-=\operatorname{diag}(1/\sqrt2,\sqrt{3/2}),\\
\sigma_+=D_+\sigma_0D_+
 =\begin{pmatrix}3/4&\sqrt3/8\\\sqrt3/8&1/4\end{pmatrix},\qquad
\sigma_-=D_-\sigma_0D_-
 =\begin{pmatrix}1/4&\sqrt3/8\\\sqrt3/8&3/4\end{pmatrix}.
\end{gathered}
\tag{6.1}
$$

Proof. All three traces are one, their leading diagonal entries are
positive, and

$$
\det\sigma_0=3/16,\qquad
\det\sigma_+=\det\sigma_-=9/64.
$$

Thus they are positive definite. The unique anchored positive
transports are $D_+,D_-$, which commute, so Theorem 3.1 gives
$\Delta=0$. Nevertheless

$$
[\sigma_0,\sigma_+]=\begin{pmatrix}0&-1/8\\1/8&0\end{pmatrix}\ne0.
\tag{6.2}
$$

Suppose one finite measurement channel $\mathcal M$ and one CPTP
preparation $\mathcal P$ fix all three states. Fidelity data processing
in both steps forces, for each pair,

$$
F(\sigma_i,\sigma_j)
\le F(\mathcal M(\sigma_i),\mathcal M(\sigma_j))
\le F(\mathcal P\mathcal M(\sigma_i),\mathcal P\mathcal M(\sigma_j))
=F(\sigma_i,\sigma_j).
$$

Hence $\mathcal M$ is pairwise optimal. Since $D_+$ has distinct
eigenvalues, (2.2) forces every nonzero effect to be supported on one
coordinate axis. The diagonal entries of (6.1) then give, effect by
effect,

$$
\mathcal M(\sigma_0)
=\tfrac12\bigl(\mathcal M(\sigma_+)+\mathcal M(\sigma_-)\bigr).
$$

Linearity of $\mathcal P$ would imply
$\sigma_0=(\sigma_++\sigma_-)/2$, whose off-diagonal entries would
be $\sqrt3/8$ rather than $1/4$. This is a contradiction. $\square$

**Theorem 6.2 (Conditional classical recovery error).** For any tuple
of Definition 1.2, suppose there is a genuine finite classical
measure–prepare factorization

$$
\tau_i=\mathcal P\mathcal M(\rho_i),\qquad
\max_i\frac12\|\tau_i-\rho_i\|_1\le\varepsilon,
\tag{6.3}
$$

where $\mathcal M$ is one finite measurement and $\mathcal P$ one
CPTP preparation. Then

$$
\varepsilon\ge\Delta(\boldsymbol\rho)^2/8.
\tag{6.4}
$$

Proof. The definition of the common infimum and fidelity data processing
give the correctly directed inequalities

$$
F_M(\boldsymbol\rho)
\le F_U(\mathcal M(\boldsymbol\rho))
\le F_U(\boldsymbol\tau).
\tag{6.5}
$$

To track the constant, fix any finite POVM and distributions $p,p',q$
obtained from $\rho,\rho',\sigma$. Cauchy–Schwarz and the scalar
inequality $(\sqrt s-\sqrt t)^2\le|s-t|$ give

$$
\left|\sum_x\sqrt{p(x)q(x)}-\sum_x\sqrt{p'(x)q(x)}\right|
\le\|\sqrt p-\sqrt{p'}\|_2
\le\sqrt{\|p-p'\|_1}
\le\sqrt{\|\rho-\rho'\|_1}.
$$

The bound is uniform over POVMs, so taking their pairwise infima
[NMLW, Proposition 3.1, PDF equation (3.2), also for singular states][NMLW]
and then changing the other argument yields

$$
|F(\rho,\sigma)-F(\rho',\sigma')|
\le\sqrt{\|\rho-\rho'\|_1}
   +\sqrt{\|\sigma-\sigma'\|_1}.
\tag{6.6}
$$

Each pair, and therefore its average, changes by at most
$2\sqrt{2\varepsilon}$ under (6.3). Equation (6.5) now implies

$$
0\le\Delta(\boldsymbol\rho)
\le F_U(\boldsymbol\tau)-F_U(\boldsymbol\rho)
\le2\sqrt{2\varepsilon}.
$$

Squaring proves (6.4). The factor $1/8$ uses **half** trace norm in
(6.3). The classical intermediate in (6.3) is an essential assumption.
A classical record accompanying a retained quantum system does not
satisfy it. $\square$

## 7. The actual five-dimensional instrument and its recovery permissions

**Definition 7.1 (Actual supplier coordinates).** Use [REC,
Definitions 1.3 and 2.1; Theorem 2.2][REC]. In the ordered five-window basis,

$$
\begin{gathered}
H=\mathbb C^5,\qquad
(e_0,e_1,e_2,e_3,e_4)=(|000\rangle,|100\rangle,|010\rangle,
                       |001\rangle,|101\rangle),\\
u=(e_0+e_3)/\sqrt2,\qquad v=(e_1+e_4)/\sqrt2,\qquad z=e_2,\\
R=\operatorname{span}\{u,v,z\},\qquad
B:\mathbb C^3\longrightarrow H,\qquad B(x_0,x_1,x_2)=x_0u+x_1v+x_2z,\\
B^\dagger B=I_3,\qquad P_R=BB^\dagger,\qquad
\iota:M_3\longrightarrow M_5,\quad\iota(X)=BXB^\dagger.
\end{gathered}
\tag{7.1}
$$

The qubit state $R$ in §5 and the code subspace $R\subset H$ here
have different types; $R$ in §§7–10 always denotes the subspace.
The untouched reference is denoted by $Z_{\rm ref}$.

The environment is $\mathbb C^2$, with orthonormal basis $(f_0,f_1)$
and pure ready state $f_0$. The actual isometry is

$$
\begin{aligned}
\mathcal V e_0&=u\otimes f_0,&
\mathcal V e_1&=u\otimes f_1,&
\mathcal V e_2&=v\otimes(f_0+f_1)/\sqrt2,\\
\mathcal V e_3&=z\otimes f_1,&
\mathcal V e_4&=z\otimes f_0.
\end{aligned}
\tag{7.2}
$$

Its orthonormal images admit a unitary completion on
$H\otimes\mathbb C^2$ for inputs with environment $f_0$ [REC,
Theorem 2.2][REC]. The first instrument measures $(f_0,f_1)$ and has
full-$H$ Kraus operators

$$
\begin{aligned}
K_0&=|u\rangle\langle e_0|+2^{-1/2}|v\rangle\langle e_2|
                         +|z\rangle\langle e_4|,\\
K_1&=|u\rangle\langle e_1|+2^{-1/2}|v\rangle\langle e_2|
                         +|z\rangle\langle e_3|.
\end{aligned}
\tag{7.3}
$$

The second uses the same interaction and ready state, measuring

$$
g_0=cf_0-isf_1,\qquad g_1=-isf_0+cf_1,\qquad
c=\cos\theta,\ s=\sin\theta.
$$

Its full operators are

$$
A_0=cK_0+isK_1,\qquad A_1=isK_0+cK_1.
\tag{7.4}
$$

The cases compared below are $\theta=0$ and $\theta=\pi/6$.
Theorem 2.2 of [REC] gives, on the entire complex $M_5$ algebra,

$$
\sum_jA_jXA_j^\dagger=\sum_jK_jXK_j^\dagger=\Phi_\circ(X).
\tag{7.5}
$$

This is full-channel equality, including after tensoring with any
untouched reference, not merely equality of populations.
The actual restricted matrices are

$$
\begin{gathered}
U_0=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad
U_1=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix},\qquad
W=U_0^\dagger U_1=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix},\\
W^\dagger=W,\quad W^2=I_3,\quad
V_0=cU_0+isU_1=U_0e^{i\theta W},\quad V_1=V_0W,\\
K_jB=2^{-1/2}BU_j,\qquad A_jB=2^{-1/2}BV_j.
\end{gathered}
\tag{7.6}
$$

These $U_j,V_j$ are unitary. If $L_j$ denotes the full operator of
the chosen instrument and $Q_j$ its restricted unitary, then
$B^\dagger L_j^\dagger L_jB=I_3/2$. Outcome fairness holds for
embedded qutrit inputs and untouched references. It does not hold on
arbitrary $H$ inputs: for instance
$K_0^\dagger K_0=\operatorname{diag}(1,0,1/2,0,1)$.
The full Kraus operators are not scaled full-$H$ unitaries.

**Assumption 7.2 (Chronology, classical view and exact task).** Fix one
of these instruments and a known horizon $n\ge0$. At each step a fresh
environment is prepared, the same interaction is applied, the same
chosen environment basis is measured, the actual binary label is supplied,
and the environment is discarded. Only these labels update the classical
record between steps. There is no intermediate quantum feedback, adaptive
instrument, reference read, retained quantum environment, quantum summary,
input-dependent quantum side information or success postselection.

For the chronological history $h=(h_1,\ldots,h_n)$,

$$
Q_h=Q_{h_n}\cdots Q_{h_1},\qquad Q_{\varnothing}=I_3.
\tag{7.7}
$$

Each history has probability $2^{-n}$ for every qutrit input, also
when entangled with any untouched finite reference. The latest factor
acts on the left. The complete decoder-visible run-dependent classical
view includes any history-dependent program, control selection, clock
variation, seed, archive or buffer. A visible correlated seed is counted
jointly. Discarded private randomness is averaged out.

An explicitly free independent shared seed may instead have a standard
Borel law $\nu$ and be conditioned on before integrating the final
channel. Decoders are measurable CPTP maps $M_5\to M_5$, selected by
the complete view and that seed. Their input includes the actual quantum
system $H$. Exact success is required for every density on
$\mathbb C^3\otimes Z_{\rm ref}$ and every finite untouched reference:
the target is $(\iota\otimes\operatorname{id})(\rho)$. It may be
required only after averaging over histories, record randomness and the
seed. Arbitrary unknown states on $H$ are not recovery targets.

These are [REC, Assumption 1.4, Definition 1.5, Convention 3.4 and
Convention 9.1][REC]. The $n$ label acquisitions, preparations, measurement
communication, calibration, deterministic known clock, fixed tables or
control descriptions, inverse-control synthesis and precision are
separate resources. Fixed descriptions may depend on $n$ but carry no
additional run-dependent history. A bound on retained register values
is not a bound on these other costs.

**Convention 7.3 (Published correction interfaces).** The correction criterion
of M. Gregoratti and
R. F. Werner, *Quantum Lost and Found*, arXiv:quant-ph/0209025v1,
[GW, Proposition 2 and equation (7)][GW] applies to the specified fine Kraus
decomposition with restricted system $\mathbb C^3\cong R$:
$t_j=Q_j/\sqrt2$ and $t_j^\dagger t_j=I_3/2$. It supplies the
standard fine-label correction principle, including a trace-preserving
extension for a rectangular isometry. It does not permit arbitrary
merger of fine labels or identify its system with all of $H$.

For an actual coarsened view, the errors are
$F_h=\sqrt{w_h}Q_h$, with $w_h$ its conditional history weights.
The criterion of Emanuel Knill and Raymond Laflamme, *A Theory of Quantum Error-Correcting
Codes*, arXiv:quant-ph/9604034v1, [KL, Theorem 3.2, equations (19)–(20)][KL] uses code $I_3$
and all complex cross terms $F_h^\dagger F_k=\gamma_{hk}I_3$.
The exact summary criterion [REC, Theorem 3.3][REC] establishes this
condition for arbitrary full-$H$ CPTP decoders and ensemble-only exact
success. It permits one projective word class per positive view;
fine-branch fairness by itself does not establish that condition.

## 8. Fine-label channels, literal retraction and invariant defect

**Theorem 8.1 (Actual label marginal and two typed inverses).** Under
Assumption 7.2, retaining every fine label gives the CPTP map

$$
\mathcal J_n^\theta:M_3\longrightarrow M_{2^n}\otimes M_5,\qquad
\mathcal J_n^\theta(X)=2^{-n}\sum_{h\in\{0,1\}^n}
 |h\rangle\langle h|\otimes\iota(Q_hXQ_h^\dagger).
\tag{8.1}
$$

Its label marginal is

$$
\mathcal L_n^\theta(X)=\operatorname{Tr}_H\mathcal J_n^\theta(X)
=2^{-n}I_{2^n}\operatorname{Tr}X.
\tag{8.2}
$$

There is a full-output CPTP map $\Gamma:M_{2^n}\otimes M_5\to M_5$
with $\Gamma\mathcal J_n^\theta=\iota$. There is also a literal CPTP
left inverse $\mathcal T:M_{2^n}\otimes M_5\to M_3$ with
$\mathcal T\mathcal J_n^\theta=\operatorname{id}_{M_3}$.
Both identities persist with every untouched finite reference.

Proof. Iterating (7.6) gives the actual history Kraus operator
$2^{-n/2}BQ_h$ from qutrit coordinates. The ranges remain in $R$,
so the restricted fairness law applies at each step; fresh preparations
give the product probability $2^{-n}$. Recording these actual outcomes
gives (8.1). Its Kraus operators are
$2^{-n/2}|h\rangle\otimes BQ_h$; their adjoint products sum to
$I_3$. Taking the system trace gives (8.2).

For any full joint operator $Y$, write
$Y_{hh}=(\langle h|\otimes I_5)Y(|h\rangle\otimes I_5)$ and set

$$
D_h=BQ_h^\dagger B^\dagger+(I_5-P_R),\qquad
\Gamma(Y)=\sum_hD_hY_{hh}D_h^\dagger.
\tag{8.3}
$$

Each $D_h$ is unitary, acting as $Q_h^\dagger$ on $R$ in the
$B$ coordinates and identity on $R^\perp$. The Kraus operators
$D_h(\langle h|\otimes I_5)$ prove complete positivity and have
adjoint products summing to $I_{2^n}\otimes I_5$. Thus $\Gamma$
is trace preserving on the **entire** joint output algebra. Since
$D_hBQ_h=B$, equation (8.1) gives $\Gamma\mathcal J_n^\theta=\iota$.
This is recovery to $M_5$ up to the specified embedding.

For a literal codomain $M_3$, choose any qutrit density $\omega$ and
use the retraction

$$
\mathcal R_B:M_5\longrightarrow M_3,\qquad
\mathcal R_B(Y)=B^\dagger YB+
 \operatorname{Tr}[(I_5-P_R)Y]\,\omega.
\tag{8.4}
$$

The second term is a positive-functional preparation map, hence CP.
Explicitly, if $\omega=\sum_k\lambda_k|a_k\rangle\langle a_k|$
and $(c_1,c_2)$ is an orthonormal basis of $R^\perp$, its Kraus
operators are $\sqrt{\lambda_k}|a_k\rangle\langle c_\ell|$.
Together with $B^\dagger$ their adjoint products sum to
$P_R+(I_5-P_R)=I_5$. Thus $\mathcal R_B$ is CPTP on all $M_5$,
and $\mathcal R_B\iota=\operatorname{id}_{M_3}$.
The map $\mathcal T=\mathcal R_B\Gamma$ is the asserted literal
left inverse. Omitting the complement trace term would lose trace
preservation on off-code inputs. All identities hold on the complex
operator algebras, so tensoring with $\operatorname{id}_{Z_{\rm ref}}$
proves the reference statements. $\square$

For any state tuple, the **label-only** output states in (8.2) are
identical. Consequently

$$
F_U(\mathcal L_n^\theta(\boldsymbol\rho))
=F_M(\mathcal L_n^\theta(\boldsymbol\rho))=1,
\qquad\Delta(\mathcal L_n^\theta(\boldsymbol\rho))=0.
\tag{8.5}
$$

If a reference is retained alongside the labels, the output is instead
$2^{-n}I_{2^n}\otimes\operatorname{Tr}_{\mathbb C^3}\rho$.
It retains its own reference marginal, which need not coincide for
different joint input states. Equation (8.5) asserts constancy of the
label marginal alone.

**Theorem 8.2 (Fine-joint invariance and direct-sum scaling).** For every
qutrit density tuple, every $n\ge0$ and either instrument,

$$
\begin{aligned}
F_U(\mathcal J_n^\theta(\boldsymbol\rho))&=F_U(\boldsymbol\rho),\\
F_M(\mathcal J_n^\theta(\boldsymbol\rho))&=F_M(\boldsymbol\rho),\\
\Delta(\mathcal J_n^\theta(\boldsymbol\rho))&=\Delta(\boldsymbol\rho).
\end{aligned}
\tag{8.6}
$$

For qubit states $\rho_i$ and a common weight $0<\lambda<1$, let
$\widehat\rho_i=\lambda\rho_i\oplus(1-\lambda)$ be qutrit states.
Then

$$
\begin{aligned}
F_U(\widehat{\boldsymbol\rho})&=
 \lambda F_U(\boldsymbol\rho)+1-\lambda,\\
F_M(\widehat{\boldsymbol\rho})&=
 \lambda F_M(\boldsymbol\rho)+1-\lambda,\\
\Delta(\widehat{\boldsymbol\rho})&=\lambda\Delta(\boldsymbol\rho).
\end{aligned}
\tag{8.7}
$$

Proof. Reuse fidelity data processing and the measured-fidelity
pullback principle [NMLW, Proposition 5.39, PDF pp. 31–32;
Appendix A.21, PDF pp. 85–86, equations (A.299)–(A.315)][NMLW].
For any CPTP $\mathcal N$ and output POVM $(E_x)$, the effects
$\mathcal N^*(E_x)$ form an input POVM with identical probabilities.
Thus $F_M(\mathcal N(\boldsymbol\rho))\ge F_M(\boldsymbol\rho)$.
The same direction holds for $F_U$ by pairwise fidelity data processing.
Apply both inequalities first to $\mathcal J_n^\theta$ and then to its
literal left inverse $\mathcal T$ from Theorem 8.1. The reverse
inequalities give equality, proving (8.6). No positive-definite
transport theorem is being applied to the singular joint outputs.

For the actual direct-sum correspondence, block square roots and trace
norms give
$F(\widehat\rho_i,\widehat\rho_j)=\lambda F(\rho_i,\rho_j)+1-\lambda$.
Given any qutrit POVM, replace each effect by its two block
compressions, keeping their outcome labels distinct. For these
block-diagonal inputs the original outcome probabilities are sums of
the two compressed probabilities. Equation (2.3) shows that this
refinement cannot increase the objective. The qubit block is a qubit
POVM and contributes at least $\lambda F_M(\boldsymbol\rho)$;
the scalar block contributes exactly $1-\lambda$. Hence every
qutrit POVM has objective at least that expression. Conversely,
combine a qubit optimizer (Theorem 2.2 for the strictly positive
family used here) with the scalar-block effect. For a general
semidefinite tuple, finite POVMs arbitrarily approaching its infimum
suffice for this converse. They give the reverse inequality after
taking the infimum. This is the common-block-weight direct-sum
property of the cited supplier, specialized to this embedding, and
proves (8.7). $\square$

In particular, use the Pauli triple of §5 with
$\widehat\rho_i=\tfrac12\rho_i\oplus\tfrac12$. It is a legitimate
strictly positive qutrit tuple, and at $a=b=1/2$,

$$
\Delta(\widehat{\boldsymbol\rho})\ge\frac1{144\sqrt6}>0.
\tag{8.8}
$$

Its full fine-label plus quantum-output defect has this same bound
at **every** horizon and at both angles by (8.6).

## 9. Existing exact record results and the scalar distinction

**Convention 9.1 (Exact record supplier).** Write
$m_n=|\{[Q_h]:h\in\{0,1\}^n\}|$, where
$[Q_h]=[Q_k]$ means equality up to a scalar phase of modulus one.
Under precisely Assumption 7.2, [REC, Theorems 3.3 and 4.1][REC] gives
minimum terminal alphabet $m_n$, including random classical
compression and arbitrary full-$H$ CPTP decoding. Its online
construction has at most $m_n$ retained register values at every
prefix, using the known deterministic clock and fixed time-dependent
tables. Terminal necessity is also a lower bound on peak register
cardinality, so this peak is attainable and minimal in that register
model.

The exact specializations [REC, Theorems 5.1, 8.2 and 9.2–9.4][REC] are

| Actual measured instrument | $n=0$ | $n=1$ | $n=2$ | $n\ge3$ |
| --- | --- | --- | --- | --- |
| $\theta=0$ | $1$ | $2$ | $4$ | $6$ |
| $\theta=\pi/6$ | $1$ | $2$ | $4$ | $2^n$ |

At $\theta=0$ a homogeneous six-value accumulator works for all
horizons. At $\theta=\pi/6$ the full acquired-history shift register
attains $2^n$ values, $n$ fixed binary bits and discrete Shannon
entropy $n$; every successful complete view determines the history
almost surely. Convention 3.4 and Theorem 9.3 of [REC] retain the
standard Borel and explicitly free independent shared-seed
permissions: exact averaged success forces conditional exact success
almost everywhere, and the same conditional alphabet bound holds.
This is an **exact** result; averaging an approximate error would not
imply the same error at almost every seed.

These results, including the all-length residue proof and the
achievable prefix-register bound, are supplied by [REC]; their source
proofs are not repeated. They count complete retained views, with all
the separate-resource qualifications of Assumption 7.2. In particular,
Theorem 4.1 is needed for the generic prefix claim in addition to the
special counts in Theorems 5.1 and 9.2–9.4.

**Theorem 9.2 (Three scalar constructions do not discriminate the
record optima).** Fix a common input tuple and a known horizon $n\ge3$
at the two angles in Convention 9.1. Each of the following constructions fails to determine
which of those two exact record requirements applies: the label-only
defect; the full fine-label plus quantum-output defect; or fidelity
data computed solely from the averaged channel and the fixed input
tuple.

Proof. The label-only defect is identically zero by (8.5), for both
angles and every horizon. The fine-joint defect equals the input
defect by (8.6), also for both angles and every horizon; (8.8) supplies
a positive example. Finally, (7.5) gives exactly the same averaged
channel on all $M_5$ inputs. Its repetitions, with fresh environments
and the outcomes discarded, are therefore identical at the two angles,
also with untouched references. Thus any construction depending only
on that channel and a common fixed tuple has identical data. Yet the
minimum retained alphabets are $6$ and $2^n$ for $n\ge3$, as supplied
in Convention 9.1. None of these identical scalar data alone separates
those unequal requirements. $\square$

This conclusion concerns the three specified substitutions. It does
not exclude a future fidelity method that uses additional relations
depending on the actual compression and decoder.

## 10. The unresolved protocol-sensitive record bridge

**Definition 10.1 (Allowed finite-view protocol channel).** For each
value $s$ of the explicitly free independent shared seed, let
$r_s(y\mid h)$ be the actual classical compression kernel,

$$
r_s(y\mid h)\ge0,\qquad \sum_y r_s(y\mid h)=1,
$$

on the complete finite counted view. The kernel is input-independent
and includes discarded private randomness. Let
$\mathcal D_{s,y}:M_5\to M_5$ be its measurable CPTP terminal decoders.
Then the actual channel is

$$
\begin{aligned}
\mathcal C_s(X)
 &=2^{-n}\sum_{h,y}r_s(y\mid h)\,
   \mathcal D_{s,y}\bigl(\iota(Q_hXQ_h^\dagger)\bigr),\\
\mathcal C(X)&=\int\mathcal C_s(X)\,d\nu(s).
\end{aligned}
\tag{10.1}
$$

Every $\mathcal D_{s,y}$ still receives the actual quantum $H$ output.
Exact success is $\mathcal C=\iota$, on all complex $M_3$ inputs
and hence with all untouched references. If there is no free seed,
use a singleton seed space. Countable or standard Borel views use the
corresponding sums or conditional measure integrals of [REC,
Convention 3.4 and Theorem 9.3][REC]; an uncountable view is not a finite
alphabet because its individual points have probability zero.

**Theorem 10.2 (No classical factorization supplied by the record
interface).** The allowed protocol interface (10.1) does not imply
the measure–prepare premise (6.3). In particular, exact fine-label
recovery exists even for the positive-defect qutrit tuple (8.8).

Proof. Retaining $y=h$ and applying (8.3) realizes exact recovery
up to $\iota$; this is an allowed terminal protocol, also with all
references. A finite measure–prepare channel from the qutrit to
$H$ would instead have form

$$
\mathcal P\mathcal M(X)=\sum_y\operatorname{Tr}(E_yX)\tau_y.
$$

On half of a maximally entangled qutrit state its output is
$\sum_y\tau_y\otimes\operatorname{Tr}_{\mathbb C^3}
[(E_y\otimes I)\rho]$, a sum of positive product operators,
hence separable. The exact target
$(B\otimes I)|\Omega_3\rangle\langle\Omega_3|(B^\dagger\otimes I)$
is pure of Schmidt rank three and is entangled. Thus such a
factorization cannot realize the allowed exact channel. Theorem 6.2
is consequently conditional on a strictly different transmission
premise and supplies no error bound for all protocols (10.1).
$\square$

**Definition 10.3 (Missing universal operational bridge).** A transfer
from the common-measurement defect to an approximate actual-record
bound requires a statement of the following form. For **every** actual
allowed protocol of retained register/view size $W$ at known horizon
$n$, with its kernels, full-$H$ decoders and independent seed law,
and with a specified uniform recovery error on **all** qutrit and
untouched-reference inputs, construct one legitimate finite POVM
$E_{\mathcal C}$ and one explicitly chosen actual state tuple
$\boldsymbol\eta_{\mathcal C}$ such that

$$
0\le\Delta(\boldsymbol\eta_{\mathcal C})
\le G_{\boldsymbol\eta_{\mathcal C}}(E_{\mathcal C})
\le g(W,n,\varepsilon).
\tag{10.2}
$$

The construction, common-realization mapping and every constant in
$g$ must be supplied, and the final upper bound must have resource
dependence strong enough to combine with the lower defect bound in
the desired direction. Separate optimal POVMs for separate pairs
would not meet (10.2).

An approximate error metric and its reference quantifier must first
be fixed; the exact source task does not choose them. For example,
one possible additional definition is

$$
\operatorname{err}(\mathcal C)=
\sup_{\substack{Z_{\rm ref}\text{ finite}\\
\rho\text{ density on }\mathbb C^3\otimes Z_{\rm ref}}}
\frac12\|((\mathcal C-\iota)\otimes\operatorname{id}_{Z_{\rm ref}})(\rho)\|_1.
\tag{10.3}
$$

Choosing this metric would still leave the construction (10.2)
unproved. A transfer must preserve the fixed fair instrument,
chronological histories, actual quantum $H$ passed to decoding,
all untouched references, complete run-dependent view accounting,
and seed integration. Correlated visible seed or control information
must be counted. An error bound on the integrated channel does not
itself give a seedwise approximate bound. The bridge must not assume
that the unknown qutrit passes only through a classical variable.

No construction satisfying these obligations is established here.
Theorem 9.2 shows why the three scalar constructions alone do not
supply it; Theorem 10.2 prevents replacing the actual task by the
premise of Theorem 6.2. These facts do not prove impossibility of every
protocol-sensitive fidelity bridge.

**Definition 10.4 (Remaining mathematical boundaries).** The exact
value of general or Pauli $F_M$, the classification of every
positive-gap optimizer, optimal constants or parameter orders in
Theorems 4.1 and 5.2, and a full singular-state transport/equality
classification remain undetermined here. Definition 10.3 is an
unresolved operational relation; neither the positive-defect example
nor the existing exact record results resolve it. No additional
record lower bound, physical realization, control-cost conclusion,
literature-completeness assertion or global novelty claim follows
from this volume.

[NMLW]: https://arxiv.org/pdf/2404.16101v3
[FC]: https://arxiv.org/html/quant-ph/9604001v1
[GW]: https://arxiv.org/html/quant-ph/0209025v1
[KL]: https://arxiv.org/html/quant-ph/9604034v1
[SEP]: https://github.com/the-omega-institute/trureturing/blob/9ebc22c28bd51d31eafacb9320f91e96df4e6275/Blueprint/D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation.md
[PROBLEM]: https://github.com/the-omega-institute/trureturing/blob/9ebc22c28bd51d31eafacb9320f91e96df4e6275/Problems/nuradha-mishra-leditzky-wilde-measured-fidelity-gap.md
[REC]: https://github.com/the-omega-institute/trureturing/blob/9ebc22c28bd51d31eafacb9320f91e96df4e6275/docs/develop/theory/AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md

## 追加锚（本行以下为增补区）
