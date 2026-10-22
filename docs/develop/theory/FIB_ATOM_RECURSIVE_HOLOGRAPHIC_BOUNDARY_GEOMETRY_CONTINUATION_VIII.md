# FIB atomic boundary geometry VIII: common exact heralding at the critical temperature

## 240. A native critical-temperature obstruction to common exact conversion

**Convention 240.0 (Source, numbering and mathematical scope).** This volume
continues [Continuation VII, §§215,226–230,235–239](https://github.com/the-omega-institute/trureturing/blob/b92a26f3f99eb2cdad322dbd60d0e95eadf7b024/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VII.md).
Numbers below 240 refer to that volume. The native preparation and fixed
registers are those of §§215,226,235–236; the common exact-success contract
is Definition 239.1. The argument here concerns a single fixed temperature
at which every required target is separable. It leaves the fixed-$1/10$
two-source result of Theorem 239.2 intact.

**Definition 240.1 (Actual native input and fixed output).** In the
one-particle coordinate order $(r,\ell,R)$ set

$$
\begin{gathered}
D=\{(q_1,q_2)\in\mathbb R^2:q_1>0,\ q_2>0,\ q_1+q_2<1\},\\
T=(1,1,1)^{\mathsf T},\qquad
L_\star=\begin{pmatrix}2&-1&-1\\-1&1&0\\-1&0&1\end{pmatrix},\\
\pi_q=(1-q_1-q_2,q_1,q_2)^{\mathsf T},\qquad
G_q=L_\star+\pi_q\pi_q^{\mathsf T},\qquad
S_q=G_q^{1/2},\qquad V_q=S_qT,\\
p=p(q)=|(V_q)_\ell|^2,\qquad
u_q=\frac{((V_q)_r,(V_q)_R)^{\mathsf T}}{\sqrt{1-p(q)}},\qquad
U_q=u_qu_q^*.
\end{gathered}
\tag{240.1}
$$

The square root is the positive principal root. Proposition 227.1 gives
$G_q\succ0$, $\|V_q\|=1$ and strictly positive coordinates of $V_q$;
in particular $0<p(q)<1$. Alice's cut remains the normalized coordinate
$\mathbb Ce_\ell$, and Bob's cut remains
$\operatorname{span}_{\mathbb C}\{e_r,e_R\}$. These are the fixed
normalized axes, without an additional rotation of the cut or an
identification with raw weighted occurrence subsystems.

At $t=e^{-\beta}\in(0,1]$, use two independent instances of the same
full Gibbs preparation

$$
\rho_{q,\beta}=
\frac{e^{-\beta d\Gamma_-(I_3-V_qV_q^*)}}{2(1+t)^2}
\quad\hbox{on }\mathcal F_-(\mathbb C^3).
\tag{240.2}
$$

All number sectors and the zero mode are retained. There is no chemical
potential or preliminary fixed-number conditioning. The labelled modes
and coupling phases of the two preparations are compatible as in
§§188,215,235–236. Apply the same coherent filter

$$
F=\Pi_{n_{A_1}+n_{A_2}=1}
  \Pi_{n_{r_1}+n_{R_1}+n_{r_2}+n_{R_2}=1}.
\tag{240.3}
$$

Bob's projector counts all four of Bob's modes. On its selected
one-particle space use the fixed identification of (235.2),
$J|x_i\rangle=|i\rangle_{\mathrm{copy}}|x\rangle_{\mathrm{space}}$
for $x\in\{r,R\}$ and $i\in\{1,2\}$. Alice's rail register and
Bob's copy register each have dimension two. The spatial register has
fixed ordered basis $(r,R)$. In Alice, copy, space order the actual
unnormalized selected state is (236.6):

$$
\begin{gathered}
\Omega_q=
\frac{(tI_4+2g(p)P_-)\otimes U_q
       +th(p)I_4\otimes(I_2-U_q)}{4(1+t)^4},\\
g(p)=(1-t)^2p(1-p),\qquad h(p)=t+(1-t)p,\\
|\psi^-\rangle=
\frac{|A_1\rangle|2\rangle_{\mathrm{copy}}
      -|A_2\rangle|1\rangle_{\mathrm{copy}}}{\sqrt2},\qquad
P_-=|\psi^-\rangle\langle\psi^-|.
\end{gathered}
\tag{240.4}
$$

Here $P_-$ is on Alice and copy. Its sign is the fixed CAR singlet
convention of (236.2)–(236.6): copy-to-party regrouping contributes
$(-1)^{N_{B_1}n_{A_2}}$ and the compatible exchange coherence is
$-|z|^2$. This is a passive coordinate sign, not a cross-party gate.
The active spatial projector is the actual $U_q$ of (240.1); the
orthogonal spectator projector is $I_2-U_q$. Thus (240.4) includes
every selected spectator population. A source-dependent spatial basis
can describe these blocks, but no source-dependent alignment is supplied
as a physical operation.

The full probability of $F$ and its normalized output are

$$
P_{\mathrm{full}}(q,t)=\operatorname{Tr}\Omega_q
 =\frac{4t(1+h(p))+2g(p)}{4(1+t)^4}>0,\qquad
\rho_q=\frac{\Omega_q}{P_{\mathrm{full}}(q,t)}.
\tag{240.5}
$$

The required output on one fixed encoded two-qubit register is

$$
\begin{gathered}
W_{\lambda(p)}=\frac{1-\lambda(p)}4I_4+\lambda(p)P_-
 =\frac{T_t(p)}{2t+g(p)},\\
\lambda(p)=\frac{g(p)}{2t+g(p)},\qquad
T_t(p)=\frac t2I_4+g(p)P_-.
\end{gathered}
\tag{240.6}
$$

The matrix $T_t(p)$ is distinct from the three-component vector $T$.
The output $P_-$ uses the same fixed rail labels as in (240.4).
Changing $q$ changes the required scalar $\lambda(p)$, not the output
register. A common completely positive map
$\mathcal E_t:M_8(\mathbb C)\to M_4(\mathbb C)$ is independent of
$q$. Exact heralding means

$$
\mathcal E_t(\rho_q)=s_qW_{\lambda(p(q))},\qquad s_q>0
\quad(q\in D).
\tag{240.7}
$$

No uniform positive lower bound on the individual $s_q$ is required.
For a physical success branch $\mathcal E_t$ is also trace-nonincreasing,
and the overall success probability is $P_{\mathrm{full}}(q,t)s_q$.
The same success branch must apply after the original filter and after
erasing all records except success; rejected outcomes are stopped.
The allowed processing of Definition 239.1 is finite adaptive LOCC
preserving each party's local total number, with separable auxiliaries,
neutral memories, classical communication and coins. It supplies no
additional input copy, entangled ancillary resource or external phase
reference. By §218 every such success branch is completely positive.

**Lemma 240.2 (An actual native open patch).** Let
$q_0=(1/3,1/3)$. Near $q_0$ define

$$
\theta(q)=\arctan\frac{(V_q)_R}{(V_q)_r}.
\tag{240.8}
$$

Then $(p(q_0),\theta(q_0))=(1/3,\pi/4)$, and

$$
\left.\frac{\partial(p,\theta)}{\partial(q_1,q_2)}\right|_{q_0}
=\begin{pmatrix}
\sqrt3/2-1/4&3/4-\sqrt3/2\\
15/16-3\sqrt3/8&3/16+3\sqrt3/8
\end{pmatrix},\qquad
\det=\frac{3(\sqrt3-1)}4>0.
\tag{240.9}
$$

Consequently there are nonempty open intervals $I\subset(0,1)$ and
$K\subset(0,\pi/2)$ containing $1/3$ and $\pi/4$, respectively,
such that every $(p,\theta)\in I\times K$ is realized by an actual
$q\in D$ through (240.1) and (240.8).

Proof. At $q_0$, $\pi_{q_0}=T/3$ and
$G_{q_0}T=T/3$, so $S_{q_0}T=T/\sqrt3$. Positivity of $G_q$
near $q_0$ makes its principal root smooth. Differentiating
$S_q^2=G_q$ gives the Sylvester equation

$$
S_{q_0}\,dS+dS\,S_{q_0}
 =d\pi\,\pi_{q_0}^{\mathsf T}
  +\pi_{q_0}\,d\pi^{\mathsf T},\qquad
d\pi=(-dq_1-dq_2,dq_1,dq_2)^{\mathsf T}.
\tag{240.10}
$$

Since $d\pi^{\mathsf T}T=0$, applying this equation to $T$ yields

$$
dV=(S_{q_0}+I_3/\sqrt3)^{-1}d\pi.
\tag{240.11}
$$

For an explicit evaluation, put $e=(0,1,-1)^{\mathsf T}$ and
$f=(-2,1,1)^{\mathsf T}$. The mutually orthogonal vectors $T,e,f$
are eigenvectors of $G_{q_0}$ with eigenvalues $1/3,1,3$.
On $T^\perp$ the inverse in (240.11) therefore equals

$$
\frac{3-\sqrt3}{2}\frac{ee^{\mathsf T}}2
 +\frac{\sqrt3}{4}\frac{ff^{\mathsf T}}6.
\tag{240.12}
$$

Substitution of $d\pi$ gives

$$
\begin{aligned}
d(V_q)_r&=-\frac{\sqrt3}{4}(dq_1+dq_2),\\
d(V_q)_\ell&=
 \left(\frac34-\frac{\sqrt3}{8}\right)dq_1
 +\left(-\frac34+\frac{3\sqrt3}{8}\right)dq_2,\\
d(V_q)_R&=
 \left(-\frac34+\frac{3\sqrt3}{8}\right)dq_1
 +\left(\frac34-\frac{\sqrt3}{8}\right)dq_2.
\end{aligned}
\tag{240.13}
$$

At $q_0$ one has
$dp=2\,d(V_q)_\ell/\sqrt3$ and
$d\theta=\sqrt3\bigl(d(V_q)_R-d(V_q)_r\bigr)/2$.
These identities give (240.9). The ordinary real inverse function
theorem applies to this smooth two-dimensional map at the interior
point $q_0$. Its image contains an open neighborhood of
$(1/3,\pi/4)$ and hence a rectangle $I\times K$ as stated.
Every point in this rectangle comes from the same joint principal-root
construction with $q\in D$. This is local joint realizability, not an
independent global choice of $p$ and the spatial ray. Neither a globally
free ray family nor a source-aware operation is used.

**Theorem 240.3 (Critical-temperature common-map obstruction).** Fix

$$
t=t_c=3-2\sqrt2\in(0,1).
\tag{240.14}
$$

For every $q\in D$, the target $W_{\lambda(p(q))}$ of (240.6) is
separable. Nevertheless the only completely positive map
$\mathcal E:M_8(\mathbb C)\to M_4(\mathbb C)$ satisfying

$$
\mathcal E(\Omega_q)=m_qW_{\lambda(p(q))}
\quad\hbox{for every }q\in D,
\qquad m_q\ge0,
\tag{240.15}
$$

is $\mathcal E=0$. In particular no common success map satisfies
(240.7), and no allowed finite adaptive local-number-preserving LOCC
instrument with the preparation and failure contract of Definition 240.1
can produce the exact required output with positive success for every
native $q\in D$ at this fixed temperature.

Proof. First, the scalar bound of Corollary 230.2, or directly
$p(1-p)\le1/4$ in (240.6), gives

$$
\lambda(p(q))\le
\frac{(1-t)^2}{1+6t+t^2}.
\tag{240.16}
$$

The identity $t_c^2-6t_c+1=0$ is equivalent to
$(1-t_c)^2=4t_c$. Thus the right side of (240.16) is $1/3$.
The two-qubit states $W_\lambda$ here are separable for
$0\le\lambda\le1/3$, by the criterion used in §§215,238:
their partial-transpose eigenvalues are $(1+\lambda)/4$ three times
and $(1-3\lambda)/4$ once, and the two-qubit PPT criterion applies.
This proves the all-source separable-target condition at the allowed
fixed temperature (240.14).

Suppose now that $\mathcal E$ satisfies (240.15). All subsequent
quantities use this fixed $t$. In the fixed spatial basis define

$$
\sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
Z_\theta=\cos(2\theta)\sigma_z+\sin(2\theta)\sigma_x.
\tag{240.17}
$$

The native coordinates are positive and real. Hence for the actual
sources in Lemma 240.2,
$u_q=(\cos\theta,\sin\theta)^{\mathsf T}$ and
$U_q=U_\theta=(I_2+Z_\theta)/2$. Suppress only the positive
$q$-independent denominator $C_t=4(1+t)^4$ of (240.4), writing
$N(p,\theta)=C_t\Omega_q$. Its exact decomposition is

$$
\begin{gathered}
N(p,\theta)=\frac12\bigl(A_0(p)\otimes I_2
                           +A_1(p)\otimes Z_\theta\bigr),\\
A_0(p)=a(p)I_4+b(p)P_-,\qquad
a(p)=t(1+t+(1-t)p),\\
b(p)=2(1-t)^2p(1-p)=2g(p),\qquad
A_1(p)=t(1-h(p))I_4+2g(p)P_-.
\end{gathered}
\tag{240.18}
$$

Set $F_0(X)=\mathcal E(X\otimes I_2)$ for
$X\in M_4(\mathbb C)$. This linear map is distinct from the
coherent filter $F$ in (240.3). Fix any $p\in I$ and let
$Q_p:M_4(\mathbb C)\to
M_4(\mathbb C)/\operatorname{span}_{\mathbb C}\{T_t(p)\}$
be the linear quotient map. Exactness of (240.15), together with
(240.6), implies for every $\theta\in K$ that

$$
\begin{aligned}
0={}&Q_pF_0(A_0(p))\\
&+\cos(2\theta)\,
 Q_p\mathcal E(A_1(p)\otimes\sigma_z)\\
&+\sin(2\theta)\,
 Q_p\mathcal E(A_1(p)\otimes\sigma_x).
\end{aligned}
\tag{240.19}
$$

The scalar functions $1,\cos(2\theta),\sin(2\theta)$ are linearly
independent on every open interval. Indeed differentiating a vanishing
linear combination twice eliminates its constant term; the remaining
combination and its first derivative force both other coefficients to
vanish. Apply this fact to each coordinate of the finite-dimensional
quotient in (240.19). The constant coefficient must vanish, proving

$$
F_0(A_0(p))\in\operatorname{span}_{\mathbb C}\{T_t(p)\}
\quad(p\in I).
\tag{240.20}
$$

The two scalar polynomials $a,b$ are linearly independent on $I$:
$a$ has degree one with nonzero constant term, whereas $b$ has degree
two with nonzero quadratic coefficient. A polynomial identity
$\alpha a+\beta b=0$ on $I$ therefore forces $\beta=0$ and
then $\alpha=0$. Thus the vectors $(a(p),b(p))$, $p\in I$,
span a two-dimensional space, and the matrices $A_0(p)$ span
$\operatorname{span}\{I_4,P_-\}$. Each image in (240.20) belongs
to this same latter span, since $T_t(p)$ does. Taking two independent
$A_0(p)$ and inverting their coefficient matrix shows separately that
$F_0(I_4)$ and $F_0(P_-)$ belong to that span. Consequently write

$$
F_0(I_4)=xI_4+yP_-,\qquad
F_0(P_-)=zI_4+rP_-.
\tag{240.21}
$$

The coefficients are real because $F_0$ preserves Hermitian matrices.
Since $T_t(p)=(tI_4+b(p)P_-)/2$, proportionality (240.20) is
equivalent to

$$
t\bigl(a(p)y+b(p)r\bigr)
 =b(p)\bigl(a(p)x+b(p)z\bigr)
\quad(p\in I).
\tag{240.22}
$$

Both sides are polynomials, so equality on the nonempty open interval
$I$ is a polynomial identity. Put $c=(1-t)^2>0$; then
$a=t(1+t)+t(1-t)p$ and $b=2cp-2cp^2$. The constant coefficient
in (240.22) is $t^2(1+t)y$ on the left and zero on the right,
so $y=0$. Its fourth-degree coefficient is zero on the left and
$4c^2z$ on the right, so $z=0$. The remaining identity is

$$
b(p)\bigl(tr-a(p)x\bigr)=0.
\tag{240.23}
$$

For $p\in I\subset(0,1)$ one has $b(p)>0$, so
$tr=a(p)x$ throughout $I$. Comparing the coefficient of $p$ gives
$t(1-t)x=0$, hence $x=0$; the constant coefficient then gives
$tr=0$, hence $r=0$. These are coefficient comparisons in a
polynomial identity. No source with $p=0$ or $p=1$ is asserted to
belong to $D$ or to the actual patch.

In particular (240.21) gives
$\mathcal E(I_8)=F_0(I_4)=0$. Complete positivity implies positivity.
For every positive matrix $X\in M_8(\mathbb C)$,

$$
0\le\mathcal E(X)\le\|X\|\mathcal E(I_8)=0,
\tag{240.24}
$$

because $0\le X\le\|X\|I_8$. Thus $\mathcal E$ vanishes on
positive matrices, hence on Hermitian matrices by positive and negative
parts, and on all matrices by complex linearity. This proves
$\mathcal E=0$. The proof of this zero-map assertion used only the
target-ray equality in (240.15); allowing zero masses does not supply a
nonzero map. Trace-nonincreasingness was not needed for the obstruction.

Finally, (240.7) would give (240.15) with
$m_q=P_{\mathrm{full}}(q,t)s_q>0$ by (240.5), contradicting
$\mathcal E=0$. Erasing the leaves of any allowed finite adaptive
LOCC success event sums their completely positive maps, so the same
contradiction applies to the required common instrument. Restoring
$C_t$ changes only the success scalar. Filter rejection has probability
$1-P_{\mathrm{full}}$; subsequent conditional failure has probability
$P_{\mathrm{full}}(1-s_q)$; success would have probability
$P_{\mathrm{full}}s_q$. The argument changes none of this accounting
and uses no positive uniform lower success bound.

The source-specific content of Lemma 240.2 and Theorem 240.3 is
`repo-derived`: it combines the native geometry of §§215,226–230,
the actual CAR and spectator law of §§235–236, and the fixed exact-success
contract of §239. Smoothness of the positive matrix square root, the
real inverse function theorem, polynomial identity on an interval and
positivity of a completely positive map are standard mathematical tools
used within these proofs. The separability criterion and the thermal
bound are the existing suppliers in §§215,230,238. No literature-priority
claim is attached to this source-specific consequence.

The theorem concerns $t=t_c$ and the exact requirement for every actual
$q\in D$. The local rectangle is a proof device inside that family;
it does not authorize arbitrary rays, global independent source parameters
or source-aware control. The physical input remains the two compatible
full Gibbs preparations followed by the original coherent filter, with
the fixed normalized cut, register $J$ and CAR convention. Preliminary
individual-copy measurements or independent per-copy twirls change that
input and are not part of the argument. The theorem determines neither
approximate conversion, source-restricted conversion, other temperatures,
additional resources nor optimization on the original unfiltered
$64$-dimensional resource. Preparation availability and ideal local control
are assumptions; physical synthesis, costs and kernel certification are
not conclusions of these ordinary mathematical proofs.

## 追加锚（本行以下为增补区）

## 241. The native conditional CP approximation gap

**Definition 241.1 (Registered CP comparison and approximation gap).** Fix
$t=t_c=3-2\sqrt2$. Retain the actual jointly generated family
$q\mapsto(p(q),U_q,\Omega_q)$ on

$$
D=\{(q_1,q_2)\in\mathbb R^2:q_1>0,\ q_2>0,\ q_1+q_2<1\}
$$

from Definition 240.1, including its positive principal-root construction,
and retain the fixed encoded output

$$
W_q=W_{\lambda(p(q))}
 =\frac{1-\lambda(p(q))}{4}I_4+\lambda(p(q))P_-.
$$

The comparison class is

$$
\mathcal C=\left\{\begin{array}{l|l}
\mathcal E:M_8(\mathbb C)\to M_4(\mathbb C) &
\begin{array}{l}
\mathcal E\text{ is one nonzero complex-linear completely positive}\\
\text{trace-nonincreasing map, independent of }q,\text{ and}\\
\operatorname{Tr}\mathcal E(\Omega_q)>0\text{ for every actual }q\in D
\end{array}
\end{array}\right\}.
$$

Here the CP class is a comparison superclass; it is not an additional
physical operation menu. Define the registered conditional approximation gap
by the infimum-over-maps, supremum-over-the-actual-family quantity

$$
\delta_{\mathrm{CP}}
 =\inf_{\mathcal E\in\mathcal C}\ \sup_{q\in D}
 \frac12\left\|
 \frac{\mathcal E(\Omega_q)}{\operatorname{Tr}\mathcal E(\Omega_q)}-W_q
 \right\|_1.
$$

The positivity condition is pointwise in $q$ for each one fixed map. No
positive success floor is imposed either within a map or across maps.

**Corollary 241.2 (Strict native conditional approximation gap).** For the
fixed $t_c$ and the exact native family of Definition 240.1,

$$
\delta_{\mathrm{CP}}>0.
$$

Equivalently, there is an $\varepsilon>0$, common to the maps, such that every
$\mathcal E\in\mathcal C$ satisfies

$$
\sup_{q\in D}\frac12\left\|
\frac{\mathcal E(\Omega_q)}{\operatorname{Tr}\mathcal E(\Omega_q)}-W_q
\right\|_1\ge\varepsilon.
$$

Proof. Theorem 240.3 says that the only completely positive map satisfying

$$
\mathcal E(\Omega_q)=m_qW_q\quad(q\in D),\qquad m_q\ge0,
$$

is the zero map. We use that assertion on the actual jointly generated
family. The local rectangle in Lemma 240.2 is only a proof device inside
that family; it does not replace it by independent ray parameters. The input
$\Omega_q$ is exactly (240.4), with the fixed singlet phase and fixed
Alice--copy--space ordering, and it retains the spectator block.

Write $C_t=4(1+t)^4$. At $t=t_c$ one has
$(1-t)^2=4t$. Definition 240.1 gives $0<p(q)<1$, hence

$$
0<g(p(q))\le t,\qquad t<h(p(q))<1.
$$

Since $U_q$ is a rank-one orthogonal projector, the numerator of (240.4)
has, on its active spatial block, eigenvalues $t+2g(p(q))$ once and $t$
three times; on its spectator block it has eigenvalue $t h(p(q))$ four
times. Consequently, uniformly for every actual $q\in D$,

$$
mI_8\le\Omega_q\le MI_8,\qquad
m=\frac{t^2}{C_t}>0,\qquad M=\frac{3t}{C_t}.
$$

For a nonzero completely positive map $\mathcal E$, set
$a=\operatorname{Tr}\mathcal E(I_8)$. Then $a>0$: if
$\mathcal E(I_8)=0$, positivity and
$0\le X\le\|X\|I_8$ for $X\ge0$ imply
$0\le\mathcal E(X)\le\|X\|\mathcal E(I_8)=0$, so complex linearity gives
$\mathcal E=0$. Put $\Phi=\mathcal E/a$. It is completely positive and
$\operatorname{Tr}\Phi(I_8)=1$. If
$B=\Phi^*(I_4)$, then $B\ge0$ and $\operatorname{Tr}B=1$, so
$B\le I_8$; thus $\Phi$ is trace-nonincreasing. Moreover, for every
actual $q$,

$$
m\le a_q:=\operatorname{Tr}\Phi(\Omega_q)\le M.
$$

The original map therefore has the derived uniform success bound
$\operatorname{Tr}\mathcal E(\Omega_q)=a a_q\ge a m$ for this fixed
$\mathcal E$. This is a consequence of the actual input bounds, not a
restriction imposed in Definition 241.1. Scalar rescaling can make $a$ and
all these successes arbitrarily small across maps, while leaving every
conditional output unchanged; no assertion is made that success tends to
zero in $q$ for a fixed map. Conversely, every completely positive $\Phi$
with $\operatorname{Tr}\Phi(I_8)=1$ is trace-nonincreasing and has positive
success on every actual input, so it is an admissible normalized
representative.

Use the output-first Choi matrix

$$
J(\Phi)=\sum_{i,j=1}^{8}\Phi(|i\rangle\langle j|)\otimes
|i\rangle\langle j|.
$$

Watrous, *The Theory of Quantum Information*, Chapter 2, Theorem 2.22 and
equations (2.65)--(2.66), give complete positivity exactly as
$J(\Phi)\ge0$ and give the linear inverse from $J(\Phi)$ to $\Phi$.
The normalized representatives are therefore identified with the compact
finite-dimensional slice

$$
K=\{J\in\operatorname{Herm}(\mathbb C^4\otimes\mathbb C^8):J\ge0,
\operatorname{Tr}J=1\},
$$

because $\operatorname{Tr}J(\Phi)=\operatorname{Tr}\Phi(I_8)=1$.

For a normalized representative define, for each actual $q$,

$$
R_q(\Phi)=\Phi(\Omega_q)-a_qW_q,\qquad
\eta=\inf_{\Phi\,:,J(\Phi)\in K}\ \sup_{q\in D}\|R_q(\Phi)\|_1.
$$

This is finite: $\Phi(\Omega_q)$ and $a_qW_q$ are positive with the same
trace $a_q$, so $\|R_q(\Phi)\|_1\le2a_q\le2M$. Suppose for contradiction
that $\eta=0$. Choose normalized maps $\Phi_n$ with
$\sup_{q\in D}\|R_q(\Phi_n)\|_1\to0$. Compactness of $K$ supplies one
convergent subsequence of their Choi matrices, with limit $J_*$ and map
$\Phi_*$. For every fixed actual $q$, Choi inversion and finite-dimensional
linearity give

$$
R_q(\Phi_*)=\lim_n R_q(\Phi_n)=0.
$$

The same single subsequence works for every fixed $q$ because the preceding
residual bound was a supremum over all of $D$; no compactness of $D$ and no
source-dependent subsequence is used. Thus
$\Phi_*(\Omega_q)=\operatorname{Tr}\Phi_*(\Omega_q)W_q$ for every actual
$q$, with nonnegative masses (indeed at least $m$). Theorem 240.3 forces
$\Phi_*=0$, contradicting
$\operatorname{Tr}\Phi_*(I_8)=1$. Hence $\eta>0$.

Finally, for an arbitrary original $\mathcal E\in\mathcal C$ use its
normalized representative $\Phi$ and set

$$
d_q=\frac12\left\|\frac{\Phi(\Omega_q)}{a_q}-W_q\right\|_1.
$$

The exact identity $\|R_q(\Phi)\|_1=2a_qd_q$ and $a_q\le M$ yield

$$
\eta\le\sup_{q\in D}\|R_q(\Phi)\|_1
\le2M\sup_{q\in D}d_q.
$$

Normalization does not change conditional outputs, so infimizing over the
original class gives

$$
\delta_{\mathrm{CP}}\ge\frac{\eta}{2M}>0.
$$

Taking $\varepsilon=\eta/(2M)$ proves the corollary. This is a nonnumeric
source-specific ordinary consequence of the native zero-map obstruction and
standard finite-dimensional Choi compactness. It neither computes an
optimal gap nor supplies an optimizer or a physical realization. The
preparation remains the two independent compatible full Gibbs states with
all sectors and the zero mode, followed by the coherent filter selecting
Alice total number one and Bob total number one across all four Bob modes;
the fixed normalized cut, identification $J$, CAR regrouping sign, and all
spectator populations are those of §§235--236 and (240.1)--(240.4). The
success record alone is retained and filter rejection and later failure are
stopped as in (240.7) and Definition 239.1. No extra copy, entangled
ancilla, external phase reference, per-copy occupation measurement,
source-aware alignment, other temperature or resource, achievable approximate
conversion protocol, or optimization on the unfiltered $64$-dimensional input
is part of this statement.

## 追加锚（本行以下为增补区）
