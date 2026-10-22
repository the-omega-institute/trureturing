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

## 242. Fixed overall success over the native source family

All references numbered 214–234 below are to [Continuation VII](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VII.md); references numbered 242 belong to this section. The source-choice question is the fixed-overall-success question of VII §234, with its original preparation and operation menu.

**Convention 242.0 (native source and operation contract).** Retain the stopped singleton history and actual coordinate order $(r,\ell,R)$ of VII Definition 226.1. Explicitly, with $q=(u,v)$,

$$
\begin{gathered}
D=\{(u,v):u>0,\ v>0,\ u+v<1\},\qquad T=(1,1,1)^\top,\\
L_\star=\begin{pmatrix}2&-1&-1\\-1&1&0\\-1&0&1\end{pmatrix},\qquad
\pi_q=(1-u-v,u,v)^\top,\\
G_q=L_\star+\pi_q\pi_q^\top,\qquad S_q=G_q^{1/2},\qquad V_q=S_qT,\\
\|V_q\|=1,\qquad H_q=S_q^{-1}L_\star S_q^{-1}=I_3-V_qV_q^*,\\
\mathfrak h=\mathbb C e_\ell\oplus\operatorname{span}_{\mathbb C}\{e_r,e_R\},
\qquad p(q)=|(V_q)_\ell|^2.
\end{gathered}
\tag{242.0a}
$$

Here $G_q^{1/2}$ is the positive principal square root; the cut is the second coordinate after this normalization, with no additional cut rotation. The exact endpoints of VII Definition 226.2 are specified by the unique root $\sigma_*\in(13/4,7/2)$ of $\sigma_*^3-\sigma_*^2-9\sigma_*+1=0$ and

$$
\tau_*=\frac{\sigma_*^2-5}{2},\qquad H_*=\sigma_*\tau_*-1,\qquad
m=\frac{\sigma_*^2}{H_*^2},\qquad
M=\frac{(\sigma_*+\tau_*+3)^2}{H_*^2}.
\tag{242.0b}
$$

VII Theorems 228.1 and 229.1 give $0<m<1/2<M<1$ and $I=p(D)=(m,M)$. The endpoints occur only at excluded boundary sources, while every point of $I$ has an actual interior inverse. The closed extension used to establish those endpoints is not an admissible source domain here.

All preparations and instruments below use the exact known-source, same-temperature, two-compatible-full-Gibbs-preparation plus one-prepared-copy finite local-number-preserving LOCC menu of VII §§214–220 and 233. The source-informed Bob basis, fixed CAR phases, neutral memories, separable auxiliaries, finite communication and exact biased coins are part of this contract. Both independent preparations have the same actual $q$ and $t$; the subsequent instrument acts on one resulting prepared copy. No extrema belonging to different sources are combined. In the common encoded qubit basis put

$$
W_\lambda=\lambda|\Psi^-\rangle\langle\Psi^-|+(1-\lambda)I_4/4,
\qquad |\Psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2,
\qquad N(\rho)=\frac{\|\rho^{T_A}\|_1-1}{2}.
\tag{242.0c}
$$

These are the singlet and ordinary-negativity conventions of VII §§215 and 224.

**Definition 242.1 (fixed-overall-success scalar data).** Write $a_+=\max\{a,0\}$. For
$0<t\le1$, $R\in(0,1]$, $p\in I$ and $q=(u,v)\in D$ with $p=p(q)$, write

$$
\begin{gathered}
b=1-t,\qquad U_t(p)=b^2p(1-p),\qquad h_t(p)=t+bp,\\
Z_t(p)=2t+U_t(p),\qquad E_t(p)=Z_t(p)+2t h_t(p),\\
A_t(p)=\frac{(U_t(p)-t)_+}{2Z_t(p)},\qquad
C=2(1+t)^4,\qquad L=CR.
\end{gathered}
\tag{242.1}
$$

At the same source, the full preparation and its active and spectator
probabilities supplied by (220.5) and (233.4) are

$$
P_a=\frac{Z_t(p)}C,\qquad
P_{\mathrm{sp}}=\frac{2t h_t(p)}C,\qquad
P_{\mathrm{full}}=\frac{E_t(p)}C.
\tag{242.2}
$$

For prescribed overall success $R\in(0,1]$, call $q$ feasible when
$P_{\mathrm{full}}\ge R$. The fixed-source frontier of Theorem 214.1,
with the conditional success set to $s=R/P_{\mathrm{full}}$, is therefore

$$
F_R(p)=A_t(p)\min\left\{1,\frac{Z_t(p)}{CR}\right\}
      =\frac{(U_t(p)-t)_+}{2\max\{Z_t(p),L\}},
\qquad E_t(p)\ge L.
\tag{242.3}
$$

The second identity is only a normalization of the first one; the fixed-
source upper bound and its finite attainer are the already established
results of §§214 and 219.

**Theorem 242.2 (complete native fixed-overall-success characterization).**
For every $t\in(0,1]$ and $R\in(0,1]$, let

$$
\mathcal Q_{t,R}=\left\{q\in D:\frac{E_t(p(q))}{2(1+t)^4}\ge R\right\}.
\tag{242.4}
$$

If $t=1$, then $\mathcal Q_{1,R}=D$ exactly for $0<R\le1/8$, and it is
empty for $R>1/8$. In the former case the optimum is $G=0$ and every
$q\in D$ is a maximizer; in the latter case the problem is infeasible.

Suppose $0<t<1$. Put

$$
\eta=\frac{1+t}{2(1-t)},\qquad z=\min\{\eta,M\},\qquad
K=\frac{E_t(z)}{C}.
\tag{242.5}
$$

The feasible set is nonempty exactly when

$$
R<K,\qquad\text{or}\qquad R=K\ \text{and}\ \eta<M.
\tag{242.6}
$$

For every feasible $R$, define

$$
p_*=\begin{cases}
\dfrac12,&CR\le E_t(1/2),\\[6pt]
\dfrac{(1+t)-\sqrt{(1+t)(1+9t)-4CR}}{2(1-t)},
&CR>E_t(1/2).
\end{cases}
\tag{242.7}
$$

Then $p_*\in(m,M)$ and the exact native optimum is

$$
G=F_R(p_*)=A_t(p_*)
\min\left\{1,\frac{Z_t(p_*)}{CR}\right\}.
\tag{242.8}
$$

The complete maximizing-source set is

$$
\operatorname*{Argmax}_{q\in\mathcal Q_{t,R}}F_R(p(q))
=\begin{cases}
\mathcal Q_{t,R},&G=0,\\
\{q\in D:p(q)=p_*\},&G>0.
\end{cases}
\tag{242.9}
$$

In particular, the second line is the entire native fibre and not a claim
that the source coordinates themselves are unique. At every source in the
right-hand side of (242.9), one declared finite instrument, following the
specified original preparation, realizes overall success $R$, one common
encoded two-qubit success output with all finer records erased, negativity
$G$, and total failure probability $1-R$.

**Proof of Theorem 242.2.** First take $t=1$. Then $U_1=0$, $h_1=1$,
$Z_1=2$, $E_1=4$ and $C=32$, independently of $p$. Thus (242.4) is all
of $D$ precisely for $R\le1/8$ and is empty for larger $R$. Equation
(242.3) is zero on the nonempty set, so every native source maximizes zero.
An empty feasible set is infeasibility, not a zero-valued optimum. The
instrument constructed below remains valid at $t=1$ because it uses no
division by $1-t$.

Now let $0<t<1$ and put $b=1-t$. Direct expansion gives

$$
\begin{aligned}
E_t(p)&=2t(1+t)+b(1+t)p-b^2p^2\\
&=H-b^2(p-\eta)^2,
\qquad H=\frac{(1+t)(1+9t)}4.
\end{aligned}
\tag{242.10}
$$

Hence $E_t$ is strictly increasing up to $\eta$ and strictly decreasing
after $\eta$. Since $\eta>1/2>m$, its supremum on the open interval
$I=(m,M)$ is $E_t(z)$. If $\eta<M$, the point $\eta$ is in $I$ and the
supremum is attained. If $\eta\ge M$, every point of $I$ has value strictly
below $E_t(M)$, including the case $\eta=M$; $E_t(M)$ is only approached as
$p\uparrow M$. Therefore the superlevel set

$$
S_R=\{p\in I:E_t(p)\ge L\}
\tag{242.11}
$$

is nonempty exactly under (242.6). When it is nonempty, completing the
square also gives

$$
S_R=I\cap\left[\eta-\frac{\sqrt{H-L}}b,
                 \eta+\frac{\sqrt{H-L}}b\right].
\tag{242.12}
$$

The native feasible set is exactly the full inverse image of $S_R$ under
$p:D\to I$.

It remains to optimize the fixed-$R$ objective. For $y>t$, the two functions

$$
\frac{y-t}{2(2t+y)},\qquad \frac{y-t}{2L}
\tag{242.13}
$$

are strictly increasing: the second has positive slope, while for
$t<x<y$ the first has difference

$$
\frac{3t(y-x)}{2(2t+y)(2t+x)}>0.
\tag{242.14}
$$

The minimum is strictly increasing as well: for $t<x<y$, choose either function attaining the minimum at $y$ and compare its value at $x$ with the minimum at $x$. Thus this minimum is strictly increasing on $(t,\infty)$, and
the positive-part extension is nondecreasing and is zero on $[0,t]$.
Since (242.3) is exactly this function evaluated at $U_t(p)$, the source
choice depends monotonically only on $U_t(p)$, with strictness whenever the
value is positive. The identity

$$
U_t(p)=b^2\left(\frac14-(p-\tfrac12)^2\right)
\tag{242.15}
$$

shows that $U_t$ has its unique scalar maximum at $1/2$.

If $L\le E_t(1/2)$, then $1/2\in S_R$ and (242.15) proves that $p_*=1/2$
maximizes (242.3). If the resulting value is positive, strictness in
(242.13) forces equality only at $p=1/2$. If it is zero, every feasible
point has value zero, including the equality case $L=E_t(1/2)$.

Assume instead that $L>E_t(1/2)$. No feasible point can lie at or to the
left of $1/2$, because $E_t$ is increasing there. If $L<E_t(z)$, there is a
unique $a\in(1/2,z)$ with $E_t(a)=L$. If $L=E_t(z)$ is feasible, (242.6)
forces $\eta<M$ and $a=\eta$. In both cases $a\in(1/2,M)$ and is feasible.
Solving $E_t(a)=L$ with (242.10) gives

$$
a=\eta-\frac{\sqrt{H-L}}b
 =\frac{(1+t)-\sqrt{(1+t)(1+9t)-4L}}{2(1-t)},
\tag{242.16}
$$

which is (242.7). Strict increase of $E_t$ on $(1/2,a)$ gives $E_t(p)<L$ there, so every feasible $p$ satisfies $p\ge a$. On $[1/2,M)$, $U_t$ is strictly decreasing, so $a$ is the unique maximizer of $U_t$ on $S_R$. This proves (242.8) and the strict-positive
part of (242.9); if its value is zero, the nonnegative objective and the
same upper bound again make every feasible source a maximizer. The
discriminant in (242.16) is nonnegative by feasibility, and it vanishes
exactly at the attained interior vertex $a=\eta$.

For completeness, the zero branch can be located independently. Put
$t_c=3-2\sqrt2$. Since $U_t(p)\le(1-t)^2/4$, every value is zero for
$t_c\le t\le1$, and the bound $U_t(p)\le t$ is an equality at $t=t_c$ only for $p=1/2$. For
$0<t<t_c$, let

$$
p_\pm=\frac12\left(1\pm\sqrt{1-\frac{4t}{(1-t)^2}}\right).
\tag{242.17}
$$

Then $G>0$ exactly when the selected $p_*$ lies in $(p_-,p_+)$; at the
endpoints and outside it the value is zero. This does not alter the
maximizer classification above.

Finally, every selected scalar $p_*$ lies in $I$. By Theorem 229.1 choose
$n\ge2$ large enough that, with $\varepsilon=1/n$,

$$
p(0,1-\varepsilon)<p_*<p(1-\varepsilon,0).
\tag{242.18}
$$

There is a unique $\xi\in(0,1)$ satisfying

$$
p\big((1-\varepsilon)\xi,(1-\varepsilon)(1-\xi)\big)=p_*.
\tag{242.19}
$$

The resulting $q_*=((1-\varepsilon)\xi,(1-\varepsilon)(1-\xi))$ has positive coordinates and sum $1-\varepsilon<1$, so $q_*\in D$ is an actual native source. The scalar maximum is attained rather than merely approached at an excluded endpoint. Every
source with the same $p$ has the same feasibility and objective. If $G>0$,
strictness gives exactly the fibre in (242.9); if $G=0$, all feasible
sources have the common zero value. This proves the theorem. ∎

**Proposition 242.3 (same-source preparation and finite instrument).** Fix
any maximizing $q$ of Theorem 242.2, including its $t=1$ case, and evaluate every symbol below at its
actual $p=p(q)$ and the same $t$. Use the two independent compatible full
Gibbs states

$$
\rho_{q,\beta}=\frac{e^{-\beta d\Gamma_-(H_q)}}{2(1+t)^2},
\qquad t=e^{-\beta},
\tag{242.20}
$$

on $\mathcal F_-(\mathbb C^3)=\bigoplus_{j=0}^3\Lambda^j\mathbb C^3$, with the zero mode and all number sectors retained and $\beta=-\log t$. Apply the
source-informed even Bob-local alignment and the CAR order of (215.5)--
(215.8), then the original coherent common filter (215.9): Alice's two
copies have total number one and all four Bob modes have total number one. Explicitly,

$$
F=\Pi_{n_{A_1}+n_{A_2}=1}\Pi_{n_{r_1}+n_{R_1}+n_{r_2}+n_{R_2}=1}.
$$

The copy-first order $(A_1,b_1,\varsigma_1,A_2,b_2,\varsigma_2)$ and party-first order $(A_1,A_2,b_1,\varsigma_1,b_2,\varsigma_2)$ are related by the passive CAR sign $(-1)^{(n_{b_1}+n_{\varsigma_1})n_{A_2}}$ of (215.8).
No preliminary spectator-discarding filter is inserted. Equations
(215.10)--(215.12) and (220.5) give

$$
\rho_{\mathrm{filtered}}=wW_\lambda\oplus_B(1-w)\frac{I_4}{4},
\qquad \lambda=\frac{U_t(p)}{Z_t(p)},\qquad
w=\frac{Z_t(p)}{E_t(p)},
\tag{242.21}
$$

with the three probabilities in (242.2). Since $t>0$, $h_t>0$ and $Z_t>0$, one has $P_a,P_{\mathrm{sp}}>0$, $0\le\lambda<1$ and $0<w<1$, precisely the hypotheses of the reused fixed-source construction. Set

$$
s=\frac{R}{P_{\mathrm{full}}}=\frac{L}{E_t(p)},\qquad
\alpha=\min\left\{1,\frac{R}{P_a}\right\}
       =\min\left\{1,\frac{L}{Z_t(p)}\right\},
\tag{242.22}
$$

and

$$
\gamma=\frac{(R-P_a)_+}{P_{\mathrm{sp}}}
       =\frac{(L-Z_t(p))_+}{2t h_t(p)},\qquad
x=\min\left\{1,\frac{P_a}{R}\right\}
       =\min\left\{1,\frac{Z_t(p)}L\right\}.
\tag{242.23}
$$

Feasibility gives $0<s\le1$ and $\alpha,\gamma\in[0,1]$. With the source-informed
active rails $b_1,b_2$ and spectator rails $\varsigma_1,\varsigma_2$, the
success Kraus maps of (219.3) are

$$
\begin{gathered}
K_a=\sqrt{\alpha}\,I_A\otimes
 \left(|0\rangle_{B,\mathrm{out}}\langle b_1|
      +|1\rangle_{B,\mathrm{out}}\langle b_2|\right),\\
K_{ij}=\sqrt{\gamma}\,|0\rangle_A\langle i|\otimes
 |1\rangle_{B,\mathrm{out}}\langle\varsigma_{j+1}|,
\qquad i,j\in\{0,1\},\\
K_a^*K_a+\sum_{i,j}K_{ij}^*K_{ij}
 =I_A\otimes(\alpha\Pi_{\mathrm{act}}+\gamma\Pi_{\mathrm{sp}})\le I.
\end{gathered}
\tag{242.24}
$$

Bob measures the active and spectator subspaces coherently within each
sector, accepts their exact coins, and communicates the outcome. Alice keeps
the active encoded qubit on active success. On spectator success she resets
to $|0\rangle$ and Bob resets to the same output code's $|1\rangle$.
Rejected coin and flag outcomes give the finite failure complement, with active and spectator effects $I_A\otimes(1-\alpha)\Pi_{\mathrm{act}}$ and $I_A\otimes(1-\gamma)\Pi_{\mathrm{sp}}$. Every displayed local ket has local total number one. In particular, the neutral-memory reset dilation of (219.8) is $|i\rangle|\mathrm{ready}\rangle_E\mapsto|\mathrm{target}\rangle|i\rangle_E$, where the memory states are neutral and orthogonal. It is an isometry within the local number-one sector and extends to a unitary there. The analogous sector-to-code map stores its rail information in a neutral memory; block-diagonal identity or failure extensions act on other number sectors. Thus each party's number is preserved separately, using separable auxiliaries and finite communication. After discarding all finer rail, sector and coin records and their environments,
the single common normalized success output is

$$
\sigma_R=xW_\lambda+(1-x)|01\rangle\langle01|,\qquad
N(\sigma_R)=xA_t(p)=F_R(p)=G.
\tag{242.25}
$$

Indeed (219.6) gives the partial-transpose spectrum

$$
\left\{\frac{x(1-3\lambda)}4,\frac{x(1+\lambda)}4,
\frac{x(1+\lambda)}4,1-x+\frac{x(1+\lambda)}4\right\}.
$$

Only the first eigenvalue can be negative, and $(3\lambda-1)_+/4=A_t(p)$, proving the stated negativity; it is not an affine-negativity
claim for arbitrary separable padding. At $R=P_a$, one has
$\alpha=1,\gamma=0,x=1$; at $R=P_{\mathrm{full}}$, one has
$\alpha=\gamma=1,x=w$. Both equalities are included in the same finite
instrument.

**Definition 242.4 (complete unconditional law).** At the same maximizing
source and with the same preparation and instrument, the five disjoint
unconditional events are

| Event | Probability |
| --- | ---: |
| Original full filter rejected; no prepared output | $1-P_{\mathrm{full}}=1-E_t(p)/C$ |
| Prepared active sector; success | $\min\{R,P_a\}$ |
| Prepared active sector; failure | $(P_a-R)_+$ |
| Prepared spectator sector; success | $(R-P_a)_+$ |
| Prepared spectator sector; failure | $P_{\mathrm{sp}}-(R-P_a)_+$ |

The last entry is nonnegative because $R\le P_a+P_{\mathrm{sp}}$. These
five masses sum to one. Indeed $P_a\alpha+P_{\mathrm{sp}}\gamma=\min\{R,P_a\}+(R-P_a)_+=R$, and the three failure masses sum to

$$
(1-P_{\mathrm{full}})+(P_a-R)_+
  +P_{\mathrm{sp}}-(R-P_a)_+=1-R.
$$

Each spectator-reset success pair
$(i,j)$ has unconditional probability $(R-P_a)_+/4$ and the identical
product output $|01\rangle\langle01|$. Thus preparation rejection remains
part of the law, while all fine records are erased on the common success
output. At the selected $p_*$ when $L>E_t(1/2)$, one has $E_t(p_*)=L$, so $P_{\mathrm{full}}=R$, $s=1$ and $\alpha=\gamma=1$. Every postfilter event then succeeds, and failure is exactly the original filter rejection $1-R$. The five-event law also applies to every other maximizing source when $G=0$, using that source's own preparation probabilities.

The fixed-source upper bound in (242.3) applies to every allowed instrument at each feasible actual source, while Proposition 242.3 realizes its value at that same source. Together with the scalar proof, this establishes the simultaneous optimum, state and full law asserted by Theorem 242.2. In particular, the conditional success parameter is $s=L/E_t(p)$ and varies with the source: the fixed-$s$ source optimization of VII §§231–233 cannot simply be used with $s$ held constant for this question.

The additional source-choice argument is (242.10)–(242.19). The quantum upper bound and the attaining maps are reused at their existing assumptions from VII §§214–220; VII §224 records their literature correspondence. In particular, G. Vidal and R. F. Werner, *A computable measure of entanglement*, Phys. Rev. A 65, 032314, [quant-ph/0102117](https://arxiv.org/abs/quant-ph/0102117), supplies the ordinary-negativity convention and average LOCC monotonicity; average monotonicity alone is not the conditional ceiling. The filtering and one-pair bounds used in VII §§217–218 are those of F. Verstraete, J. Dehaene and B. De Moor, *Local filtering operations on two qubits*, Phys. Rev. A 64, 010101(R), [quant-ph/0011111](https://arxiv.org/abs/quant-ph/0011111), and N. Linden, S. Massar and S. Popescu, *Purifying noisy entanglement requires collective measurements*, Phys. Rev. Lett. 81, 3279, [quant-ph/9805001](https://arxiv.org/abs/quant-ph/9805001), with the parameter conventions and singular-leaf treatment specified there. N. Schuch, F. Verstraete and J. I. Cirac, *Quantum entanglement theory in the presence of superselection rules*, Phys. Rev. A 70, 042310, [quant-ph/0404079](https://arxiv.org/abs/quant-ph/0404079), supplies the local-number and two-preparation projection context, with the actual full-Gibbs and spectator accounting fixed by VII §215.

The result is conditional on this ideal known-source preparation and operation contract. It permits no extra copies, entangled ancilla, external phase reference, cut postrotation or unknown-source decoder, and gives no optimization over the original unfiltered $64$-dimensional resource. It neither establishes physical availability or cost of the stipulated controls and memories nor makes a quantum-advantage or literature-priority claim. Empty feasible sets, open endpoints and the zero-negativity regime retain the distinct meanings stated above.

## 追加锚（本行以下为增补区）
