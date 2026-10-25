# Native central-noise Green stability: coupling onset and the negative spectral ladder

## 1. The fixed source and the form correspondence

**Definition 1.1 (source, measure, clock and absorbing domain).** Let C denote
[Native central-noise full Green propagation and attractive stability](FIB_NATIVE_CENTRAL_NOISE_GREEN_STABILITY.md)
and A denote
[Native attractive boundary response](FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md),
both at repository revision
`e0086a9b94dd0c152d16222363adf13d7d9d6c2d`.
Use C, Definitions 1.1–1.2 and 15.1, without changing the source.
Thus $0<Z<1$, $r=1-Z$, $H=r/2$, $0<l<k_o<u<H$,
the mode probabilities in order $(0,1,2,3,13)$ are
$(k,H-k,Z,H-k,k)$, and the signed amplitudes have convention
$\psi_s=\sqrt{p_s}e^{-i\theta_s}$ with arbitrary fixed preparation phases.
The actual phase circles each have period $2\pi$ and

$$
\begin{aligned}
\Omega&=(l,u)\times\mathbb T^2,&
o&=(k_o,\alpha_o,\beta_o),&d\mu&=dk\,d\alpha\,d\beta,\\
P&=\partial_k,&
Q&=\tfrac12\partial_\alpha+c(k)\partial_\beta,&
c(k)&=\tfrac12-k/r,&Z_c&=-r^{-1}\partial_\beta.
\end{aligned}
\tag{1.1}
$$

The measure is raw, not probability normalized. For $\epsilon=|\nu|>0$,
the free form is $T_\epsilon=\|P\cdot\|_2^2+\|Q\cdot\|_2^2+
\epsilon^2\|Z_c\cdot\|_2^2$ on the closure $\mathcal F_\epsilon$ of
smooth periodic functions compactly supported in height. Both traces at
$k=l,u$ vanish. Its operator is $L_\epsilon$, with original semigroup
$e^{-tL_\epsilon}$. The field and attractive form are exactly

$$
\Gamma_{\epsilon,o}(q)=\int_0^\infty
 p^\Omega_\epsilon(t,o,q)\,dt,\qquad
q_{\epsilon,g}[f]=T_\epsilon[f]
 -g\int_\Omega\Gamma_{\epsilon,o}|f|^2\,d\mu.
\tag{1.2}
$$

In particular this retains the full unit source, all time scales and both
absorbing walls. The process supplied by C, (1.2), uses independent
covariance-$2$ Brownian motions $W^1,W^2,C$, zero area drift,
$J_t=\int_0^tW^1_s\,dW^2_s+\nu C_t$, and first exit of
$k_o+W^1_t$ from $(l,u)$. No time rescaling or new primitive central
control is included in these definitions.

In an injective source chart, write

$$
\begin{aligned}
x&=k-k_o,&y&=2(\alpha-\alpha_o),\\
z&=-r\{\beta-\beta_o-c(k_o)y\}-xy/2,&\xi&=(x,y,z),\\
U&=\partial_x-\tfrac y2\partial_z,&
V&=\partial_y+\tfrac x2\partial_z,&Z_H&=\partial_z,\\
d\mu&=m_0\,d\xi,&m_0&=(2r)^{-1},&
\delta_s\xi&=(sx,sy,s^2z).
\end{aligned}
\tag{1.3}
$$

These are exact identities: $(P,Q,Z_c)=(U,V,Z_H)$ and
$\det D\delta_s=s^4$. Let $\Phi_o$ be the inverse chart. The whole-group
Lebesgue Green field is $\mathcal G_\epsilon$, with

$$
\mathcal G_\epsilon(\delta_s\xi)=s^{-2}\mathcal G_{\epsilon/s}(\xi),
\quad
R(\xi)=\bigl((x^2+y^2)^2+16z^2\bigr)^{1/4},
\quad \mathcal G_0=(2\pi)^{-1}R^{-2}.
\tag{1.4}
$$

For $W=\mathcal G_1$, set

$$
\begin{aligned}
\mathcal T[v]&=\|Uv\|_2^2+\|Vv\|_2^2+\|Z_Hv\|_2^2,\\
\mathcal H_1&=\overline{C_c^\infty(\mathbb R^3;\mathbb C)}
 ^{(\|\cdot\|_2^2+\mathcal T)^{1/2}},&
\mathcal L_1&=-(U^2+V^2+Z_H^2),\\
\mathcal V[v]&=\int W|v|^2\,d\xi,&
\mathcal Q_\gamma[v]&=\mathcal T[v]-\gamma\mathcal V[v],\\
A_\gamma&=\text{the self-adjoint operator of }\mathcal Q_\gamma,&
e(\gamma)&=\inf_{\|v\|_2=1}\mathcal Q_\gamma[v].
\end{aligned}
\tag{1.5}
$$

Whole-group integrals and inner products use $d\xi$, with the inner
product conjugate linear in its first slot. The native correspondence is
$\gamma=g/m_0$, not $\gamma=g$. The norm meant by the free form norm is
$\|v\|_{\mathcal H_1}^2=\|v\|_2^2+\mathcal T[v]$; no global
Euclidean $H^1$ identification is imposed.

**Definition 1.2 (precise supplied analytic inputs).** The following are
inputs from C and A, with their original hypotheses.
C, Proposition 15.2 and (15.8), gives, for every $a>0$, a finite $b_a$
such that

$$
\mathcal V[v]\le a\mathcal T[v]+b_a\|v\|_2^2,
\qquad v\in\mathcal H_1.
\tag{1.6}
$$

C, Theorem 18.2, supplies compactness of
$J:v\mapsto W^{1/2}v$ from $\mathcal H_1$ to $L^2$, local Rellich
compactness, and the weak-derivative characterization of this same free
domain. In particular bounded smooth multiplication with bounded frame
derivatives preserves it. That theorem also supplies the unique normalized
strictly positive ground state $h_\gamma$, its complex simplicity and
isolation, and free-norm subsequential compactness of normalized minimizing
sequences whenever $e(\gamma)<0$.

Write $\lambda_0$ for C, Definition 16.2's full-angular horizontal constant
with natural, non-Dirichlet angular endpoints. A, Theorem 9.3 and
Corollary 11.2, supply the sharp threshold and strict remainder

$$
\begin{aligned}
\gamma_c&=2\pi\lambda_0,&g_c&=m_0\gamma_c,\\
e(\gamma)&=0\quad(0<\gamma\le\gamma_c),&
e(\gamma)&<0\quad(\gamma>\gamma_c),\\
\mathcal Q_{\gamma_c}[v]&\ge\|Z_Hv\|_2^2>0
                    \quad(0\ne v\in\mathcal H_1).
\end{aligned}
\tag{1.7}
$$

The value zero at critical coupling is not attained. C, (18.4) and
(16.14), also give $W>0$ almost everywhere, $W\to0$ uniformly at
infinity, and $W(\xi)\le C R(\xi)^{-2}$ for $R\ge1$.
C, (16.15)–(16.17), supplies compact smooth annular witnesses approaching
the horizontal quotient $\gamma_c$, without restriction to radial tests.
C, (2.5), supplies uniform convergence
$\mathcal G_\kappa\to\mathcal G_0$ on each fixed compact annulus as
$\kappa\downarrow0$.

The native inputs are C, Theorem 4.1's compact resolvent for each positive
$\epsilon$, C, (3.2)'s bounded chart remainder, and C, (15.4)'s uniform
bound off every fixed source neighborhood. Thus, for a fixed sufficiently
small chart $U_o$ and fixed $\epsilon_0$, constants $B,C_N$ satisfy

$$
\left|\Gamma_{\epsilon,o}(\Phi_o(\xi))
       -m_0^{-1}\mathcal G_\epsilon(\xi)\right|\le B,
\qquad
\sup_{\Omega\setminus N}\Gamma_{\epsilon,o}\le C_N,
\quad 0<\epsilon\le\epsilon_0.
\tag{1.8}
$$

These bounds include the actual phase deck images, full killed-time tail
and both wall collars. They are not Green fields for a changed boundary
problem. The ground-state native $O_g(1)$ estimate in C, Theorem 19.1, is
an existing result; the several-eigenfunction estimates below use additional
tail and matrix arguments.

**Definition 1.3 (localization and spectral conventions).** Fix real
nonnegative smooth native cutoffs $\chi,\psi$ with
$\chi^2+\psi^2=1$, $\chi=1$ near $o$,
$\operatorname{supp}\chi\Subset U_o$, and $\psi=0$ near $o$.
Use C, (16.5)–(16.7), the localization identity on the actual vector fields:

$$
\begin{aligned}
q_{\epsilon,g}[f]
 &=q_{\epsilon,g}[\chi f]+q_{\epsilon,g}[\psi f]
                 -\int B_\epsilon|f|^2\,d\mu,\\
B_\epsilon
 &=\sum_{D=P,Q}(|D\chi|^2+|D\psi|^2)
       +\epsilon^2(|Z_c\chi|^2+|Z_c\psi|^2),\qquad
0\le B_\epsilon\le C_{\rm IMS}.
\end{aligned}
\tag{1.9}
$$

The bound is uniform for $0<\epsilon\le\epsilon_0$ on the full native
form domain. Its supplier is the displayed product-rule proof in C,
(16.5), followed by form-core closure. Teschl's Euclidean IMS formula,
[*Mathematical Methods in Quantum Mechanics*, online edition, GSM 99,
Lemma 11.3, (11.12)–(11.13)](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf),
is classical background, not a substitution of Euclidean derivatives into
this model. In each frame direction the identities
$\chi D\chi+\psi D\psi=0$ and the product rule give exactly (1.9).

Define the zero-extended pullback

$$
(\mathcal B_\epsilon f)(\xi)
 =m_0^{1/2}\epsilon^2(\chi f)(\Phi_o(\delta_\epsilon\xi)).
\tag{1.10}
$$

It belongs to $\mathcal H_1$, has norm $\|\chi f\|_2$, and satisfies

$$
\begin{aligned}
\mathcal T[\mathcal B_\epsilon f]&=\epsilon^2T_\epsilon[\chi f],\\
\left|\mathcal Q_\gamma[\mathcal B_\epsilon f]
                 -\epsilon^2q_{\epsilon,g}[\chi f]\right|
 &\le gB\epsilon^2\|\chi f\|_2^2,\qquad \gamma=g/m_0.
\end{aligned}
\tag{1.11}
$$

These are C, (19.3)'s exact domain and Jacobian correspondences. The same
identities hold for direct pullback of any native form function compactly
supported in the chart, without an extra multiplication by $\chi$.

All eigenvalue lists below count complex multiplicity. The classical
spectral tools used are Teschl, §4.3, Theorem 4.10 and its explicit
form-domain version, Corollary 4.11 and Theorem 4.12(i): for a semibounded
self-adjoint operator, an $n$-dimensional form subspace whose Rayleigh
quotients are strictly below $b$ forces at least $n$ spectral dimensions
in $(-\infty,b)$. In particular the equivalent ascending variational levels
are

$$
\mu_n(q)=\inf_{\substack{S\subset D(q)\\\dim S=n}}
                  \sup_{0\ne v\in S}\frac{q[v]}{\|v\|_2^2}.
\tag{1.12}
$$

For a level below essential spectrum this is the corresponding eigenvalue
with multiplicity. The subspace formula also follows directly by
intersecting an arbitrary $n$-space with the orthogonal complement of the
first $n-1$ eigenvectors, and by using their first $n$ eigenvectors for the
reverse bound. Teschl, §6.5, Theorem 6.24, is used only under its exact KLMN
hypotheses: a closed semibounded Hermitian free form and a Hermitian
perturbation of relative form bound less than one. Here (1.6), with
$\gamma a<1$, checks those hypotheses on precisely $\mathcal H_1$.
These external tools supply no native chart, measure, clock or field
comparison. The source-specific deductions below are repo-derived
applications of the stated inputs, with no historical-priority assertion.

## 2. The positive branch and its critical escape

**Theorem 2.1 (continuous free-form branch, strict curvature and flat
critical onset).** For $\gamma>\gamma_c$, choose the unique normalized
positive ground state $h_\gamma$ of (1.5). Then
$\gamma\mapsto h_\gamma$ is continuous into $\mathcal H_1$, and

$$
e\in C^1((\gamma_c,\infty)),\qquad
e'(\gamma)=-\mathcal V[h_\gamma]<0.
\tag{2.1}
$$

The function $e$ is strictly concave on this interval. As
$\gamma\downarrow\gamma_c$,

$$
\begin{aligned}
h_\gamma&\rightharpoonup0&&\text{in }\mathcal H_1,\\
\int_K h_\gamma^2\,d\xi&\longrightarrow0
           &&\text{for every fixed compact }K\subset\mathbb R^3,\\
\mathcal T[h_\gamma]&\longrightarrow0,&
\mathcal V[h_\gamma]&\longrightarrow0,\\
e(\gamma)&=o(\gamma-\gamma_c),&
e'(\gamma)&\longrightarrow0,\\
\|Z_Hh_\gamma\|_2^2&=o(\gamma-\gamma_c).
\end{aligned}
\tag{2.2}
$$

Consequently $e$ joined to its zero branch on $0<\gamma\le\gamma_c$ is
$C^1$ at $\gamma_c$. The normalized states do not converge strongly to zero
in the free norm, since their $L^2$ norms remain one.

Proof. Fix a finite upper coupling bound $M>\gamma_c$. Choose $a$ in
(1.6) with $Ma\le1/2$. For $\gamma_c<\gamma\le M$,

$$
0>e(\gamma)=\mathcal Q_\gamma[h_\gamma]
 \ge\tfrac12\mathcal T[h_\gamma]-M b_a.
\tag{2.3}
$$

Thus these normalized states have a common free-norm bound, and their
potential integrals have a common bound $K_M$ by (1.6). Cross-substitution
of the minimizers at $\gamma_1<\gamma_2$ gives

$$
-\mathcal V[h_{\gamma_2}]
 \le\frac{e(\gamma_2)-e(\gamma_1)}{\gamma_2-\gamma_1}
 \le-\mathcal V[h_{\gamma_1}].
\tag{2.4}
$$

In particular $e$ is locally Lipschitz on the supercritical interval.
If $\gamma_j\to\gamma_*>\gamma_c$, (2.3) and (2.4) imply

$$
\mathcal Q_{\gamma_*}[h_{\gamma_j}]
 =e(\gamma_j)+(\gamma_j-\gamma_*)\mathcal V[h_{\gamma_j}]
 \longrightarrow e(\gamma_*).
\tag{2.5}
$$

This is a normalized minimizing sequence at the single fixed parameter
$\gamma_*$. The supplied free-norm compactness gives a strongly convergent
subsequence whose limit is a ground state there. Strong $L^2$ convergence
of nonnegative functions keeps that limit nonnegative; its unit norm and
the supplied uniqueness identify it with $h_{\gamma_*}$, without a phase
ambiguity. Applying the same argument to every subsequence proves full
$\mathcal H_1$ convergence. Continuity of the bounded map
$J:\mathcal H_1\to L^2$ makes $\mathcal V[h_\gamma]$ continuous.
Letting the endpoints of (2.4) coalesce proves (2.1) and $C^1$ regularity.
Strict negativity follows from $W>0$ and $\|h_\gamma\|_2=1$.

As the infimum of affine functions of $\gamma$, $e$ is concave.
To prove strictness, suppose equality in its concavity inequality holds
between two distinct supercritical parameters $\gamma_a,\gamma_b$ at an
interior convex combination. The normalized minimizer $h$ at that
combination has endpoint energies at least $e(\gamma_a)$ and
$e(\gamma_b)$. Linearity of its form in $\gamma$ and the equality assumed
force equality at both endpoints. It is therefore a ground eigenfunction
for both forms. Subtracting the two weak eigenvalue equations gives

$$
\int W\overline v h\,d\xi
 =-\frac{e(\gamma_b)-e(\gamma_a)}{\gamma_b-\gamma_a}
                     \langle v,h\rangle,
\qquad v\in\mathcal H_1.
\tag{2.6}
$$

The product $Wh$ is locally integrable: weighted Cauchy–Schwarz uses
$\mathcal V[h]<\infty$ and local integrability of $W$, supplied by its
local Coulomb bound in C, (18.4). Compact smooth tests thus imply that
$W$ equals the constant in (2.6) almost everywhere on $\{h>0\}$.
That set has full measure by positivity. A positive function tending
uniformly to zero at infinity cannot be an almost-everywhere constant.
This contradiction proves strict concavity.

For the critical limit write $\delta=\gamma-\gamma_c>0$. By (1.7),

$$
0>e(\gamma)
 =\mathcal Q_{\gamma_c}[h_\gamma]-\delta\mathcal V[h_\gamma]
 \ge-\delta K_M.
\tag{2.7}
$$

Hence $e(\gamma)\to0$ and
$0\le\mathcal Q_{\gamma_c}[h_\gamma]\le\delta K_M\to0$.
For any sequence of parameters tending down to criticality, the common
free bound permits extraction of a weak $\mathcal H_1$ limit $h$.
Compactness of $J$ gives $Jh_\gamma\to Jh$ strongly along that
subsequence. Lower semicontinuity of $\mathcal T$ yields

$$
0\le\mathcal Q_{\gamma_c}[h]
 \le\liminf\mathcal Q_{\gamma_c}[h_\gamma]=0.
\tag{2.8}
$$

The strict remainder (1.7) forces $h=0$. Every weakly convergent
subsequence has this limit, so $h_\gamma\rightharpoonup0$ in the free
space. Compactness of $J$ now gives $\mathcal V[h_\gamma]\to0$ for the
entire family. On each relatively compact open neighborhood of a given
compact $K$, the supplied local Rellich embedding takes the same bounded
weakly zero family to a strongly zero $L^2$ family. Thus the asserted
compact-set mass tends to zero.

The energy identity gives
$\mathcal T[h_\gamma]=e(\gamma)+\gamma\mathcal V[h_\gamma]\to0$.
More precisely (2.7), with the actual potential integral in place of its
bound, gives

$$
-\mathcal V[h_\gamma]
 \le\frac{e(\gamma)}\delta\le0,
\qquad
0\le\|Z_Hh_\gamma\|_2^2
 \le\mathcal Q_{\gamma_c}[h_\gamma]
 =e(\gamma)+\delta\mathcal V[h_\gamma]
 \le\delta\mathcal V[h_\gamma].
\tag{2.9}
$$

These prove both little-oh statements. Formula (2.1) gives the derivative
limit. Since the left branch is identically zero and the right difference
quotient and derivative both tend to zero, the joined energy is $C^1$ at
criticality. None of these arguments supplies a critical exponent or a
new rescaling of the escaping normalized states. $\square$

## 3. The infinite discrete negative spectrum and the collapsing gap

**Theorem 3.1 (negative spectral ladder and logarithmic count).** For every
fixed $\gamma>\gamma_c$, $A_\gamma$ has an infinite sequence of negative
eigenvalues, with complex multiplicities,

$$
\lambda_1(\gamma)=e(\gamma)<\lambda_2(\gamma)
 \le\lambda_3(\gamma)\le\cdots<0,
\qquad \lambda_n(\gamma)\uparrow0.
\tag{3.1}
$$

Every negative eigenvalue is isolated with finite multiplicity, and for
every $t>0$,

$$
N_\gamma(t)=\operatorname{rank}\mathbf1_{(-\infty,-t)}(A_\gamma)
 <\infty,\qquad
N_\gamma(t)\ge c_\gamma\log(1/t)-C_\gamma
\tag{3.2}
$$

for some $c_\gamma>0$ and finite $C_\gamma$. The lower bound can be taken
for all $t>0$ by increasing $C_\gamma$.

Proof. The KLMN hypotheses are checked in Definition 1.3. In particular
there is $C$ with

$$
\mathcal Q_\gamma[v]\ge\tfrac12\mathcal T[v]-C\|v\|_2^2.
\tag{3.3}
$$

Suppose the spectral subspace below $-t$ were infinite dimensional, and
take an orthonormal sequence $v_j$ in it. Semiboundedness and the upper
spectral bound $-t$ imply that these vectors belong to the form domain and
$\mathcal Q_\gamma[v_j]\le-t$. Equation (3.3) bounds their free norms.
Orthonormality implies weak $L^2$ convergence to zero. Every free-weak
subsequence therefore has limit zero, and compactness of $J$ gives
$\mathcal V[v_j]\to0$. But
$\mathcal Q_\gamma[v_j]\ge-\gamma\mathcal V[v_j]\to0$, contradicting
the bound $-t$. This proves finiteness of every strictly negative spectral
projection. Any negative spectral point lies in such a finite-dimensional
projection for some $t>0$ smaller than its absolute value. The spectral
theorem on that finite-dimensional space makes it an isolated finite
multiplicity eigenvalue. Negative spectrum can accumulate only at zero,
since the operator is bounded below.

For the number of negative directions use the supplied sharp annular
witnesses, not an assumed radial Hardy optimizer. Since
$\gamma>\gamma_c$, C, (16.16), permits one fixed nonzero compact smooth
annular $u$, normalized in $L^2$, such that

$$
\mathcal E_H[u]-\gamma\int\mathcal G_0|u|^2\,d\xi=-2b<0,
\qquad \operatorname{supp}u\subset\{a\le R\le b_1\},
\quad 0<a<b_1<\infty.
\tag{3.4}
$$

Here $\mathcal E_H=\|U\cdot\|_2^2+\|V\cdot\|_2^2$ and $b>0$.
For $D_su=s^{-2}u\circ\delta_{1/s}$, the exact field and Green scalings
in (1.3)–(1.4) give

$$
\begin{aligned}
\|D_su\|_2&=1,\\
\mathcal Q_\gamma[D_su]
 &=s^{-2}\left(\mathcal E_H[u]
       +s^{-2}\|Z_Hu\|_2^2
       -\gamma\int\mathcal G_{1/s}|u|^2\,d\xi\right).
\end{aligned}
\tag{3.5}
$$

Uniform annular convergence of $\mathcal G_{1/s}$ makes the bracket at
most $-b$ for all $s\ge s_0$, after increasing $s_0\ge1$.
Choose $L>b_1/a$ and set $s_j=s_0L^j$, $j=0,1,\ldots$.
Their supports lie in pairwise separated annuli
$[as_j,b_1s_j]$. Thus the vectors $D_{s_j}u$ are orthonormal, and
all off-diagonal form entries vanish: the form is local and their compact
supports are separated. For a finite linear combination,

$$
\mathcal Q_\gamma\left[\sum_jd_jD_{s_j}u\right]
 =\sum_j|d_j|^2\mathcal Q_\gamma[D_{s_j}u]
 \le-\sum_j b s_j^{-2}|d_j|^2.
\tag{3.6}
$$

There are arbitrarily many negative directions. Theorem 4.12(i) of
Teschl, in its form-domain scope, and the finite projections already
proved give infinitely many negative discrete eigenvalues. The bottom is
the supplied simple ground state, hence the strict first inequality in
(3.1). Their only possible accumulation point is zero, which proves the
last assertion in (3.1), including $0\in\sigma(A_\gamma)$.

For the strict threshold $-t$, retain exactly those $j\ge0$ with
$b s_0^{-2}L^{-2j}>t$. On their span every nonzero Rayleigh quotient is
strictly below $-t$, so

$$
N_\gamma(t)\ge
 \#\left\{j\ge0:j<
        \frac{\log(b/s_0^2t)}{2\log L}\right\}.
\tag{3.7}
$$

The right side is at least
$\max\{0,(2\log L)^{-1}\log(b/s_0^2t)-1\}$.
This proves (3.2) with, for example,
$c_\gamma=(2\log L)^{-1}$ and a sufficiently large nonnegative
$C_\gamma$. Strict versus non-strict spectral cutoff can change the
integer count by an endpoint but not this bound. No upper logarithmic
asymptotic, sharp coefficient or uniformity in $\gamma$ is asserted.
$\square$

**Corollary 3.2 (gap collapse and fixed excited levels at onset).** Let
$h_\gamma$ be as in Theorem 2.1 and define

$$
\Delta_\gamma
 =\inf_{\substack{v\in\mathcal H_1,\ \|v\|_2=1\\
                         \langle h_\gamma,v\rangle=0}}
             \mathcal Q_\gamma[v]-e(\gamma).
\tag{3.8}
$$

Then

$$
\Delta_\gamma=\lambda_2(\gamma)-e(\gamma),\qquad
0<\Delta_\gamma<|e(\gamma)|,
\qquad
\Delta_\gamma\longrightarrow0
          \quad(\gamma\downarrow\gamma_c).
\tag{3.9}
$$

For every fixed $n$, $\lambda_n(\gamma)\to0$ as
$\gamma\downarrow\gamma_c$.

Proof. Form-domain min–max on the ground state's orthogonal complement
identifies its bottom with $\lambda_2$. The first eigenvalue is simple and
isolated, while $\lambda_2<0$ by Theorem 3.1. This gives both strict
inequalities. Theorem 2.1 gives $e(\gamma)\to0$, so (3.9) follows by
squeezing. For each $n$, $e(\gamma)\le\lambda_n(\gamma)<0$ proves the
last assertion by the same argument. Thus an infinite negative ladder at
each supercritical parameter is compatible with no negative level and no
zero eigenfunction at criticality. In particular a uniform positive lower
bound for the ground-state gap on couplings approaching criticality is
impossible. $\square$

## 4. Negative eigenfunction tails and finite-dimensional cutoff errors

**Lemma 4.1 (a quantitative tail on the actual free domain).** Fix
$\gamma>\gamma_c$. If $h\in\mathcal H_1$ is an $L^2$-normalized weak
eigenfunction of $A_\gamma$ with eigenvalue $\lambda<0$, there are finite
$C_{\gamma,\lambda}$ and $R_{\gamma,\lambda}$ such that

$$
\int_{R(\xi)>r_0}|h|^2\,d\xi
 \le C_{\gamma,\lambda}r_0^{-2},
\qquad r_0\ge R_{\gamma,\lambda}.
\tag{4.1}
$$

No symmetry or ground-state positivity is required.

Proof. Choose a real smooth $\eta\in[0,1]$, zero for $R\le1$ and
one for $R\ge2$, and put $\eta_s=\eta\circ\delta_{1/s}$ for $s\ge1$.
It is smooth also at zero because it is constant there. Frame
homogeneity and the compact transition annulus give

$$
|U\eta_s|+|V\eta_s|\le C/s,\qquad
|Z_H\eta_s|\le C/s^2.
\tag{4.2}
$$

Although $\eta_s$ is not compactly supported, it and $\eta_s^2$ are
bounded with bounded frame derivatives, so their products with $h$ are
in $\mathcal H_1$. This follows from the weak-derivative characterization
and cutoff approximation supplied in C, Theorem 18.2. Test the weak
eigenvalue equation against $\eta_s^2h$. The product rule in each of
$U,V,Z_H$, followed by its real part, gives exactly

$$
\mathcal Q_\gamma[\eta_sh]
 -\lambda\|\eta_sh\|_2^2
 =\int\bigl(|U\eta_s|^2+|V\eta_s|^2+|Z_H\eta_s|^2\bigr)|h|^2\,d\xi
 \le C s^{-2}.
\tag{4.3}
$$

The potential integral is finite by (1.6); no operator-domain product is
being assumed. On $\operatorname{supp}\eta_s\subset\{R\ge s\}$,
$W\le C_Ws^{-2}$ by Definition 1.2. Dropping the nonnegative kinetic
term in (4.3) therefore gives

$$
(|\lambda|-\gamma C_Ws^{-2})\|\eta_sh\|_2^2\le Cs^{-2}.
\tag{4.4}
$$

Take $s$ large enough that $\gamma C_Ws^{-2}\le|\lambda|/2$.
Since $\eta_s=1$ for $R\ge2s$, (4.4), with $r_0=2s$, proves (4.1).
The constants can be taken common for finitely many normalized
eigenfunctions whose negative eigenvalues are fixed and bounded away from
zero. This argument is a vector-field form computation; it does not import
a Euclidean radial eigenfunction equation. $\square$

**Lemma 4.2 (all Gram and form entries on a fixed negative spectral
subspace).** Fix $\gamma>\gamma_c$ and $n\ge1$. Choose an orthonormal
list $h_1,\ldots,h_n$ of eigenfunctions for the first $n$ eigenvalues
$\lambda_1,\ldots,\lambda_n$, including repeated eigenvalues according
to multiplicity. Let $\widehat\chi=\chi\circ\Phi_o$ extended smoothly
by zero to the group and $\varphi_\epsilon=\widehat\chi\circ\delta_\epsilon$.
Define

$$
G^\epsilon_{ij}=\langle\varphi_\epsilon h_i,
                                  \varphi_\epsilon h_j\rangle,
\qquad
F^\epsilon_{ij}=\mathcal Q_\gamma(
                         \varphi_\epsilon h_i,\varphi_\epsilon h_j).
\tag{4.5}
$$

There are finite constants depending on $\gamma,n$, the fixed source and
the cutoff such that, as $\epsilon\downarrow0$,

$$
\|G^\epsilon-I_n\|_{\rm op}\le C_{\gamma,n}\epsilon^2,
\qquad
\|F^\epsilon-\operatorname{diag}(\lambda_1,\ldots,\lambda_n)\|_{\rm op}
                       \le C_{\gamma,n}\epsilon^2.
\tag{4.6}
$$

In particular the cutoff span has dimension $n$, and every nonzero
$v\in\operatorname{span}\{h_1,\ldots,h_n\}$ satisfies

$$
\frac{\mathcal Q_\gamma[\varphi_\epsilon v]}
     {\|\varphi_\epsilon v\|_2^2}
 \le\lambda_n+C_{\gamma,n}\epsilon^2
\tag{4.7}
$$

for sufficiently small $\epsilon$.

Proof. For some fixed $a_0>0$, $\widehat\chi=1$ when $R\le a_0$.
Thus $1-\varphi_\epsilon^2$ is supported where $R\ge a_0/\epsilon$.
By Lemma 4.1,

$$
\left|G^\epsilon_{ij}-\delta_{ij}\right|
 \le\left(\int_{R\ge a_0/\epsilon}|h_i|^2\right)^{1/2}
      \left(\int_{R\ge a_0/\epsilon}|h_j|^2\right)^{1/2}
 \le C_{\gamma,n}\epsilon^2.
\tag{4.8}
$$

There are only $n^2$ entries, so this also bounds the matrix operator
norm, after changing the constant. Exact field homogeneity gives

$$
|U\varphi_\epsilon|+|V\varphi_\epsilon|\le C\epsilon,
\qquad |Z_H\varphi_\epsilon|\le C\epsilon^2.
\tag{4.9}
$$

The compact support of $\widehat\chi$ and its smooth extension justify
these global derivative bounds. All products in the next identity belong
to the free domain. For any real cutoff $\varphi$ of this kind, expansion
of the sesquilinear form gives

$$
\begin{aligned}
\mathcal Q_\gamma(\varphi h_i,\varphi h_j)
={}&\tfrac12\{\mathcal Q_\gamma(h_i,\varphi^2h_j)
                  +\mathcal Q_\gamma(\varphi^2h_i,h_j)\}\\
 &+\int\bigl(|U\varphi|^2+|V\varphi|^2+|Z_H\varphi|^2\bigr)
                                  \overline{h_i}h_j\,d\xi\\
={}&\tfrac{\lambda_i+\lambda_j}{2}
                            \langle h_i,\varphi^2h_j\rangle
     +\int\bigl(|U\varphi|^2+|V\varphi|^2+|Z_H\varphi|^2\bigr)
                                  \overline{h_i}h_j\,d\xi.
\end{aligned}
\tag{4.10}
$$

The first equality is the product rule, with the potential term unchanged;
the second uses both weak eigenvalue equations. Cauchy–Schwarz and (4.9)
bound the last integral by $C\epsilon^2$. Together with (4.8), this
proves the second matrix estimate in (4.6), also for distinct eigenvalues
and complex eigenfunctions.

For a coefficient vector $d\in\mathbb C^n$ and
$v=\sum d_jh_j$, (4.6) gives

$$
\begin{aligned}
\big|\|\varphi_\epsilon v\|_2^2-\|d\|^2\big|
 &\le C\epsilon^2\|d\|^2,\\
\mathcal Q_\gamma[\varphi_\epsilon v]
 &\le\sum_j\lambda_j|d_j|^2+C\epsilon^2\|d\|^2
 \le\lambda_n\|d\|^2+C\epsilon^2\|d\|^2.
\end{aligned}
\tag{4.11}
$$

The Gram matrix is positive definite once $C\epsilon^2<1/2$.
To obtain (4.7) even though $\lambda_n<0$, subtract
$\lambda_n\|\varphi_\epsilon v\|_2^2$ in (4.11); the additional term
is bounded in absolute value by $|\lambda_n|C\epsilon^2\|d\|^2$.
Divide by $\|\varphi_\epsilon v\|_2^2\ge\|d\|^2/2$.
This proves the uniform quotient bound on the whole finite span, rather
than only on its individual basis vectors. $\square$

## 5. Both native min–max comparisons and the number of negative levels

**Theorem 5.1 (every fixed native negative level with a bounded
remainder).** Fix the native data of Definition 1.1, a coupling
$g>g_c$, and an integer $n\ge1$. Let $E_{\epsilon,n}(g)$ be the
$n$th eigenvalue of the self-adjoint native form $q_{\epsilon,g}$,
ordered with complex multiplicity, and put $\gamma=g/m_0$.
There are finite $C_{g,n}$ and $\epsilon_{g,n}>0$ such that

$$
\left|E_{\epsilon,n}(g)-\epsilon^{-2}\lambda_n(g/m_0)\right|
 \le C_{g,n},\qquad 0<\epsilon<\epsilon_{g,n}.
\tag{5.1}
$$

In particular these first $n$ levels are negative for sufficiently small
$\epsilon$. Their multiplicities are included in both comparisons; no
simplicity of an excited eigenvalue is assumed.

Proof. For each positive $\epsilon$, the native form is closed and
semibounded with compact resolvent by C, Theorem 4.1. Hence the indicated
eigenvalues and their finite-dimensional low spectral spaces exist.
First establish the upper comparison. Use Lemma 4.2's $n$-dimensional
cutoff cell space. For $v\in\operatorname{span}\{h_1,\ldots,h_n\}$ set

$$
(\mathcal I_\epsilon v)(\Phi_o(\delta_\epsilon\xi))
 =m_0^{-1/2}\epsilon^{-2}\varphi_\epsilon(\xi)v(\xi),
\tag{5.2}
$$

and extend by zero outside the chart. Its compact chart support is
strictly inside both height faces. Products have the weak derivatives
required for $\mathcal H_1$; local smooth approximation on their compact
support and inverse pullback put (5.2) in the whole native
$\mathcal F_\epsilon$, retaining the prescribed periodicity and both
zero wall traces. The exact raw Jacobian in (1.3) gives

$$
\|\mathcal I_\epsilon v\|_{L^2(\mu)}^2
                   =\|\varphi_\epsilon v\|_2^2.
\tag{5.3}
$$

The supported version of (1.11), which uses the full potential remainder
(1.8), gives

$$
\left|\epsilon^2q_{\epsilon,g}[\mathcal I_\epsilon v]
                  -\mathcal Q_\gamma[\varphi_\epsilon v]\right|
 \le gB\epsilon^2\|\varphi_\epsilon v\|_2^2.
\tag{5.4}
$$

For completeness, the potential scaling responsible for the coupling is
$m_0^{-1}\mathcal G_\epsilon(\delta_\epsilon\xi)
=m_0^{-1}\epsilon^{-2}W(\xi)$, while the norm density is
$m_0\epsilon^4$ and the squared amplitude is
$m_0^{-1}\epsilon^{-4}$. Thus multiplying the native form by
$\epsilon^2$ produces $\mathcal T- (g/m_0)\mathcal V$, exactly as
in (5.4). The remainder is bounded by the raw native squared norm.

The Gram estimate makes $\mathcal I_\epsilon$ injective on this span.
Equations (4.7), (5.3) and (5.4), applied to every vector of its
$n$-dimensional image, give by native min–max

$$
\mu_{\epsilon,n}:=\epsilon^2E_{\epsilon,n}(g)
       \le\lambda_n(\gamma)+C_{g,n}\epsilon^2.
\tag{5.5}
$$

This proves in particular a fixed strictly negative upper bound
$\mu_{\epsilon,n}\le-a_n$, with $a_n=|\lambda_n(\gamma)|/2>0$,
after decreasing $\epsilon_{g,n}$.

For the reverse comparison use the full native low space
$S_{\epsilon,n}$ spanned by any orthonormal first $n$ native
eigenfunctions. If the $n$th level is repeated, select any $n$-dimensional
subspace of the corresponding ordered eigenbasis. The spectral theorem
gives, for every $f\in S_{\epsilon,n}$,

$$
\epsilon^2q_{\epsilon,g}[f]
           \le\mu_{\epsilon,n}\|f\|_2^2\le-a_n\|f\|_2^2.
\tag{5.6}
$$

On the support of $\psi$, (1.8) gives
$q_{\epsilon,g}[\psi f]\ge T_\epsilon[\psi f]
-gC_{\rm out}\|\psi f\|_2^2$. Combine this with the actual native IMS
identity (1.9) and the two-sided chart comparison (1.11). There is a
constant $D_g$, independent of $\epsilon,f,n$, such that

$$
\epsilon^2q_{\epsilon,g}[f]
 \ge\mathcal Q_\gamma[w]+\epsilon^2T_\epsilon[\psi f]
                       -D_g\epsilon^2\|f\|_2^2,
\qquad w=\mathcal B_\epsilon f,
\quad \|w\|_2\le\|f\|_2.
\tag{5.7}
$$

For example $D_g=gB+gC_{\rm out}+C_{\rm IMS}$ suffices.
This inequality retains the exterior kinetic term and includes both
boundary collars through $C_{\rm out}$. Since
$\mathcal Q_\gamma[w]\ge e(\gamma)\|w\|_2^2$, (5.6)–(5.7) give

$$
|e(\gamma)|\,\|\mathcal B_\epsilon f\|_2^2
 \ge(a_n-D_g\epsilon^2)\|f\|_2^2
 \ge\tfrac12a_n\|f\|_2^2
\tag{5.8}
$$

for small $\epsilon$. Thus the cutoff-rescaling map has a uniform
positive norm lower bound on this entire low space, and its image
$W_{\epsilon,n}=\mathcal B_\epsilon S_{\epsilon,n}\subset\mathcal H_1$
has dimension exactly $n$. This proves the needed dimension statement
without presupposing localization of individual excited eigenfunctions.

Drop the nonnegative exterior kinetic term in (5.7). For nonzero
$f\in S_{\epsilon,n}$ it follows that

$$
\mathcal Q_\gamma[\mathcal B_\epsilon f]
 \le(\mu_{\epsilon,n}+D_g\epsilon^2)\|f\|_2^2
 \le(\mu_{\epsilon,n}+D_g\epsilon^2)
                                \|\mathcal B_\epsilon f\|_2^2.
\tag{5.9}
$$

The last inequality has the indicated direction because its coefficient
is negative and $\|\mathcal B_\epsilon f\|_2\le\|f\|_2$.
This sign is essential; no near-isometry of the native low space is
assumed. Whole-group min–max on the $n$-dimensional image now gives

$$
\lambda_n(\gamma)
 \le\sup_{0\ne w\in W_{\epsilon,n}}
                   \frac{\mathcal Q_\gamma[w]}{\|w\|_2^2}
 \le\mu_{\epsilon,n}+D_g\epsilon^2.
\tag{5.10}
$$

Combining (5.5) and (5.10), and dividing by $\epsilon^2$, proves (5.1).
Both applications of min–max use full subspaces and count multiplicity;
the first uses the quantitative tail and both cutoff matrices, and the
second the full native low spectral space, the actual vector-field IMS
identity and the negative-coefficient norm comparison. $\square$

**Theorem 5.2 (native logarithmic negative count).** For each fixed native
source and fixed $g>g_c$, there are $c_g>0$, finite $C_g$ and
$\epsilon_g>0$ such that the total native negative multiplicity satisfies

$$
N^-_\epsilon(g):=\operatorname{rank}
       \mathbf1_{(-\infty,0)}(q_{\epsilon,g})
 \ge c_g\log(1/\epsilon)-C_g,
\qquad 0<\epsilon<\epsilon_g.
\tag{5.11}
$$

Here the spectral projection is that of the associated native operator;
it has finite rank for each fixed positive noise.

Proof. Use the same fixed annular $u$, constants $b,s_0,L,a,b_1$ and
scales $s_j$ as in (3.4)–(3.6), for $\gamma=g/m_0$.
Choose $\rho_*>0$ so small that the closed gauge ball
$\{R\le b_1\rho_*\}$ is contained strictly inside the injective chart
and both native height walls. Decrease it further to have
$gB\rho_*^2<b/2$; when $B=0$ this condition needs no decrease.
For every index with $s_j\le\rho_*/\epsilon$, transfer $D_{s_j}u$
directly to the native chart by

$$
f_{\epsilon,j}(\Phi_o(\delta_\epsilon\xi))
      =m_0^{-1/2}\epsilon^{-2}D_{s_j}u(\xi),
\tag{5.12}
$$

with zero extension. These are smooth native form functions, orthonormal
by the exact Jacobian, and have pairwise separated compact supports.
Equations (3.5) and (1.8), or the supported version of (1.11), give

$$
q_{\epsilon,g}[f_{\epsilon,j}]
 \le-b\epsilon^{-2}s_j^{-2}+gB
 \le-\frac{b}{2\epsilon^2s_j^2}<0.
\tag{5.13}
$$

The last inequality uses $\epsilon^2s_j^2\le\rho_*^2$.
Off-diagonal norm and form terms vanish on these separated native
supports. Hence every nonzero vector of their span has negative form
value, and the negative spectral projection has rank at least

$$
\#\{j\ge0:s_0L^j\le\rho_*/\epsilon\}
 \ge\frac{\log(1/\epsilon)}{\log L}
                +\frac{\log(\rho_*/s_0)}{\log L}-1
\tag{5.14}
$$

when the scale interval is nonempty. This is (5.11), for example with
$c_g=1/\log L$ and a large enough $C_g$. Compact resolvent and
semiboundedness give finitely many negative native eigenvalues at each
fixed $\epsilon$. This simultaneous annular proof does not insert a
growing $n$ into the fixed-$n$ remainder (5.1). $\square$

**Corollary 5.3 (the native ground gap and the limits of the parameters).**
For each fixed $g>g_c$, the first native gap satisfies

$$
E_{\epsilon,2}(g)-E_{\epsilon,1}(g)
 =\epsilon^{-2}\Delta_{g/m_0}+O_g(1).
\tag{5.15}
$$

All constants and small-noise thresholds in (5.1) are for fixed $g,n$
and the fixed native source. The count constants in (5.11) are for fixed
$g$ and that source. None of these estimates supplies bounds uniform as
$n\to\infty$ or $g\downarrow g_c$.

Proof. Subtract (5.1) for $n=1,2$ and use (3.9).
The positive leading gap follows from the supplied simple cell bottom;
its coefficient tends to zero as $g\downarrow g_c$ by Theorem 2.1 and
Corollary 3.2. The explicit estimates show where parameter dependence
enters: (4.4) uses $|\lambda_n|^{-1}$, (4.6) a fixed finite matrix size,
(5.8) uses $a_n=|\lambda_n|/2$, and the annular witness and its initial
scale depend on the strict excess $\gamma-\gamma_c$. These quantities
are not bounded away from degeneration by the hypotheses of a joint
limit. Thus (5.15) is a fixed-coupling small-noise assertion, and does
not interchange the critical and native small-noise limits. $\square$

## 6. The retained analytic contract

**Definition 6.1 (scope of the spectral conclusions).** The branch,
escape and spectral statements concern the analytic forms (1.2) and
(1.5), on their stated complex closures. The supplied heat estimates,
Green scaling, full killed remainder, compact potential multiplier,
sharp threshold and simple ground state retain their attributions in C,
§§2–4 and 15–20, and A, §§9 and 11. Teschl, Theorems 4.10–4.12 and
6.24, supplies the stated general spectral and form tools; the actual
native localization supplier is C, (16.5)–(16.7) and (19.3), with the
fieldwise product identity (1.9). The new deductions here are the
parameter and critical conclusions of §2, the annular spectral and gap
consequences of §3, the tail and finite-span estimates of §4, and the
two-sided native spectral and counting comparisons of §5. They reuse
the threshold rather than asserting a new Hardy theorem.

This contract includes no critical exponent, uniform large-level or
critical-coupling asymptotic, exact logarithmic counting coefficient,
free native-control realization, or identification with a Hecke spectrum.
The independent central Brownian input and the two absorbing walls are
analytic premises of the original model. Any physical or acquisition
interpretation still requires its own same-source state, operator, field,
measure, boundary and clock correspondence and its original execution,
observation and resource permissions. Neither a variational eigenvalue nor
a cell rescaling supplies those permissions.

## 追加锚（本行以下为增补区）
