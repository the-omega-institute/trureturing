# FIB phase-parent spectrum and joint-occupation readout design

The legal Hilbert space, site quadrature controls and supplied same-phase reference are those of [Parent/Readout, Chapter 8][ParentReadout]. Its Chapters 9–10 concern fixed relation targets and selected conjugate families. This volume instead compares all real phase directions in the same recorded-site menu, then allows independent joint occupation. All probability laws are normalized; the coherent preparation and control menu are supplied assumptions.

## 1. Activity-matched phase information and the legal quantum parent

The fixed-target designs of Parent/Readout Chapter 9 and the following minimax designs use the same recorded-site experiment. A target may remain estimable when some phase directions are unobserved; the minimum Fisher/QFI ratio instead ranges over every nonconstant real phase direction. Thus zero-weight target optima do not contradict the positive weights required below.

### 1.1. A common law and a recorded site distribution

**Definition 1.1 (Activity law and normalized local terms).** Let $n\ge1$,
use the open-boundary legal words $B_n$ and Hilbert space $\mathcal K_n$
of Parent/Readout §8, and fix $a_i>0$. For the occupied set $I(u)=\{i:u_i=1\}$ put

$$
p_u=\mathcal Z^{-1}\prod_{i\in I(u)}a_i,\qquad
|\psi_+\rangle=\sum_{u\in B_n}\sqrt{p_u}|u\rangle,\qquad
D=\operatorname{diag}(\sqrt p).
\tag{1.1}
$$

Take the local parent of [Boundary Calculus, Definition 15.22][BC8]:

$$
\begin{aligned}
v_i&=\sqrt{a_i}|0\rangle_i-|1\rangle_i,\\
h_i&=P_{i-1}|v_i\rangle\langle v_i|P_{i+1},\\
K_i&=(1+a_i)^{-1}h_i,\qquad H_{\rm loc}=\sum_i h_i.
\end{aligned}
\tag{1.2}
$$

All operators in (1.2) are restricted to $\mathcal K_n$;
$P_0=P_{n+1}=I$. The other tensor factors carry the identity.
In particular $K_i^2=K_i$, whereas $h_i^2=(1+a_i)h_i$.
By Boundary Calculus, Proposition 15.23, their common zero space is
$\mathbb C\psi_+$.

**Definition 1.2 (Calibrated experiment with a recorded site).** Choose
$i$ independently of the signal with probability $\omega_i\ge0$,
$\sum_i\omega_i=1$, and retain both $i$ and the complete output word.
Use the same-phase reference, basis phase $\alpha=\pi/2$ and pulse of
Parent/Readout Theorem 8.11. Equivalently, the Hamiltonian convention of (8.6) has
$\beta=-\pi$ and pulse duration $\tau=\pi/4$. The signal family is

$$
|\psi_\theta\rangle
=\sum_u\sqrt{p_u}e^{-i\theta f_u}|u\rangle,\qquad f:B_n\to\mathbb R.
\tag{1.3}
$$

The unknown signal $\theta$ and the supplied pulse duration $\tau$ are
different parameters. Write $J_\omega[f]$ for the classical Fisher
information at $\theta=0$, and write $\mathcal Q_p[f]$ for the pure-state
quantum Fisher information of (1.3). Set

$$
\mathcal E_i(f,f)=
\sum_{\substack{\{u,v\}\in E(\Gamma_n)\\u,v\text{ differ at }i}}
\frac{p_up_v}{p_u+p_v}(f_u-f_v)^2.
\tag{1.4}
$$

### 1.2. Matching the experiment to the parent spectrum

**Theorem 1.3 (Activity-matched information spectrum).** Under
Definitions 1.1–1.2, let

$$
H_\omega=\sum_i\omega_iK_i,\qquad
\bar f=\sum_up_uf_u,\qquad
g=D(f-\bar f\,\mathbf 1).
\tag{1.5}
$$

For every real $f$,

$$
J_\omega[f]=4\langle g,H_\omega g\rangle,\qquad
\mathcal Q_p[f]=4\|g\|^2.
\tag{1.6}
$$

In particular, choose

$$
R=\sum_i(1+a_i),\qquad
\omega_i=\frac{1+a_i}{R}.
\tag{1.7}
$$

Then, writing $\Delta_{\rm loc}$ for the lowest eigenvalue of
$H_{\rm loc}$ on $\psi_+^\perp$,

$$
\inf_{\mathcal Q_p[f]>0}\frac{J_\omega[f]}{\mathcal Q_p[f]}
=\frac{\Delta_{\rm loc}}{R}.
\tag{1.8}
$$

For the same choice (1.7), the entire generalized spectrum of the pair of
information forms $(J_\omega,\mathcal Q_p)$ after quotienting the
constant phase is the spectrum of $H_{\rm loc}|_{\psi_+^\perp}/R$.

Proof. Orient an insertion edge at $i$ as $u_i=0,v_i=1$. The same law
(1.1) supplies $p_v=a_ip_u$. On its two-dimensional block,

$$
K_i|_{\{u,v\}}
=\frac1{p_u+p_v}
\begin{pmatrix}
p_v&-\sqrt{p_up_v}\\
-\sqrt{p_up_v}&p_u
\end{pmatrix}.
\tag{1.9}
$$

The blocks at fixed $i$ are disjoint, and blocked words contribute zero.
This proves the normalization in (1.2) and gives

$$
\langle Df,K_iDf\rangle=\mathcal E_i(f,f).
\tag{1.10}
$$

The two resolved outcomes on this edge have, at the reference, masses
$(p_u+p_v)/2$ and opposite derivatives
$\sqrt{p_up_v}(f_v-f_u)$. Their total Fisher contribution is
$4p_up_v(f_v-f_u)^2/(p_u+p_v)$, exactly as in Parent/Readout Theorem 8.11.
The recorded, signal-independent site label weights this contribution
by $\omega_i$, so $J_\omega[f]=4\sum_i\omega_i\mathcal E_i(f,f)$.
The pure-state formula used in Parent/Readout Proposition 8.14 gives
$\mathcal Q_p[f]=4\operatorname{Var}_p(f)$.

Each $K_i$ annihilates $\psi_+$, so centering $f$ does not change the
energy. This proves (1.6). The map $f\mapsto Df$ sends the real subspace
$\{f:\sum_up_uf_u=0\}$ bijectively onto the real part of
$\psi_+^\perp$, and $\|Df\|^2=\operatorname{Var}_p(f)$ there.
For (1.7), $H_\omega=H_{\rm loc}/R$. The Rayleigh principle proves
(1.8), and this same invertible change of variables proves the full
generalized-spectrum statement. The parent is real symmetric, so its
restriction has a real eigenbasis; restricting $f$ to real directions
loses none of these eigenvalues. $\square$

Theorem 1.3 is a concrete synthesis of the resolved experiment of Parent/Readout §8
and the activity parent of Boundary Calculus §15.9. Its general tools
are the classical stochastic-matrix-form correspondence below and the
pure-state Fisher formula already attributed in Parent/Readout §8.13. The choice
(1.7) matches the parent; it does not assert optimality among site
distributions.

### 1.3. The resampling clock and the energy curvature

**Corollary 1.4 (Unit refresh, parent refresh and phase curvature).**
For the same activity law, let $\mathscr L_p$ be the function generator
of Parent/Readout Proposition 8.13, with one unit refresh rate at each site, and let
$\gamma(p)$ be its variational gap. Define $H_{\rm hb}=\sum_iK_i$.
Then

$$
H_{\rm hb}=-D\mathscr L_pD^{-1},\qquad
\operatorname{gap}(H_{\rm hb})=\gamma(p).
\tag{1.11}
$$

Consequently

$$
\min_i(1+a_i)\gamma(p)
\le\Delta_{\rm loc}
\le\max_i(1+a_i)\gamma(p).
\tag{1.12}
$$

For uniform activity $a_i=a$, $H_{\rm loc}=(1+a)H_{\rm hb}$.
For the matched experiment (1.7),

$$
J_\omega[f]=\frac2R
\left.\frac{d^2}{d\theta^2}
\langle\psi_\theta|H_{\rm loc}|\psi_\theta\rangle
\right|_{\theta=0}.
\tag{1.13}
$$

Proof. The edge block of $-\mathscr L_p$ is
$(p_u+p_v)^{-1}\begin{pmatrix}p_v&-p_v\\-p_u&p_u\end{pmatrix}$.
Conjugating by $D$ gives (1.9). Summing each unordered edge once proves
the first equality in (1.11), without an extra factor $1/2$.
This is the stochastic-matrix-form transform of
Castelnovo–Chamon–Mudry–Pujol, equations (19b), (22a–e) and (26a–c),
with their column generator equal to $\mathscr L_p^{\mathsf T}$;
see the [source note][SMF1].
The graph $\Gamma_n$ is connected because every occupied word can
delete bits to reach $0^n$. The common zero ray is therefore simple,
and similarity proves the gap equality.

The positive terms $K_i$ give
$\min_i(1+a_i)H_{\rm hb}\preceq H_{\rm loc}
\preceq\max_i(1+a_i)H_{\rm hb}$. All three operators have the same
zero ray. The Rayleigh principle on its orthogonal complement gives
(1.12). Equivalently, $H_{\rm loc}$ is the transform of the reversible
chain having insertion rate $a_i$ and deletion rate $1$ at site $i$:
it uses site refresh rate $1+a_i$.

On a phase-rotated edge, the $K_i$ energy is
$2p_up_v[1-\cos(\theta(f_u-f_v))]/(p_u+p_v)$.
Its second derivative at zero is twice the edge contribution in (1.4).
Summing with coefficients $1+a_i$ and using (1.7) proves (1.13).
$\square$

In matrix coordinates, (1.6) reads
$J_\omega=4DH_\omega D$ and
$\mathbf Q_p=4(D^2-pp^{\mathsf T})$.
Thus the ordinary Fisher matrix is related by congruence to the
parent. Its ordinary eigenvalues are not the parent energies.
The comparison in Theorem 1.3 is a generalized spectrum, or equivalently
a Rayleigh quotient normalized by quantum Fisher information.
The semigroup identity from (1.11) is
$e^{-sH_{\rm hb}}=De^{s\mathscr L_p}D^{-1}$ for $s\ge0$;
it concerns imaginary-time evolution, rather than real-time unitary
motion. Multiplying every refresh rate by $r$ scales classical gaps by
$r$; multiplying the Hamiltonian by an energy unit $\varepsilon$
scales energy gaps by $\varepsilon$.

### 1.4. Exact finite boundaries

**Proposition 1.5 (A parent gap alone does not bound local sensitivity).**
For $n=2$, uniform $a>0$ and the uniform recorded-site experiment,

$$
\operatorname{spec}H_{\rm loc}=\{0,1,1+2a\},\qquad
\inf_{\mathcal Q_p[f]>0}\frac{J_p[f]}{\mathcal Q_p[f]}
=\frac1{2(1+a)}.
\tag{1.14}
$$

Proof. In the ordered basis $(00,10,01)$ the parent is
$\begin{pmatrix}2a&-\sqrt a&-\sqrt a\\-\sqrt a&1&0\\
-\sqrt a&0&1\end{pmatrix}$.
Its ground vector is proportional to $(1,\sqrt a,\sqrt a)$;
$(0,1,-1)$ has eigenvalue $1$, and
$(-2\sqrt a,1,1)$ has eigenvalue $1+2a$.
These nonzero mutually orthogonal vectors form a basis.
Uniform sampling is the matched choice, with $R=2(1+a)$,
so Theorem 1.3 gives (1.14). The parent gap remains $1$ while the
information ratio tends to zero as $a\to\infty$. $\square$

**Proposition 1.6 (Known product phases preserve the calibrated identity).**
Let
$U_\varphi=\bigotimes_i\operatorname{diag}(1,e^{i\varphi_i})$.
Replace the reference and parent by $U_\varphi\psi_+$ and
$U_\varphi H_{\rm loc}U_\varphi^\dagger$, and use pulse phase
$\beta_i=\varphi_i-\pi$ at site $i$. Then Theorem 1.3 and (1.13)
hold with these replacements.

Proof. The diagonal unitary preserves $\mathcal K_n$, commutes with
the diagonal signal generator and leaves complete-word outcome
probabilities invariant. Direct conjugation of (8.6) gives
$U_\varphi H_i(\beta)U_\varphi^\dagger=H_i(\beta+\varphi_i)$.
Hence the entire calibrated experiment has the original joint outcome
law, while parent spectra and energies are unchanged. $\square$

**Proposition 1.7 (Reference, support and locality boundaries).** The
reference information identity need not hold away from its calibrated
phase. The legal-space restriction and positive-support restriction
cannot be dropped from the spectral correspondence. Arbitrary positive
laws need not give parents on three consecutive tensor positions.

Proof. To test the reference condition,
take $n=1$, $p=(1/3,2/3)$, $f=(0,1)$ and keep the fixed reference pulse.
The two probabilities along (1.3) are
$q_\pm(\theta)=1/2\pm(\sqrt2/3)\sin\theta$.
At $\theta=\pi/2$ both are positive but their derivatives vanish;
classical information is zero, although $\mathcal Q_p[f]=8/9$.
Thus (1.6) is local at the calibrated reference.

For $n=1$ the spectra are $\{0,1\}$ for $H_{\rm hb}$ and
$\{0,1+a_1\}$ for $H_{\rm loc}$, so the matched information ratio is
$1$. On the unrestricted tensor space, $n=2$ has the additional zero
vector $|11\rangle$; the legal-space restriction cannot be omitted.
If a law has zero masses, the invertible transform applies only after
restricting to its positive support. Disconnected support has
zero global variance-normalized gap; this is different from its
smallest strictly positive energy above a degenerate zero space.
Singleton support has no positive-variance phase direction.

The three-position locality in (1.2) uses the activity insertion ratio.
An arbitrary positive law need not have that locality. On $B_4$, for
$p(u)\propto e^{\kappa u_1u_4}$ with $\kappa>0$, the insertion ratio at
site $1$ is $1$ or $e^\kappa$ according to $u_4$. Its normalized
off-diagonal coefficient has magnitude respectively
$1/2$ or $e^{\kappa/2}/(1+e^\kappa)<1/2$.
No sum of terms on at most three consecutive sites can reproduce
these site-$1$ matrix elements: every term that changes site $1$
has identical action for the two remote values of site $4$.
The matrix transform survives, but the stated tensor locality does not.
$\square$

[SMF1]: ../../../Library/StatisticalMechanics/castelnovo2005stochasticmatrixform.md

## 追加锚（本行以下为增补区）

## 2. The exact optimal five-state phase-readout design

### 2.1. The fixed law and grouped site operators

Use the uniform law on the five legal words
$(000,100,010,001,101)$, in that order, and the calibrated reference
experiment of Parent/Readout §8. All three activities in §1 are one. Write
$e_0,e_1,e_2,e_3,e_{13}$ for the corresponding orthonormal vectors and
$\psi=\mathbf1/\sqrt5$. The normalized site operators are

$$
\begin{aligned}
K_1&=\tfrac12\bigl[
(e_0-e_1)(e_0-e_1)^{\mathsf T}
+(e_3-e_{13})(e_3-e_{13})^{\mathsf T}\bigr],\\
K_2&=\tfrac12(e_0-e_2)(e_0-e_2)^{\mathsf T},\\
K_3&=\tfrac12\bigl[
(e_0-e_3)(e_0-e_3)^{\mathsf T}
+(e_1-e_{13})(e_1-e_{13})^{\mathsf T}\bigr].
\end{aligned}
\tag{2.1}
$$

Each $K_i$ is an orthogonal projection and annihilates $\psi$.
For a recorded site distribution
$\omega\in\Delta_3=\{\omega_i\ge0:\sum_i\omega_i=1\}$, define

$$
H_\omega=\sum_i\omega_iK_i,\qquad
\gamma(\omega)=\lambda_{\min}(H_\omega|_{\psi^\perp}).
\tag{2.2}
$$

The experiment's exact Fisher/QFI identity gives

$$
\gamma(\omega)=
\inf_{f:\mathcal Q_p[f]>0}
\frac{\mathcal J_\omega[f]}{\mathcal Q_p[f]}.
\tag{2.3}
$$

The budget is one sampled site per trial, and the site label is retained.
The two edges attached to each endpoint site share its single weight;
they cannot be assigned independent edge budgets.

**Definition 2.1 (An isolated algebraic parameter).** Let $\tau$ be
the unique root in $(1/2,13/25)$ of

$$
P_4(t)=12t^4+20t^3-2t^2-4t-1.
\tag{2.4}
$$

Set

$$
q=4\tau^2+2\tau-1,\qquad
D=2q+4\tau(1-\tau^2),\qquad
x=\frac qD,\qquad y=\frac{4\tau(1-\tau^2)}D.
\tag{2.5}
$$

These definitions are unambiguous:
$P_4(1/2)=-1/4$ and $P_4(13/25)=26857/390625>0$, while
$P_4'(t)=48t^3+60t^2-4t-4\ge373/25>0$ throughout the
isolating interval. The intermediate value theorem and strict
monotonicity give existence and uniqueness there. Also $q>0$,
$0<x<1/2$, $y>0$, and $2x+y=1$.

### 2.2. A primal spectrum and a common test direction

**Theorem 2.2 (Exact global optimum).** The unique maximizer of
(2.2) over the entire site simplex is

$$
\boxed{\omega^\star=(x,y,x),\qquad
\gamma^\star=(1-\tau)x.}
\tag{2.6}
$$

In particular, the optimization includes nonsymmetric distributions
and every zero-weight boundary. Numerical values are

$$
\tau\approx0.51588140,\qquad
\omega^\star\approx(0.29574131,0.40851737,0.29574131),\qquad
\gamma^\star\approx0.14317387.
\tag{2.7}
$$

Proof. Consider the vector

$$
v=(2\tau^2-1,\ \tau,\ -2\tau(\tau+1),\ \tau,\ 1)^{\mathsf T}.
\tag{2.8}
$$

Its coordinates sum to zero, and
$yq=4\gamma^\star\tau(\tau+1)$ by (2.5).
Direct substitution into (2.1) gives
$(H_{\omega^\star}v)_{13}=x(1-\tau)$,
$(H_{\omega^\star}v)_1=(H_{\omega^\star}v)_3
=x\tau(1-\tau)$, and
$(H_{\omega^\star}v)_2=-yq/2$.
These are the corresponding coordinates of $\gamma^\star v$.
The remaining coordinate agrees because $H_{\omega^\star}\mathbf1=0$
and both vectors have coordinate sum zero. Thus

$$
H_{\omega^\star}v=\gamma^\star v.
\tag{2.9}
$$

To identify this eigenvalue as the gap, take any $x,y>0$ and
$H_{(x,y,x)}$. The endpoint-odd vector $e_1-e_3$ has eigenvalue $x$.
In the orthonormal even basis
$(e_2,e_0,(e_1+e_3)/\sqrt2,e_{13})$, the matrix is

$$
T_{x,y}=
\begin{pmatrix}
y/2&-y/2&0&0\\
-y/2&x+y/2&-x/\sqrt2&0\\
0&-x/\sqrt2&x&-x/\sqrt2\\
0&0&-x/\sqrt2&x
\end{pmatrix}.
\tag{2.10}
$$

Its characteristic polynomial is $sC_{x,y}(s)$, where

$$
C_{x,y}(s)=s^3-(3x+y)s^2+
\left(2x^2+\tfrac52xy\right)s-\tfrac54yx^2.
\tag{2.11}
$$

The positive-weight legal graph is connected, so its only zero mode
is constant and the three roots $r_1\le r_2\le r_3$ of $C_{x,y}$
are positive. Their sum is $3x+y>3x$, so $r_3>x$.
Since $C_{x,y}(x)=yx^2/4>0$, the factorization
$C_{x,y}(x)=\prod_j(x-r_j)$ then forces

$$
0<r_1<x<r_2\le r_3.
\tag{2.12}
$$

Consequently $r_1$ is simple. The candidate
$\gamma^\star=x(1-\tau)$ lies in $(0,x)$, so (2.9) and
(2.12) prove that it is the gap of $H_{\omega^\star}$.

Now write

$$
N_v=v^{\mathsf T}v
=8\tau^4+8\tau^3+2\tau^2+2,\qquad
Z^\star=\frac{vv^{\mathsf T}}{N_v}.
\tag{2.13}
$$

This is positive semidefinite, has trace one and annihilates $\psi$.
The three grouped energies are

$$
\begin{aligned}
v^{\mathsf T}K_1v=v^{\mathsf T}K_3v
&=\tfrac12(1-\tau)^2\bigl((2\tau+1)^2+1\bigr),\\
v^{\mathsf T}K_2v&=\tfrac12q^2.
\end{aligned}
\tag{2.14}
$$

Their equality follows from the exact polynomial identity

$$
q^2-(1-\tau)^2\bigl((2\tau+1)^2+1\bigr)=P_4(\tau)=0.
\tag{2.15}
$$

Together with (2.9) and $\sum_i\omega_i^\star=1$, this gives

$$
\operatorname{Tr}(Z^\star K_i)
=\frac{q^2}{2N_v}=\gamma^\star
\quad\text{for every }i.
\tag{2.16}
$$

For every $\omega\in\Delta_3$, the Rayleigh quotient of this same
vector therefore supplies the global upper bound

$$
\gamma(\omega)
\le\frac{v^{\mathsf T}H_\omega v}{N_v}
=\sum_i\omega_i\operatorname{Tr}(Z^\star K_i)
=\gamma^\star.
\tag{2.17}
$$

The candidate attains the bound. Equivalently, with
$\Pi=I-\psi\psi^{\mathsf T}$, its primal and dual certificates are

$$
H_{\omega^\star}-\gamma^\star\Pi\succeq0,\qquad
(H_{\omega^\star}-\gamma^\star\Pi)Z^\star=0,
\tag{2.18}
$$

together with (2.13) and (2.16).

For uniqueness, equality in (2.17) requires
$H_\omega v=\gamma^\star v$. Its endpoint-coordinate difference is

$$
(H_\omega v)_1-(H_\omega v)_3
=(\omega_1-\omega_3)(1-\tau^2).
\tag{2.19}
$$

Since $v_1=v_3$ and $1-\tau^2>0$, the weights satisfy
$\omega_1=\omega_3$. The $13$ coordinate then yields

$$
\frac{\omega_1+\omega_3}{2}(1-\tau)=\gamma^\star,
\tag{2.20}
$$

so both endpoint weights are $x$, and the remaining weight is $y$.
This proves uniqueness among all site distributions. $\square$

### 2.3. Observable consequences and scope

If $\omega_2=0$, state $2$ is isolated. If $\omega_1=0$,
$\{1,13\}$ separates from the remaining states; if $\omega_3=0$,
$\{3,13\}$ separates. The graph is disconnected throughout the
simplex boundary, and $\gamma(\omega)=0$ there.

The center weight at the optimum is larger than either endpoint
weight. Indeed $y-x=[1+2\tau-4\tau^2-4\tau^3]/D>0$:
the numerator decreases on the isolating interval and its value at
$13/25$ is $6187/15625>0$. Uniqueness then shows that uniform
site sampling is strictly suboptimal. Its gap is approximately
$0.13831892$, compared with (2.7).

The worst reference-phase direction at the optimum is explicitly

$$
g^\star=\frac v{\sqrt{N_v}},\qquad
f^\star=\frac{\sqrt5\,v}{\sqrt{N_v}},\qquad
\mathbb E_pf^\star=0,\qquad
\mathcal Q_p[f^\star]=4,\qquad
\mathcal J_{\omega^\star}[f^\star]=4\gamma^\star.
\tag{2.21}
$$

The factor $1/2$ in (2.1) is retained throughout. A graph
Laplacian that instead gives each selected edge weight $\omega_i$
is $L_\omega=2H_\omega$ and has twice this gap. The sampled
Fisher/QFI ratio uses $H_\omega$, hence (2.6).

The conclusion concerns the fixed uniform five-state law, the
recorded-site measurement menu and the calibrated reference phase.
It proves neither optimality among arbitrary quantum measurements
nor a result away from that reference. Unequal sampling changes
this menu's information operator; it does not change the occupation
law or identify dimensionless information with physical energy.
The activity-matched distribution of §1 supplies an exact parent
spectrum correspondence, while (2.6) separately optimizes this
five-state sampling budget. General activities and longer legal
chains require their own optimality certificates.

## 3. Exact optimal readout for positive reflection-symmetric activities

### 3.1. The fixed activity law and its spectral coordinates

Retain the five legal words and the recorded-site, calibrated reference
experiment of §Parent/Readout §8–10. Fix $a,b>0$, write $s=1+a$ and $Z=s^2+b$, and use
the single actual law and positive reference vector

$$
p=\frac{(1,a,b,a,a^2)}Z,\qquad
\psi=\frac{(1,\sqrt a,\sqrt b,\sqrt a,a)}{\sqrt Z}.
\tag{3.1}
$$

This is the hard-core activity family with equal endpoint activities.
Its joint weight is $a^2$; an independently adjustable pair interaction
is not part of (3.1). Define

$$
\begin{aligned}
K_1&=\frac{
(\sqrt a\,e_0-e_1)(\sqrt a\,e_0-e_1)^{\mathsf T}
+(\sqrt a\,e_3-e_{13})(\sqrt a\,e_3-e_{13})^{\mathsf T}}s,\\
K_2&=\frac{(\sqrt b\,e_0-e_2)(\sqrt b\,e_0-e_2)^{\mathsf T}}{1+b},\\
K_3&=\frac{
(\sqrt a\,e_0-e_3)(\sqrt a\,e_0-e_3)^{\mathsf T}
+(\sqrt a\,e_1-e_{13})(\sqrt a\,e_1-e_{13})^{\mathsf T}}s.
\end{aligned}
\tag{3.2}
$$

These are orthogonal projections annihilating $\psi$. For
$\omega\in\Delta_3$, put $H_\omega=\sum_i\omega_iK_i$ and
$\gamma(\omega)=\lambda_{\min}(H_\omega|_{\psi^\perp})$.
The identity of §1 identifies this gap with the minimum
Fisher/QFI ratio for the same law and experiment. The site budget
continues to tie both endpoint blocks to one weight.

**Definition 3.1 (Secular coefficients and selected root).** Set

$$
c_0=\frac{Z}{s^2(1+b)},\qquad
c_1=\frac{2ab}{s^2(1+b)},\qquad
c_2=\frac{a^2b}{s^2(1+b)}.
\tag{3.3}
$$

All three coefficients are positive and sum to one. They will be
squared spectral coordinates, rather than occupation probabilities.
For $0<t<1$, define

$$
\mathscr F(t)=\frac{c_0}t-\frac{c_1}{1-t}-\frac{c_2}{2-t},
\qquad
\mathscr R(t)=
\sqrt{\frac{c_1}{2(1-t)^2}+\frac{c_2}{(2-t)^2}}.
\tag{3.4}
$$

With $B_c=1+2c_0+c_1$, let

$$
N(t)=t^2-B_ct+2c_0,\qquad
t_0=\frac{B_c-\sqrt{B_c^2-8c_0}}2.
\tag{3.5}
$$

The polynomial $N$ is positive at zero and negative at one:
$N(0)=2c_0>0$ and $N(1)=-c_1<0$. Thus its smaller root
$t_0$ lies in $(0,1)$ and its larger root exceeds one. Also

$$
\mathscr F(t)=\frac{N(t)}{t(1-t)(2-t)}.
\tag{3.6}
$$

The function $\mathscr F$ strictly decreases from $+\infty$ to
zero on $(0,t_0)$, while $\mathscr R$ is positive and strictly
increasing. Consequently there is a unique $t_*\in(0,t_0)$ with

$$
\mathscr F(t_*)=\mathscr R(t_*).
\tag{3.7}
$$

Equivalently, $t_*$ is the unique root in that interval of

$$
2N(t)^2-t^2\bigl[c_1(2-t)^2+2c_2(1-t)^2\bigr]=0.
\tag{3.8}
$$

The interval keeps $\mathscr F$ positive and excludes extraneous
roots introduced by squaring.

### 3.2. Global optimum, branch ordering and uniqueness

**Theorem 3.2 (Positive-activity optimal site design).** Write
$F_*=\mathscr F(t_*)$. The unique maximizer among all site
distributions is

$$
\boxed{
\omega^*=\frac{(F_*,1,F_*)}{1+2F_*},\qquad
\gamma^*=\frac{t_*F_*}{1+2F_*}.
}
\tag{3.9}
$$

For every finite $a,b>0$, the active gap is simple and reflection
even. A rank-one certificate suffices for global optimality, including
comparison with every nonsymmetric distribution and every boundary.

Proof. Put $e_+=(e_1+e_3)/\sqrt2$, $o=(e_1-e_3)/\sqrt2$, and

$$
\begin{aligned}
g&=\frac{e_0+\sqrt{2a}\,e_++a e_{13}}s,\\
h&=\frac{\sqrt{2a}(e_0-e_{13})+(a-1)e_+}s,\\
k&=\frac{a e_0-\sqrt{2a}\,e_++e_{13}}s,\\
u&=\frac{\sqrt b\,g-s e_2}{\sqrt Z}.
\end{aligned}
\tag{3.10}
$$

Direct inner products show that $(\psi,u,h,k,o)$ is orthonormal,
with $\psi=(sg+\sqrt b\,e_2)/\sqrt Z$. Let $A=K_1+K_3$ and
$\Delta=K_1-K_3$. Substitution into (3.2) gives

$$
A|_{\psi^\perp}=\operatorname{diag}(0,1,2,1)
\quad\text{in the order }(u,h,k,o),
\tag{3.11}
$$

$$
\Delta u=\Delta k=0,\qquad
\Delta h=-o,\qquad\Delta o=-h,
\tag{3.12}
$$

and

$$
K_2=ww^{\mathsf T},\qquad
w=\sqrt{c_0}\,u+\sqrt{c_1}\,h+\sqrt{c_2}\,k.
\tag{3.13}
$$

All these are identities in an ordinary orthonormal space; no
weighted occupation-coordinate quotient is treated as Euclidean.

For symmetric weights $(x,y,x)$ with $x,y>0$ and $2x+y=1$,
the odd eigenvalue is $x$, and the even block on $\psi^\perp$ is

$$
M(x)=\operatorname{diag}(0,x,2x)+y\,cc^{\mathsf T},
\qquad c=(\sqrt{c_0},\sqrt{c_1},\sqrt{c_2})^{\mathsf T}.
\tag{3.14}
$$

Its secular function is
$1+y\sum_{j=0}^2c_j/(jx-\lambda)$. Its derivative with respect
to $\lambda$ is strictly positive off its three poles. At successive
ends of $(0,x)$ and $(x,2x)$ it runs from $-\infty$ to
$+\infty$, and on $(2x,\infty)$ it runs from $-\infty$ to
one. Thus its three eigenvalues satisfy

$$
0<\lambda_1<x<\lambda_2<2x<\lambda_3.
\tag{3.15}
$$

The first root is strictly positive by its open interval.
The poles themselves are not eigenvalues
because every $c_j>0$. This also proves simplicity and identifies
$\lambda_1$ as the full gap.

Writing $\lambda_1=xt$, the secular equation is
$(y/x)\mathscr F(t)=1$. Hence all positive symmetric weights
are parameterized by $t\in(0,t_0)$ through

$$
x=\frac{\mathscr F(t)}{1+2\mathscr F(t)},\qquad
y=\frac1{1+2\mathscr F(t)},\qquad
\gamma(t)=\frac{t\mathscr F(t)}{1+2\mathscr F(t)}.
\tag{3.16}
$$

Differentiation yields

$$
\gamma'(t)=
\frac{2\mathscr F(t)^2
-c_1/(1-t)^2-2c_2/(2-t)^2}
{(1+2\mathscr F(t))^2}.
\tag{3.17}
$$

It is positive before the root (3.7) and negative afterward,
because its numerator is
$2(\mathscr F-\mathscr R)(\mathscr F+\mathscr R)$.
This proves unique optimality within symmetric weights.

For a certificate against all weights, use

$$
v=\frac{\sqrt{c_0}}{t_*}u
-\frac{\sqrt{c_1}}{1-t_*}h
-\frac{\sqrt{c_2}}{2-t_*}k,\qquad
L=v^{\mathsf T}v
=\frac{c_0}{t_*^2}
+\frac{c_1}{(1-t_*)^2}
+\frac{c_2}{(2-t_*)^2}.
\tag{3.18}
$$

Then $v\perp\psi$, $w^{\mathsf T}v=F_*$, and (3.16) gives
$H_{\omega^*}v=\gamma^*v$. Reflection and (3.11) give

$$
v^{\mathsf T}K_1v=v^{\mathsf T}K_3v
=\frac12\left[\frac{c_1}{(1-t_*)^2}
+\frac{2c_2}{(2-t_*)^2}\right]
=F_*^2=v^{\mathsf T}K_2v.
\tag{3.19}
$$

The middle equality is (3.7). Since the candidate weights sum
to one, $\gamma^*=F_*^2/L$. Therefore
$Y_*=vv^{\mathsf T}/L$ is positive semidefinite, has trace one,
annihilates $\psi$, and satisfies
$\operatorname{Tr}(Y_*K_i)=\gamma^*$ for every site. For all
$\omega\in\Delta_3$,

$$
\gamma(\omega)\le
\frac{v^{\mathsf T}H_\omega v}{L}
=\sum_i\omega_i\operatorname{Tr}(Y_*K_i)=\gamma^*.
\tag{3.20}
$$

The candidate attains this upper bound by (3.15).

If another distribution attains it, equality in the Rayleigh
quotient implies $H_\omega v=\gamma^*v$. Write
$x=(\omega_1+\omega_3)/2$ and
$\delta=(\omega_1-\omega_3)/2$. Its odd component, by (3.12), is
$-\delta v_h o$. But
$v_h=-\sqrt{c_1}/(1-t_*)\ne0$, so $\delta=0$.
The $u$ coordinate then gives

$$
(1-2x)\sqrt{c_0}F_*
=\gamma^*\frac{\sqrt{c_0}}{t_*},
\tag{3.21}
$$

which fixes the center weight at $1/(1+2F_*)$ and both endpoint
weights at $F_* /(1+2F_*)$. This proves global uniqueness.
If any weight is zero, the positive-law legal graph disconnects
as in §3.3, and its gap is zero. $\square$

The trace-one spectral certificate is the classical $E$-optimal
design mechanism; see [Dette and Grigoriev, Theorem 2.1 and
Remark 2.1][DG3]. The source-specific conclusion here is the
explicit reduction (3.10)–(3.14), the selected root and the
nonzero odd coupling that proves uniqueness for these grouped sites.
A general equivalence theorem alone does not supply these facts.

### 3.3. A universal center premium and the occupation bridge

**Theorem 3.3 (Sampling bounds and the joint-occupation coefficient).**
For every finite positive activity pair,

$$
\frac14<\omega_1^*=\omega_3^*<\frac13
<\omega_2^*<\frac12.
\tag{3.22}
$$

For the law (3.1), set
$X=\mathbb E_p n_1=\mathbb E_p n_3$,
$z=\mathbb E_p n_2$, $\kappa=\mathbb E_p(n_1n_3)$,
$p_0=p(000)$ and $D_{\rm occ}=(1-z)(p_0+z)$. Then the
coefficients of the same optimal-design problem satisfy

$$
c_0=\frac{p_0}{D_{\rm occ}},\qquad
c_1=\frac{2z(X-\kappa)}{D_{\rm occ}},\qquad
c_2=\frac{z\kappa}{D_{\rm occ}}
=\frac{\operatorname{Cov}_p(n_1,n_3)}{D_{\rm occ}}.
\tag{3.23}
$$

Proof. At the root, (3.7) and $\sum_jc_j=1$ give the identities

$$
\frac{c_1}{(1-t_*)^2}
=(2F_*-1)((2-t_*)F_*+1)>0,
\tag{3.24}
$$

$$
\frac{2c_2}{(2-t_*)^2}
=1-t_*F_*-2(1-t_*)F_*^2>0.
\tag{3.25}
$$

The first implies $F_*>1/2$. If $F_*\ge1$, the right side of
the second is at most $t_*-1<0$, a contradiction. Thus
$1/2<F_*<1$, and (3.9) gives (3.22).

Conditioned on $n_2=0$, the endpoint occupations are independent
Bernoulli variables with parameter $\rho=a/(1+a)$, directly
from the four weights $(1,a,a,a^2)$. Hence

$$
X=(1-z)\rho,\qquad
\kappa=(1-z)\rho^2,\qquad
\kappa(1-z)=X^2,\qquad
\operatorname{Cov}_p(n_1,n_3)=\kappa z.
\tag{3.26}
$$

Also $p_0=1/Z$, $z=b/Z$, $X-\kappa=a/Z$ and
$D_{\rm occ}=s^2(1+b)/Z^2$. Substitution into (3.3)
gives (3.23). In particular, the activities can be recovered as

$$
a=\frac{\kappa}{X-\kappa},\qquad
b=\frac{\kappa-X^2}{(X-\kappa)^2}.
\tag{3.27}
$$

These formulas require the law (3.1), rather than arbitrary
reflection-symmetric five-state probabilities. $\square$

The coefficient $c_2$ measures the center projector's squared
overlap with the double-endpoint spectral direction $k$.
It is determined by a normalized occupation covariance.
It is not a complex coherence or an interaction energy.

For a centered phase function $f$, put $q_j=\psi_jf_j$.
Direct substitution in the endpoint projector gives

$$
q^{\mathsf T}K_1q
=\frac{X-\kappa}{1+a}(f_0-f_1)^2
+\frac{\kappa}{1+a}(f_3-f_{13})^2.
\tag{3.28}
$$

Thus the joint state supplies a second phase-difference block
whose conductance relative to the first is
$\kappa/(X-\kappa)=a$. Both blocks consume the same endpoint
site budget. Changing the phases of the pure state leaves
$X,z,\kappa$ unchanged while changing its off-diagonal entries;
the occupation bridge does not determine arbitrary coherence.

### 3.4. Heat-bath interpretation and support boundaries

For $D_\psi=\operatorname{diag}(\psi)$, the matrices

$$
P_i=D_\psi^{-1}(I-K_i)D_\psi,\qquad
P_\omega=\sum_i\omega_iP_i
=D_\psi^{-1}(I-H_\omega)D_\psi
\tag{3.29}
$$

are the legal single-site heat-bath kernels and their random-scan
mixture. On an endpoint pair the conditional probabilities are
$(1,a)/(1+a)$; on the center pair they are $(1,b)/(1+b)$.
The spectrum of $I-H_\omega$ is nonnegative because it is a
convex combination of orthogonal projections. Thus

$$
\operatorname{SLEM}(P_\omega)=1-\gamma(\omega).
\tag{3.30}
$$

Theorem 3.2 also solves fastest mixing within this fixed affine
family of site kernels. The general spectral optimization and
prescribed-equilibrium framework belongs to [Boyd, Diaconis and
Xiao, §§2, 6][BDX3]. Allowing independently chosen graph-edge
probabilities would be a different feasible family.

**Theorem 3.4 (Positive-support limits differ from support restriction).**
With the other activity fixed and positive, either $a\downarrow0$
or $b\downarrow0$ gives

$$
\omega^*\longrightarrow(1/3,1/3,1/3),\qquad
\gamma^*\longrightarrow1/3.
\tag{3.31}
$$

At exactly $a=0$, restricting the phase experiment to its actual
support $\{0,2\}$ instead gives optimal ratio one under center-only
sampling. At exactly $b=0$, restricting it to
$\{0,1,3,13\}$ instead gives optimal ratio $1/2$ under
$(1/2,0,1/2)$.

Proof. In either positive-activity limit,
$(c_0,c_1,c_2)\to(1,0,0)$. The even matrix (3.14)
therefore converges uniformly in $x\in[0,1/2]$ to
$\operatorname{diag}(1-2x,x,2x)$, while the odd eigenvalue
remains $x$. Its gap is $\min\{x,1-2x\}$, uniquely maximized
at $x=1/3$ with value $1/3$. Continuity of the minimum eigenvalue
and compactness imply convergence of the symmetric optimizers
and values. Global symmetry for every positive activity pair was
proved in Theorem 3.2.

At $a=0$, the restricted endpoint projectors vanish and $K_2$
is the sole rank-one projection on the nonconstant phase
direction, so the restricted gap is $\omega_2$. At $b=0$,
the restricted center projector vanishes and the endpoint
operators act on the two independent hard-core endpoint bits.
On the nonconstant directions their mixture has eigenvalues
$\omega_1,\omega_3,\omega_1+\omega_3$, so its minimum is maximized
by the stated weights. $\square$

Positive-support minimax includes directions on rare states after
normalization by their QFI. Removing those directions at zero
support changes the parameter space. Theorems 3.2–3.4 concern
the fixed reference-phase, recorded-site experiment. They establish
no optimum over arbitrary quantum measurements, physical control
availability or pair-interaction family with joint weight distinct
from $a^2$.

[DG3]: ../../../Library/Estimation/dettegrigoriev2014eoptimal.md
[BDX3]: ../../../Library/Estimation/boyddiaconisxiao2004fastestmixing.md

## 追加锚（本行以下为增补区）

## 4. Independent joint occupation and a change of the active phase sector

### 4.1. One actual law and the two square-sector eigenvalues

Allow the joint occupation weight to vary independently. Fix $a,b,c>0$
and put

$$
T=1+2a+c,\qquad Z=T+b,\qquad
p=\frac{(1,a,b,a,c)}Z,\qquad
\psi=\frac{(1,\sqrt a,\sqrt b,\sqrt a,\sqrt c)}{\sqrt Z}.
\tag{4.1}
$$

The state order and the recorded-site reference-phase experiment remain
those of Parent/Readout §8. This enlarges the activity family of §3, recovered when
$c=a^2$. It does not change the definition of its site budget. The
information projectors of the same actual law are

$$
\begin{aligned}
K_1&=\frac{(\sqrt a\,e_0-e_1)(\sqrt a\,e_0-e_1)^{\mathsf T}}{1+a}
+\frac{(\sqrt c\,e_3-\sqrt a\,e_{13})
(\sqrt c\,e_3-\sqrt a\,e_{13})^{\mathsf T}}{a+c},\\
K_2&=\frac{(\sqrt b\,e_0-e_2)(\sqrt b\,e_0-e_2)^{\mathsf T}}{1+b},\\
K_3&=\frac{(\sqrt a\,e_0-e_3)(\sqrt a\,e_0-e_3)^{\mathsf T}}{1+a}
+\frac{(\sqrt c\,e_1-\sqrt a\,e_{13})
(\sqrt c\,e_1-\sqrt a\,e_{13})^{\mathsf T}}{a+c}.
\end{aligned}
\tag{4.2}
$$

They are orthogonal projections annihilating $\psi$. Define
$H_\omega=\sum_i\omega_iK_i$ and
$\gamma(\omega)=\lambda_{\min}(H_\omega|_{\psi^\perp})$.
All phase coordinates in this optimization are real.

**Definition 4.1 (Square-sector and center-overlap parameters).** Set

$$
U=ac+2c+a,\qquad
d=\frac1{1+a}+\frac c{a+c}=\frac U{(1+a)(a+c)},\qquad
q=2-d=\frac{aT}{(1+a)(a+c)}.
\tag{4.3}
$$

Thus $0<d,q<2$. Define positive coefficients summing to one by

$$
C_0=\frac Z{T(1+b)},\qquad
C_1=\frac{2b(a+c)^2}{TU(1+b)},\qquad
C_2=\frac{acb}{U(1+b)}.
\tag{4.4}
$$

For $0<t<q$, write

$$
F(t)=\frac{C_0}t-\frac{C_1}{q-t}-\frac{C_2}{2-t},
\qquad
R(t)=\sqrt{\frac{qC_1}{2(q-t)^2}+\frac{C_2}{(2-t)^2}}.
\tag{4.5}
$$

Let $t_0\in(0,q)$ be the unique zero of $F$. Let
$\widehat t\in(0,t_0)$ be the unique solution of $F(t)=R(t)$,
and put $t_*=\min\{\widehat t,d\}$.

These parameters have exact algebraic specifications. With
$B=q+2C_0+(2-q)C_1$,

$$
N(t)=t^2-Bt+2qC_0,\qquad
F(t)=\frac{N(t)}{t(q-t)(2-t)}.
\tag{4.6}
$$

Since $N(0)>0$ and $N(q)=-q(2-q)C_1<0$,
$t_0$ is its smaller root. The selected $\widehat t$ is the
unique root in $(0,t_0)$ of

$$
2N(t)^2-t^2\bigl[qC_1(2-t)^2+2C_2(q-t)^2\bigr]=0.
\tag{4.7}
$$

Indeed $F$ is strictly decreasing and $R$ strictly increasing
there, with $F-R$ positive near zero and negative at $t_0$.
The interval excludes roots created by squaring.

### 4.2. The complete finite positive design

**Theorem 4.2 (Joint-weight optimum and branch classification).**
For every $a,b,c>0$, the unique globally optimal distribution is

$$
\boxed{
\omega^*=\frac{(F_*,1,F_*)}{1+2F_*},\qquad
\gamma^*=\frac{t_*F_*}{1+2F_*},\qquad F_*=F(t_*).
}
\tag{4.8}
$$

If $\widehat t<d$, the gap is a simple reflection-even mode.
If $\widehat t=d$, the reflection-even and reflection-odd modes
meet, while an even rank-one real certificate still suffices.
If $\widehat t>d$, the optimal gap has exactly those two active
modes and admits a rank-two real certificate.

Proof. Put $e_+=(e_1+e_3)/\sqrt2$ and
$o=(e_1-e_3)/\sqrt2$. Define

$$
\begin{aligned}
g&=\frac{e_0+\sqrt{2a}\,e_++\sqrt c\,e_{13}}{\sqrt T},\\
h&=\frac{\sqrt2(a+c)e_0+\sqrt a(c-1)e_+
-\sqrt{2c}(1+a)e_{13}}{\sqrt{TU}},\\
k&=\sqrt{\frac{ac}U}e_0-\sqrt{\frac{2c}U}e_+
+\sqrt{\frac aU}e_{13},\\
u&=\frac{\sqrt b\,g-\sqrt T\,e_2}{\sqrt Z}.
\end{aligned}
\tag{4.9}
$$

Then $(\psi,u,h,k,o)$ is orthonormal and
$\psi=(\sqrt T\,g+\sqrt b\,e_2)/\sqrt Z$. Direct substitution
in (4.2), with $A=K_1+K_3$ and $\Delta=K_1-K_3$, gives

$$
A|_{\psi^\perp}=\operatorname{diag}(0,q,2,d)
\quad\text{in the order }(u,h,k,o),
\tag{4.10}
$$

$$
\Delta u=\Delta k=0,\qquad
\Delta h=-\sqrt{dq}\,o,\qquad
\Delta o=-\sqrt{dq}\,h,
\tag{4.11}
$$

$$
K_2=ww^{\mathsf T},\qquad
w=\sqrt{C_0}\,u+\sqrt{C_1}\,h+\sqrt{C_2}\,k.
\tag{4.12}
$$

Thus positive symmetric weights $(x,y,x)$ give the odd
eigenvalue $dx$ and the even matrix

$$
M(x)=\operatorname{diag}(0,qx,2x)+y\,CC^{\mathsf T},
\qquad C=(\sqrt{C_0},\sqrt{C_1},\sqrt{C_2})^{\mathsf T}.
\tag{4.13}
$$

Its strictly increasing secular function has one root in each
of $(0,qx)$, $(qx,2x)$ and $(2x,\infty)$, by the same pole
argument as §4.2. In particular the lowest even eigenvalue is
simple. Writing it as $xt$, its secular equation gives

$$
x=\frac{F(t)}{1+2F(t)},\qquad
y=\frac1{1+2F(t)},\qquad
\gamma(x)=x\min\{t,d\}.
\tag{4.14}
$$

The interval $0<t<t_0$ parameterizes all $0<x<1/2$.
The even branch $tF(t)/(1+2F(t))$ has derivative with sign
$F(t)-R(t)$, since its numerator is

$$
2F(t)^2-\frac{qC_1}{(q-t)^2}-\frac{2C_2}{(2-t)^2}
=2(F(t)-R(t))(F(t)+R(t)).
\tag{4.15}
$$

It increases until $\widehat t$ and decreases afterward.
Where $t>d$, the odd branch is $dF(t)/(1+2F(t))$,
strictly decreasing in $t$. Therefore the unique symmetric
maximizer is $t_*=\min\{\widehat t,d\}$.

For global certificates, use the even vector

$$
v=\frac{\sqrt{C_0}}{t_*}u
-\frac{\sqrt{C_1}}{q-t_*}h
-\frac{\sqrt{C_2}}{2-t_*}k,\qquad
L=v^{\mathsf T}v,\qquad \bar v=v/\sqrt L.
\tag{4.16}
$$

It satisfies $H_{\omega^*}v=\gamma^*v$.
Its normalized endpoint and center energies are

$$
E=\bar v^{\mathsf T}K_1\bar v
=\bar v^{\mathsf T}K_3\bar v=\frac{R(t_*)^2}L,\qquad
G=\bar v^{\mathsf T}K_2\bar v=\frac{F_*^2}L.
\tag{4.17}
$$

If $t_*=\widehat t$, then $E=G=\gamma^*$ and
$Y_*=\bar v\bar v^{\mathsf T}$ supplies the common Rayleigh
upper bound for all distributions as in (3.20).

If $t_*=d<\widehat t$, then $G>E$. The odd vector has
site energies $(d/2,0,d/2)$. Define

$$
\eta=\frac d{d+2(G-E)}\in(0,1),\qquad
Y_*=\eta\bar v\bar v^{\mathsf T}+(1-\eta)oo^{\mathsf T}.
\tag{4.18}
$$

This is positive semidefinite, has trace one, and annihilates
$\psi$. The eigenvector identity gives
$\gamma^*=2xE+yG=dx$ and $x/y=F_*$, hence
$G=F_*(d-2E)$ and

$$
\eta G=\frac{dF_*}{1+2F_*}=\gamma^*,\qquad
\operatorname{Tr}(Y_*K_i)=\gamma^*\quad(i=1,2,3).
\tag{4.19}
$$

For every distribution, its smallest eigenvalue is at most the
trace against this same trace-one certificate. Thus
$\gamma(\omega)\le\operatorname{Tr}(Y_*H_\omega)=\gamma^*$.
The candidate attains the bound by the even and odd spectra.

For uniqueness, an optimal distribution makes
$H_\omega-\gamma^*(I-\psi\psi^{\mathsf T})$ positive
semidefinite. Its zero trace against $Y_*$ forces
$H_\omega v=\gamma^*v$; the coefficient of the even vector in
the certificate is positive in both cases. Write
$x=(\omega_1+\omega_3)/2$ and
$\delta=(\omega_1-\omega_3)/2$. Its odd component is
$-\delta\sqrt{dq}\,v_h o$. Since
$v_h=-\sqrt{C_1}/(q-t_*)\ne0$, $\delta=0$.
The $u$ coordinate fixes
$(1-2x)F_*=\gamma^*/t_*$, and therefore fixes the candidate
weights. Every zero-weight boundary disconnects the positive
legal graph, so its gap is zero. $\square$

The crossing branch can be selected without solving an eigenvalue
problem. It occurs precisely when

$$
d<q,\qquad F(d)>0,\qquad F(d)>R(d).
\tag{4.20}
$$

Equality in the last comparison is the meeting surface.
If $d\ge q$, or $F(d)\le0$ when $d<q$, the crossing branch
is absent. For rational parameters all comparisons in (4.20)
are rational after squaring the last one under $F(d)>0$.

The general spectral certificate mechanism retains the ownership
documented in [DG3]. The result here concerns the explicit
three-parameter projectors (4.2), their two sectors, selected
root and all-weight equality conditions.

### 4.3. Real certificate rank and sampling conditions

**Theorem 4.3 (Real rank and the exact sampling tests).**
In the strict crossing branch of (4.20), no real rank-one
optimal spectral certificate exists. A complex Hermitian
rank-one matrix can encode the same two real active directions.
Every finite positive law satisfies $F_*>1/2$, hence
$1/4<\omega_1^*=\omega_3^*<1/2$ and $0<\omega_2^*<1/2$.
For every branch, the center has more samples than either
endpoint exactly when $F_*<1$. The entire strict interval
pattern (3.22) holds exactly when $1/2<F_*<1$.

Proof. In the strict crossing branch the minimum eigenspace is
exactly the real span of $\bar v,o$, by the secular intervals.
Any optimal real certificate is supported there. A real unit
vector in it is $z=\alpha\bar v+\beta o$. Its endpoint-energy
difference is

$$
z^{\mathsf T}(K_1-K_3)z
=-2\alpha\beta\sqrt{dq}\,\bar v_h.
\tag{4.21}
$$

The coefficients $\sqrt{dq}$ and $\bar v_h$ are nonzero.
Since all three optimal site weights are positive, an optimal
certificate must have all three site energies equal. Thus
$\alpha\beta=0$. The pure odd vector has center energy zero
and endpoint energy $d/2>0$. The pure even vector has
$G>E$. Neither gives an optimal rank-one real certificate.

On the complexified space, instead set
$z_{\mathbb C}=\sqrt\eta\,\bar v+i\sqrt{1-\eta}\,o$.
It has norm one, and each real symmetric $K_i$ satisfies

$$
z_{\mathbb C}^\dagger K_i z_{\mathbb C}
=\eta\bar v^{\mathsf T}K_i\bar v+(1-\eta)o^{\mathsf T}K_i o
=\gamma^*.
\tag{4.22}
$$

The imaginary cross terms cancel. This is a complex rank-one
certificate, whose real part is (4.18); it packages two real
phase directions and is not one real phase perturbation.

At the even stationary root, put $f=F(\widehat t)$.
Using $C_0+C_1+C_2=1$ and $f^2=R(\widehat t)^2$ gives

$$
(2f-1)((2-\widehat t)f+1)
=\frac{q(2-q)C_1}{(q-\widehat t)^2}>0.
\tag{4.22a}
$$

The second factor is positive because $0<\widehat t<q<2$.
Therefore $f>1/2$. Since $t_*\le\widehat t$ and $F$ is
decreasing, $F_*\ge f>1/2$.

Finally (4.8) gives
$y>x\iff1>F_*$,
$x>1/4\iff F_*>1/2$,
$x<1/3\iff F_*<1$, and
$y<1/2\iff F_*>1/2$. These are the stated necessary and
sufficient tests. $\square$

Thus only the center-versus-endpoint ordering can fail in the
older interval pattern; its endpoint lower bound survives every
finite positive joint weight.

Thus rank assertions require the coefficient field and parameter
space. Neither certificate rank counts quantum memory dimension,
independent preparations or physical particles.

### 4.4. A fully positive rational counterexample to the center premium

**Theorem 4.4 (A two-direction optimum with a smaller center budget).**
For the actual law

$$
p=\frac{(1,9,1,9,1)}{21},
\tag{4.23}
$$

the unique optimum is

$$
\boxed{
\omega^*=(75/182,\ 16/91,\ 75/182),\qquad
\gamma^*=15/182.
}
\tag{4.24}
$$

In particular the center weight is smaller than either endpoint
weight, although every occupation probability is positive.

Proof. Here $a=9,b=c=1$, so
$d=1/5$, $q=9/5$ and
$(C_0,C_1,C_2)=(21/40,1/4,9/40)$.
At $t=d$,

$$
F(d)=75/32,\qquad
R(d)^2=725/4608,\qquad F(d)>R(d).
\tag{4.25}
$$

Thus (4.20) holds and (4.8) gives (4.24).

There is also an entirely rational primal and dual certificate.
Use the unnormalized vectors

$$
\psi_0=(1,3,1,3,1)^{\mathsf T},\quad
v=(-1,8/3,-16,8/3,1)^{\mathsf T},\quad
o_0=(0,1,0,-1,0)^{\mathsf T}.
\tag{4.26}
$$

Then $\psi=\psi_0/\sqrt{21}$,
$v\perp\psi_0$, $o_0\perp\psi_0$, $v\perp o_0$,
$v^{\mathsf T}v=2450/9$ and $o_0^{\mathsf T}o_0=2$.
For the candidate $H$,

$$
Hv=(15/182)v,\qquad Ho_0=(15/182)o_0.
\tag{4.27}
$$

Set

$$
Y=\frac1{1365}vv^{\mathsf T}
+\frac{281}{702}o_0o_0^{\mathsf T}.
\tag{4.28}
$$

It is positive semidefinite, has trace one, annihilates $\psi_0$
and has $\operatorname{Tr}(YK_i)=15/182$ for every site.
Its normalized even weight is $70/351$, with the remaining
$281/351$ on the odd direction.

An explicit primal factorization is

$$
H-\frac{15}{182}\left(I-\frac{\psi_0\psi_0^{\mathsf T}}{21}\right)
=\frac{957}{1274}rr^{\mathsf T}
+\frac{4335}{232232}ss^{\mathsf T},
\tag{4.29}
$$

$$
r=(1,-95/638,-107/957,-95/638,5/957)^{\mathsf T},\qquad
s=(0,1,-2/51,1,-304/51)^{\mathsf T}.
\tag{4.30}
$$

Both coefficients are positive. The factorization proves the
primal lower bound, while (4.28) proves the all-weight upper
bound. Theorem 4.2 supplies uniqueness. $\square$

### 4.5. The pair determinant and an unchanged-marginal comparison

For the reflected law write
$X=p_1+p_{13}=p_3+p_{13}$, $z=p_2$ and $\kappa=p_{13}$.
Its pair determinant and unconditional covariance are different:

$$
\Delta=p_0p_{13}-p_1p_3
=\frac{c-a^2}{Z^2}
=(1-z)\kappa-X^2,\qquad
\operatorname{Cov}_p(n_1,n_3)=\kappa-X^2=\Delta+z\kappa.
\tag{4.31}
$$

The determinant is the same diagonal quantity used in the
conserved two-copy exchange of
[Circulation and Control, §24.4][CC4], with its $Z$ coordinate
mapped to $z$ here. This parameter identification does not identify
the two-copy exchange with one-copy site readout.

Directly from (4.3),

$$
d-1=
\frac{\Delta}{(p_0+p_1)(p_1+p_{13})}.
\tag{4.32}
$$

Thus the sign of the conditional endpoint relation determines
which square-sector eigenvalue is smaller. It does not by itself
select the final active gap: the center-overlap coefficients and
the comparison (4.20) are still required.

At fixed $X,z$, with $0<X<1-z$, the positive occupation fiber is

$$
p_\kappa=(1-2X-z+\kappa,\ X-\kappa,\ z,\ X-\kappa,\ \kappa),
\quad
\max\{0,2X+z-1\}<\kappa<X.
\tag{4.33}
$$

The threshold $\kappa_0=X^2/(1-z)$ lies strictly inside this
interval. Indeed $\kappa_0<X$,
$\kappa_0>0$, and

$$
\kappa_0-(2X+z-1)=\frac{(X-(1-z))^2}{1-z}>0.
\tag{4.34}
$$

Consequently identical endpoint and center means permit both
signs of $\Delta$. For example (4.23) and

$$
p'=(5,5,1,5,5)/21
\tag{4.35}
$$

share $X=10/21$ and $z=1/21$, but have
$\kappa=1/21$ and $5/21$. The second is the activity law
$a=1,b=1/5,c=1$, so its optimal center weight exceeds either
endpoint by Theorem 3.3; the first has the opposite strict
ordering by Theorem 4.4. The common marginal readings therefore
do not determine the optimal site distribution.

The pair weight can be interpreted conditionally as
$c/a^2=e^{-\beta J}$ after supplying a diagonal Gibbs Hamiltonian
with inverse temperature $\beta>0$. No temperature, physical
coupling, apparatus or energy scale is supplied by the probability
law alone. In particular $\Delta$, $\kappa$ and the sampling gap
are not complex coherence or physical energy.

The entire chapter concerns positive finite laws and real
reference-phase directions within the fixed recorded-site menu.
Zero-support restriction, arbitrary quantum measurements,
longer-chain locality and physical preparation require separate
arguments.

[CC4]: AURIC_FIB_ATOM_CIRCULATION_CONTROL_KL_ACTION_AND_TORIC_RELATIONS.md

### 4.6. Distinct thresholds for active sectors and the center premium

**Theorem 4.5 (Explicit negative-determinant thresholds).**
Fix $a,c>0$ with $c<a^2$. Define

$$
B=\frac{2(a+c)^2}{TU},\qquad C=\frac{ac}{U},\qquad
\ell=\frac{c(1+a)^2}{(a^2-c)T},
\tag{4.36}
$$

$$
J_d=\frac{qB}{2(q-d)^2}+\frac{C}{(2-d)^2},\qquad
s=d^2J_d,
\tag{4.37}
$$

$$
b_{\mathrm{act}}
=\frac{2}{2\ell+s+\sqrt{s^2+4s(\ell+1)}},\qquad
b_{\mathrm{prem}}=\frac{1-d}{\ell+d}.
\tag{4.38}
$$

Then $0<b_{\mathrm{prem}}<b_{\mathrm{act}}$.
For $b<b_{\mathrm{act}}$ the strict even--odd crossing is
active; at equality the modes meet; for $b>b_{\mathrm{act}}$
only the even mode is active. Independently, the center has
less, equal or more weight than each endpoint according as
$b<b_{\mathrm{prem}}$, $b=b_{\mathrm{prem}}$ or
$b>b_{\mathrm{prem}}$.

Proof. Here $0<d<1<q$, and substitution into (4.5) gives

$$
F(d)=\frac{1-\ell b}{d(1+b)},\qquad
R(d)^2=\frac{b}{1+b}J_d.
\tag{4.39}
$$

The first quantity decreases strictly from $1/d>0$ and
vanishes at $b=1/\ell$; the second increases strictly from
zero. Thus their positive square roots meet exactly once
in $(0,1/\ell)$. The equation is
$(1-\ell b)^2=sb(1+b)$, whose selected root is (4.38).
The branch test (4.20) proves the active-sector statements.

At the even stationary root, put $f=F(\widehat t)$.
The normalization and stationary equation also give

$$
\frac{2(2-q)C_2}{(2-\widehat t)^2}
=1-\widehat t f-2(q-\widehat t)f^2>0.
\tag{4.40}
$$

If $f\ge1$ and $q\ge1$, the right side is at most
$1-2q+\widehat t<1-q\le0$, a contradiction. Hence the
even stationary branch has $f<1$ throughout $q\ge1$.
For $c<a^2$, monotonicity of $F$ therefore gives
$F_*<1\iff F(d)<1$. Solving (4.39) at one gives
$b_{\mathrm{prem}}$. At that value $F(d)=1>f$, so
$d<\widehat t$ and $F(d)>R(d)$; it lies strictly below
$b_{\mathrm{act}}$. Theorem 4.3 proves the ordering.
For $c=a^2$, $q=d=1$ and only the even stationary mode is
active, so (4.40) recovers the center premium for all
$b>0$. $\square$

The determinant-zero surface and the active-sector surface
are different. In particular a negative determinant permits
a crossing but does not force it; the center can have a
premium within the crossing branch itself.

For all signs of the determinant there is also a scalar
necessary and sufficient premium test. Let $t_1\in(0,t_0)$
be the unique solution of $F(t_1)=1$, selected by the cubic
$N(t_1)=t_1(q-t_1)(2-t_1)$. Then

$$
F_*<1\iff t_1<d\ \text{ and }\ R(t_1)<1.
\tag{4.41}
$$

Indeed $F_*<1\iff t_*>t_1$, and
$\widehat t>t_1\iff F(t_1)>R(t_1)$ by strict monotonicity.
This test does not treat determinant sign as a substitute
for the center-overlap coefficients.

### 4.7. Crossing the active surface inside one marginal fiber

**Proposition 4.6 (A fixed-marginal active-sector crossing).**
At $X=9/16$ and $z=1/28$, three strictly positive laws in
the same occupation fiber have the following exact data:

| $\kappa$ | $(a,b,c)$ | $d$ | $F(d)$ | $R(d)^2$ | Active sector |
| --- | --- | --- | --- | --- | --- |
| $1/4$ | $(7/2,2/5,14/5)$ | $2/3$ | $5/6$ | $1/4$ | Strict crossing |
| $9/32$ | $(7/3,8/27,7/3)$ | $4/5$ | $2/3$ | $4/9$ | Meeting surface |
| $5/16$ | $(28/17,4/17,35/17)$ | $14/15$ | $10/63$ | $265/96$ | Even only |

The conditional-independence point of this same fiber is
$\kappa_0=21/64>5/16$.

Proof. Reconstruct the parameters of each actual law by

$$
p_0=1-z-2X+\kappa,\qquad
a=\frac{X-\kappa}{p_0},\quad
b=\frac z{p_0},\quad c=\frac\kappa{p_0}.
\tag{4.42}
$$

All five entries are positive. Substitution in
(4.3)--(4.5) gives the displayed fractions, and (4.20)
selects the three sectors. Equation (4.31) gives
$\kappa_0=X^2/(1-z)=21/64$. Thus the active meeting surface
can be crossed before the determinant changes sign.
All spectral coefficients change with the actual law in
(4.42); none is held fixed while only $\kappa$ is replaced.
$\square$

### 4.8. A disappearing center and two different boundary problems

**Proposition 4.7 (Positive-support limit versus restricted support).**
Fix $a,c>0$ and put $m=\min\{d,q\}=1-|d-1|>0$.
As $b\downarrow0$ through positive laws,

$$
\omega^*\longrightarrow\frac{(1,m,1)}{2+m},\qquad
\gamma^*\longrightarrow\frac m{2+m}.
\tag{4.43}
$$

If the zero-probability center phase is first removed and
the experiment is optimized on the remaining four-state
support, $(1/2,0,1/2)$ is optimal with gap $m/2$.

Proof. In the five-dimensional limit, $u\to-e_2$,
$C_0\to1$ and $C_1,C_2\to0$. The symmetric spectrum on
the complement of the ground ray becomes
$\{y,qx,2x,dx\}$, so its minimum is $\min\{y,mx\}$.
With $y=1-2x$ the unique symmetric maximizer satisfies
$y=mx$, giving (4.43). Continuity of the finite matrices
and eigenvalues is uniform over the compact weight
simplex; their maxima therefore converge to this value.
The finite positive maximizers are symmetric by Theorem
4.2, so their limit is the stated symmetric maximizer.

On restricted four-state support, $K_2$ vanishes. Reflection
averaging preserves total endpoint budget and cannot lower
the minimum eigenvalue. With that budget $s\le1$, the
best symmetric allocation has gap $sm/2$, attained at
$s=1$. This gives the restricted-support result. Since
$m>0$, $m/(2+m)<m/2$. The difference comes from retaining
or deleting a phase direction, rather than from changing
the meaning of one sample. $\square$


[ParentReadout]: FIB_LEGAL_EDGE_LOAD_INTRINSIC_NULL_KERNEL_DUAL_RESIDUAL_AND_PRESENTATION_OBSTRUCTION.md
[BC8]: AURIC_FIB_ATOM_PYRAMID_BOUNDARY_CALCULUS.md

## 追加锚（本行以下为增补区）

## 5. Full pure-state information and the five-state spectral complement

### 5.1. The actual tangent space and the same preparation budget

**Definition 5.1 (Probability and phase directions).** Fix a finite
$n\ge1$, a strictly positive normalized law $p$ on $B_n$, and the
supplied real reference $\psi=(\sqrt{p_s})_{s\in B_n}$.
Put $V=\psi^\perp\cap\mathbb R^{B_n}$. For $u,v\in V$, use the
normalized pure-state path

$$
z(t)=\frac{\psi+t(u+iv)}{\|\psi+t(u+iv)\|}.
\tag{5.1}
$$

Its derivative at zero is $u+iv$. These are all horizontal
pure-state directions, rather than only derivatives within the
activity family. In the negative-phase convention,
$\dot p_s=2\psi_su_s$ and $\dot\theta_s=-v_s/\psi_s$.
Thus normalization and the common-phase gauge are respectively
$\sum_s\dot p_s=0$ and $\sum_sp_s\dot\theta_s=0$.

Keep the complete recorded-site quadrature experiment of
Parent/Readout Chapter 8 fixed at this reference. For a legal
site-$i$ pair $\{s,t\}$ its phase projection is

$$
K_{st}=\frac{(\psi_t e_s-\psi_s e_t)
(\psi_t e_s-\psi_s e_t)^{\mathsf T}}{p_s+p_t},\qquad
K_i=\sum_{\{s,t\}\text{ at }i}K_{st}.
\tag{5.2}
$$

At a fixed site the pairs are disjoint, and blocked words remain
separate outcomes. Let $\omega_i\ge0$, $\sum_i\omega_i=1$ and
$H_\omega=\sum_i\omega_iK_i$. A sample uses a quadrature site
with total probability $r\in[0,1]$, conditional probabilities
$\omega_i$, or a full mode-basis measurement with probability
$1-r$. All setting labels and outputs are retained. The
probabilities $r,\omega_i$ and the measurement effects do not
change along (5.1).

Write $B_\omega=H_\omega|_V$ and
$\gamma(\omega)=\lambda_{\min}(B_\omega)$. Define the full local
information ratio by

$$
\Gamma(r,\omega)=\inf_{(u,v)\ne(0,0)}
\frac{J_{r,\omega}(u,v)}{4(\|u\|^2+\|v\|^2)}.
\tag{5.3}
$$

The denominator is the pure-state QFI at the supplied reference.
The ratio concerns first-order information, not an assertion of
global identification or finite-sample minimax risk. Supplying
the reference and coherent controls is an assumption separate
from the sample count.

### 5.2. Pointwise transfer without reflection symmetry

**Theorem 5.2 (All positive five-state laws).** Take $n=3$ with
the order $(0,1,2,3,13)$, any strictly positive law $p$, every site
distribution $\omega$, and every $0\le r\le1$. Then

$$
\boxed{\Gamma(r,\omega)=r\gamma(\omega).}
\tag{5.4}
$$

Consequently the full probability-and-phase optimum has the same
site distributions as the phase-only optimum, and every overall
optimum in the enlarged menu has $r=1$. For the reflected laws
of Theorem 4.2, its explicit unique site distribution is also
the unique full-tangent optimum. Reflection symmetry is not
needed for the pointwise identity (5.4).

Proof. First compute the information of the actual experiment.
On a pair set $S=p_s+p_t$,
$\alpha=\psi_su_s+\psi_tu_t$ and
$\beta=\psi_sv_t-\psi_tv_s$. At the reference the two
probabilities are $S/2$, and their derivatives are
$\alpha+\beta$ and $\alpha-\beta$, up to the fixed outcome-sign
convention. Their Fisher contributions add to

$$
\frac{(\alpha+\beta)^2+(\alpha-\beta)^2}{S/2}
=\frac{4(\alpha^2+\beta^2)}S.
\tag{5.5}
$$

The normalized vectors
$(\psi_se_s+\psi_te_t)/\sqrt S$ and
$(\psi_te_s-\psi_se_t)/\sqrt S$ are orthonormal on the pair.
A blocked word contributes $4u_s^2$ and no phase term.
The mode-basis setting contributes $4\|u\|^2$.
Summing pairs, blocked outcomes and recorded settings gives

$$
J_{r,\omega}(u,v)
=4\bigl[u^{\mathsf T}(I-rH_\omega)u
+r v^{\mathsf T}H_\omega v\bigr].
\tag{5.6}
$$

Polarization therefore gives the complete reference matrices
in orthonormal horizontal coordinates:

$$
F_{r,\omega}=4\begin{pmatrix}I_V-rB_\omega&0\\0&rB_\omega\end{pmatrix},
\qquad Q=4I_{2\dim V}.
\tag{5.7}
$$

Every $K_i$ is a projection annihilating $\psi$, so
$0\preceq B_\omega\preceq I_V$. Hence

$$
\Gamma(r,\omega)=
\min\{r\lambda_{\min}(B_\omega),
1-r\lambda_{\max}(B_\omega)\}.
\tag{5.8}
$$

The paired calculation is an application of established
rank-one measurement information algebra: see Li--Ferrie--
Gross--Kalev--Caves, equations (12), (15)--(16) [FSIC5]. Its
specialization here retains the actual legal blocks, blocked
outcomes and setting budget. The block diagonal form uses the
real calibrated reference and opposite quadratures; rank one
alone does not set arbitrary classical cross blocks to zero.

It remains to prove the five-state spectral inequality. On
the four square states, $K_1$ and $K_3$ are rank-two orthogonal
projections. Their common kernel is the one-dimensional ray of
the restricted square-root law: their four pair equations
connect the square. The sum of their ranges has dimension
three, so their common range has dimension one. These two
common spaces are orthogonal. Their two-dimensional orthogonal
complement is invariant under both projections, each of rank
one there.

Put $s=\omega_1+\omega_3$. On $V$, the eigenvalues of
$A=\omega_1K_1+\omega_3K_3$ are

$$
0,\lambda_-,\lambda_+,s,\qquad
0\le\lambda_-\le\lambda_+\le s,\qquad
\lambda_-+\lambda_+=s.
\tag{5.9}
$$

The zero direction comes from the center state and the common
square kernel after removing $\psi$. The common range has
eigenvalue $s$. The remaining block has trace $s$ and is
bounded above by $sI$, proving (5.9), including zero weights.

Write $\mu_1\le\cdots\le\mu_4$ for the eigenvalues of
$B_\omega=A+\omega_2K_2|_V$. Positivity of the added rank-one
projection and the variational eigenvalue principle give
$\mu_2\ge\lambda_-$ and $\mu_3\ge\lambda_+$.
Meanwhile

$$
\sum_j\mu_j=2s+\omega_2=1+s,
\qquad
\mu_1+\mu_4
=1+s-(\mu_2+\mu_3)\le1.
\tag{5.10}
$$

Thus $1-r\mu_4\ge r\mu_1$ for $0\le r\le1$, and (5.8)
is (5.4). The connected legal graph and any strictly positive
site distribution give a positive phase gap. Its maximum
$\gamma^*>0$ exists by continuity on the compact simplex.
Equation (5.4) gives $\max_\omega\Gamma(r,\omega)=r\gamma^*$;
therefore every overall optimum has $r=1$ and a phase-optimal
site distribution. Apply Theorem 4.2 for reflected laws.
$\square$

The argument uses the square-plus-center projection geometry.
It neither assumes independent endpoint occupations nor
identifies a mixed-state tangent space with $V\oplus iV$.

### 5.3. The same conjugate information budget

For any real unit $h\in V$, the two conjugate tangent
directions $h$ and $ih$ have normalized information
$1-rh^{\mathsf T}B_\omega h$ and
$rh^{\mathsf T}B_\omega h$. Their sum is one. Restricting
to the supplied relation family of Parent/Readout §9.10,
with $h_s=d_s/(\sqrt{\bar p_s}\sqrt{I_0})$, therefore gives

$$
\frac{F_{\kappa\kappa}}{I_0}=1-t,\qquad
\frac{I_0F_{\chi\chi}}4=t,\qquad
F_{\kappa\chi}=0,\qquad t=rh^{\mathsf T}B_\omega h.
\tag{5.11}
$$

The local model's vanishing classical cross term does not
remove its imaginary horizontal Gram pairing. Equation
(5.11) lies inside the arbitrary-measurement directional
budget already proved in Parent/Readout §§9.11 and 10.7.
It does not give both individual QFI limits simultaneously.

Likewise the $2\dim V$ generalized eigenvalues in (5.7)
sum to $\dim V$: each eigenvalue of $rB_\omega$ is paired
with its complement. This consumes the existing pure-state
Fisher trace budget, rather than creating a new uncertainty
principle. The unrestricted local half-QFI measurement of
[FSIC5] and Parent/Readout §10.9 uses additional calibrated
global operations. It is a different menu from the single-site
controls studied here. Parent/Readout §8.5 already records
the separate mixed-state observation kernel.

[FSIC5]: https://arxiv.org/abs/1507.06904v2

## 追加锚（本行以下为增补区）

## 6. A rare vacuum separates phase and full-tangent designs

### 6.1. Positive laws and the graph left after vacuum deletion

**Definition 6.1 (A supplied rare-vacuum law).** Fix a finite
$n\ge4$, let $0$ denote the empty word in $B_n$, and put
$M=|B_n|-1$. For $\epsilon>0$, define

$$
p_\epsilon(0)=\frac\epsilon{M+\epsilon},\qquad
p_\epsilon(s)=\frac1{M+\epsilon}\quad(s\ne0).
\tag{6.1}
$$

Use the pure reference $\psi_\epsilon=\sqrt{p_\epsilon}$ and
the same fixed quadrature settings, blocked-word outcomes,
recorded labels and preparation budget as Definition 5.1.
Write $\gamma_\epsilon(\omega)$ and
$\Gamma_\epsilon(r,\omega)$ for the corresponding ratios.
Let $G_n^\circ$ be the legal-toggle graph induced by the
nonempty words, and let $L_n^\circ$ be its unweighted
combinatorial Laplacian. Define

$$
g_n=\lambda_2\!\left(\frac1{2n}L_n^\circ\right),
\tag{6.2}
$$

with the eigenvalues ordered increasingly, including the
constant zero mode. The graph and $g_n$ are fixed before
letting $\epsilon$ tend to zero.

**Theorem 6.2 (Separation at every finite length at least four).**
For every site distribution $\omega$,

$$
\Gamma_\epsilon(1,\omega)
\le\frac{\epsilon(M-1)}{M(1+\epsilon)}.
\tag{6.3}
$$

For the uniform distribution $\bar\omega_i=1/n$,

$$
0<g_n\le1,\qquad
\gamma_\epsilon(\bar\omega)\longrightarrow g_n,
\qquad
\lambda_{\max}(B_{\bar\omega,\epsilon})
\longrightarrow1.
\tag{6.4}
$$

Consequently, for each fixed $0<r<1$ and all sufficiently
small positive $\epsilon$,

$$
\Gamma_\epsilon(r,\bar\omega)
>\sup_\omega\Gamma_\epsilon(1,\omega).
\tag{6.5}
$$

Thus a mode-basis setting can strictly improve the full
pure-state information criterion under the same preparation
budget. All compared laws have full support, and all
horizontal directions are retained.

Proof. Every site pairs the empty word with its singleton.
The vacuum diagonal entry of each $K_i$ is $1/(1+\epsilon)$,
and $H_\omega\psi_\epsilon=0$. Put

$$
u_\epsilon=(I-\psi_\epsilon\psi_\epsilon^{\mathsf T})e_0.
\tag{6.6}
$$

Then $u_\epsilon\in V_\epsilon$ and

$$
\|u_\epsilon\|^2=\frac M{M+\epsilon},\qquad
u_\epsilon^{\mathsf T}H_\omega u_\epsilon
=\frac1{1+\epsilon}.
\tag{6.7}
$$

The amplitude direction $(u_\epsilon,0)$ in (5.6), with
$r=1$, has information ratio

$$
\frac{u_\epsilon^{\mathsf T}(I-H_\omega)u_\epsilon}
{\|u_\epsilon\|^2}
=\frac{\epsilon(M-1)}{M(1+\epsilon)}.
\tag{6.8}
$$

This proves the uniform upper bound (6.3), independently
of the site allocation.

For uniform sites the finite matrices have the limit

$$
H_{\bar\omega,\epsilon}\longrightarrow
\begin{pmatrix}1&0\\0&L_n^\circ/(2n)\end{pmatrix},
\qquad
\psi_\epsilon\longrightarrow
\left(0,\frac{\mathbf1}{\sqrt M}\right).
\tag{6.9}
$$

Indeed each vacuum--singleton pair has matrix entries
$1/(1+\epsilon)$ at the vacuum,
$\epsilon/(1+\epsilon)$ at the singleton, and
$-\sqrt\epsilon/(1+\epsilon)$ off diagonal. Each pair of
nonempty words has equal probabilities and contributes
$(e_s-e_t)(e_s-e_t)^{\mathsf T}/(2n)$ to the uniform
operator. This proves (6.9) entry by entry.

The graph $G_n^\circ$ is connected. Delete occupied sites
from any nonempty independent set until a singleton is
reached, retaining at least one occupied site throughout.
Singletons $i,j$ with $|i-j|\ge2$ are connected by the
two-edge route $\{i\},\{i,j\},\{j\}$. The graph of these
singleton compatibilities is the complement of the path
$P_n$. Its first four vertices are connected by the edges
$\{1,3\},\{1,4\},\{2,4\}$, and every vertex $j\ge5$
is adjacent to vertex 1. Hence its connectivity holds for
every $n\ge4$.

Connectivity gives a simple constant kernel and a positive
finite $g_n$. Each $H_{\bar\omega,\epsilon}$ is a convex
combination of orthogonal projections, so it lies between
zero and identity; its limiting nonvacuum block does also.
Thus $g_n\le1$. At the limit the full operator has exactly
one zero mode, the limiting ground vector, while its
nonzero spectrum consists of the nonvacuum positive
spectrum and the vacuum eigenvalue 1. Continuity of the
ordered eigenvalues of these finite symmetric matrices
therefore proves (6.4).

For every positive $\epsilon$, (5.8) and the projection
contraction give

$$
\Gamma_\epsilon(r,\bar\omega)
\ge\min\{r\gamma_\epsilon(\bar\omega),1-r\}.
\tag{6.10}
$$

For sufficiently small $\epsilon$ this is at least
$\min\{rg_n/2,1-r\}>0$, whereas (6.3) tends to zero.
This proves (6.5). $\square$

The limiting graph is used to prove a bound for positive
laws. It does not replace the tangent space by a reduced
support space. In particular, the vacuum amplitude
direction (6.6) remains a tested direction in every
comparison. The result is for each fixed finite $n$;
it supplies no uniform lower bound as $n\to\infty$.

### 6.2. Short lengths and the activity-family boundary

**Proposition 6.3 (Exceptions and locality of the supplied law).**
Deleting the vacuum disconnects the legal-toggle graph at
$n=2$ and $n=3$. Every positive law at $n=2$ satisfies
$\Gamma(r,\omega)=r\gamma(\omega)$. At $n=1$ the sole quadrature setting has
$\gamma=1$ and $\Gamma(r)=\min\{r,1-r\}$, so mixing with
the mode basis improves the joint criterion by a different
mechanism. For $n\ge3$ and $\epsilon\ne1$, (6.1) is not
a single-site activity law
$p(s)\propto\prod_i\lambda_i^{s_i}$ on $B_n$.

Proof. At $n=2$ only two isolated singleton words remain
after deletion. At $n=3$ the center singleton is isolated,
while the endpoint singletons connect through their pair.
This prevents the positive $g_n$ argument of Theorem 6.2
at those lengths. Theorem 5.2 nevertheless treats every
positive law at $n=3$ directly.

At $n=2$ the two site projections each have rank one
and annihilate $\psi$. Their weighted sum on the
two-dimensional $V$ has trace one, so its two eigenvalues
$\gamma,\Lambda$ satisfy $\gamma+\Lambda=1$.
Equation (5.8) proves the stated identity for every $r$.

At $n=1$ the one legal pair spans the entire two-state
space. Its $K_1$ is identity on the one-dimensional $V$,
so (5.8) gives the asserted ratios.

For the activity claim, the singleton-to-vacuum ratios
would force $\lambda_i=1/\epsilon$ for every site. A legal
nonadjacent pair exists at $n\ge3$. Its actual ratio to
the vacuum is $1/\epsilon$, whereas the product formula
would give $1/\epsilon^2$. Equality requires
$\epsilon=1$. $\square$

Theorem 6.2 thus distinguishes general positive supplied
laws from a restricted local activity family. It does
not establish the same separation inside that family,
or supply a local preparation Hamiltonian for (6.1).

### 6.3. An exact positive eight-state comparison

**Proposition 6.4 (A rational length-four witness).** Order
the legal words as

$$
(0000,0001,0010,0100,0101,1000,1001,1010)
\tag{6.11}
$$

and take

$$
p=\frac{(1,100,100,100,100,100,100,100)}{701}.
\tag{6.12}
$$

For every quadrature site allocation,
$\Gamma(1,\omega)\le6/707$. Uniform conditional site
allocation with quadrature fraction $r=9/10$ satisfies

$$
\Gamma(9/10,\bar\omega)\ge\frac9{500}
>\frac6{707},\qquad
\frac9{500}-\frac6{707}=\frac{3363}{353500}.
\tag{6.13}
$$

Proof. Here $M=7$ and $\epsilon=1/100$, so (6.3) gives
$6/707$. For the uniform phase lower bound use indices
$0,\ldots,7$ in order (6.11). The site pair sets are

$$
\begin{aligned}
1 &: \{\{0,5\},\{1,6\},\{2,7\}\},\\
2 &: \{\{0,3\},\{1,4\}\},\\
3 &: \{\{0,2\},\{5,7\}\},\\
4 &: \{\{0,1\},\{3,4\},\{5,6\}\}.
\end{aligned}
\tag{6.14}
$$

For $D=\operatorname{diag}(\sqrt p)$ and $u=Df$, the
condition $u\perp\sqrt p$ is $\sum_sp_sf_s=0$, and

$$
\|u\|^2=\operatorname{Var}_p(f),\qquad
u^{\mathsf T}H_{\bar\omega}u
=\sum_{\{s,t\}\text{ legal}}c_{st}(f_s-f_t)^2,
\quad c_{st}=\frac{p_sp_t}{4(p_s+p_t)}.
\tag{6.15}
$$

Use the spanning tree whose long path is
$2\!-\!7\!-\!5\!-\!6\!-\!1\!-\!4\!-\!3$
and whose remaining leaf edge is $0\!-\!5$.
For each unordered pair $\{s,t\}$ let $P_{st}$ be its
unique tree path. The variance identity and Cauchy's
inequality along that path give

$$
\begin{aligned}
\operatorname{Var}_p(f)
&=\sum_{s<t}p_sp_t(f_s-f_t)^2\\
&\le\sum_{e\text{ in the tree}}L_e(\nabla_e f)^2,
\qquad
L_e=\sum_{s<t:e\in P_{st}}p_sp_t|P_{st}|.
\end{aligned}
\tag{6.16}
$$

The exact edge loads relative to (6.15) are

| Tree edge $e$ | $L_e/c_e$ |
|---|---:|
| $\{2,7\}$ | $24$ |
| $\{5,7\}$ | $40$ |
| $\{5,6\}$ | $33712/701$ |
| $\{1,6\}$ | $33696/701$ |
| $\{1,4\}$ | $28072/701$ |
| $\{3,4\}$ | $16840/701$ |
| $\{0,5\}$ | $8080/701$ |

These fractions follow by enumerating the 28 unordered
pairs in (6.16); their maximum is $33712/701<50$. All remaining
legal-edge energies are nonnegative. Consequently

$$
\operatorname{Var}_p(f)
\le50\,u^{\mathsf T}H_{\bar\omega}u,
\qquad\gamma(\bar\omega)\ge\frac{701}{33712}>\frac1{50}.
\tag{6.17}
$$

For $r=9/10$, the amplitude block $I-rB_{\bar\omega}$
is at least $I/10$, and the phase block
$rB_{\bar\omega}$ is at least $9I/500$.
Equation (5.8) and exact rational subtraction prove
(6.13). $\square$

The gain concerns the worst direction of the full
horizontal pure-state tangent at a supplied calibrated
reference. It neither makes the classical Fisher
matrix equal to QFI nor proves simultaneous attainment
of individual QFI limits. The comparison uses the same
number of preparations and changes the recorded setting
distribution; it supplies no finite-sample risk theorem,
hardware implementation or physical energy assignment.

### 6.4. The global sign fiber and the nearby indistinguishable ray

**Proposition 6.5 (No uniform identifiable neighborhood).**
For any positive law on $B_n$, the fixed menu of Definition
5.1 gives the same recorded distribution on all rays

$$
\psi^\sigma=\sum_{s\in B_n}\sigma_s\sqrt{p_s}\,e_s,
\qquad \sigma_s\in\{-1,1\}.
\tag{6.18}
$$

There are $2^{|B_n|-1}$ distinct rays in this displayed
family. For the law (6.1), flipping only the vacuum sign
gives a distinct ray with the same distribution, represented
at distance $2\sqrt{\epsilon/(M+\epsilon)}$ from the positive
reference. Thus no fixed positive-radius neighborhood of
these references is identifiable uniformly as
$\epsilon\downarrow0$, despite the positive limiting local
information ratio of Theorem 6.2.

Proof. On a pair the two quadrature probabilities at
(6.18) are

$$
\frac12\left|\sigma_s\sqrt{p_s}
\mathbin{\pm} i\sigma_t\sqrt{p_t}\right|^2
=\frac{p_s+p_t}{2}.
\tag{6.19}
$$

Mode-basis and blocked-word probabilities remain $p_s$.
Recorded setting probabilities are state-independent,
so the entire distribution is unchanged for every $r$
and $\omega$. Full support makes two sign vectors define
the same ray exactly when they differ by an overall sign,
giving the count. A vacuum-only flip changes precisely
one coordinate by $2\sqrt{p_\epsilon(0)}$; both normalized
states remain in the legal carrier. For any fixed radius
this distance is smaller than that radius at sufficiently
small positive $\epsilon$, while the two rays remain
distinct. This proves the nonuniform-neighborhood claim.
$\square$

This boundary concerns the fixed single-quadrature menu.
Parent/Readout Theorem 8.6 uses both real and imaginary
edge observations, which supply the missing sign-sensitive
data on connected support. Its pure-state propagation
result is not contradicted by (6.19). A local Fisher lower
bound at the calibrated reference does not itself supply
those additional observations.

**Attribution 6.6 (The specific increment and established tools).**
The full tangent Fisher algebra in Chapter 5 consumes
[FSIC5]. The five-state increment is the all-positive,
all-weight extremal-eigenvalue inequality (5.10) and its
complete optimizer transfer. The larger-state increment
is the fixed-menu rare-vacuum separation of Theorem 6.2
and its exact positive comparison (6.13). The elementary
connectivity and path inequalities inside these proofs
are supporting methods, not new graph or congestion
principles.

Huang--Preskill--Soleimanifar, [arXiv:2404.07281v1][HPS6],
equations (19)--(25) and Proposition 3, already use the
same heat-bath transition weights and diagonal
symmetrization in quantum-state certification. At level
one and zero reference phase, their support-restricted
transition operator corresponds to
$I-D^{-1}H_{\bar\omega}D$, with
$D=\operatorname{diag}(\sqrt p)$. Their Appendix D.2,
equation (42) and Proposition 12, gives the classical
length-weighted canonical-path gap bound and attributes
it to Sinclair. Equation (6.16) is the elementary
variance proof of that method for the selected tree;
the tree and its exact loads are the instance-specific
data.

Mao--Chen--Huang--Preskill--Zhou,
[arXiv:2608.01617v1][MCHPZ6], Appendix C, Definition S4,
Theorem S5 and equations (C.1)--(C.3), provide a close
multiparameter antecedent using the same heat-bath
operator. Their single-qubit setting is randomly chosen
from $X,Y,Z$, with $Z$ on the other qubits; their full
Fisher guarantee uses the chain's relaxation time.
That broader menu includes the real-edge observations
absent from (6.19). Its guarantee is not substituted
for the exact narrower-menu comparison here.

No literature priority is claimed for these specific
conclusions. In particular, (6.1) provides neither a
local activity realization nor an attainment statement
for the original finite-producer optimization problem.

[HPS6]: https://arxiv.org/abs/2404.07281v1
[MCHPZ6]: https://arxiv.org/abs/2608.01617v1

## 7. Activity laws retain the phase optimum beyond five states

### 7.1. The upper spectral edge and exclusion sectors

**Definition 7.1 (Activity and complementary operators).**
Fix $n\ge2$, positive activities $\lambda_i=a_i$ and the
law of (1.1), and a site distribution $\omega$. Use the
site projections of (5.2), and put

$$
\begin{aligned}
q_i&=\frac{\lambda_i}{1+\lambda_i},&
b_i&=\frac{\omega_i}{1+\lambda_i},&
\rho_i&=\mathbb E_p s_i,\\
Se_s&=(-1)^{|s|}e_s,&
C_{\lambda,\omega}&=I-SH_{\lambda,\omega}S,&
\delta&=\lambda_{\min}(C_{\lambda,\omega})=1-\Lambda(\omega).
\end{aligned}
\tag{7.1}
$$

Here $H_{\lambda,\omega}=\sum_i\omega_iK_i$ and
$\Lambda=\lambda_{\max}(H_{\lambda,\omega}|_V)$.
The zero ground mode does not change this maximum.
Let $\Pi_i^{\rm blocked}$ project onto legal words
with an occupied neighbor of $i$. For a physical path
edge $e=\{i,j\}$ define

$$
d_e=\frac{\omega_i+\omega_j-
\sqrt{(\omega_i-\omega_j)^2+4\omega_i\omega_jq_iq_j}}2,
\qquad D_{\mathcal M}=\sum_{e\in\mathcal M}d_e,
\tag{7.2}
$$

where $\mathcal M$ is a matching of the physical path.
This is an operator comparison on the same legal
carrier, with no additional measurement setting.

**Theorem 7.2 (Complement bound and arbitrary weights through length six).**
For every positive activity vector and every site
distribution,

$$
C_{\lambda,\omega}
=H_{\lambda^{-1},\omega}+\sum_i\omega_i\Pi_i^{\rm blocked},
\qquad \delta\ge D_{\mathcal M}
\quad\text{for every matching }\mathcal M.
\tag{7.3}
$$

At every length $2\le n\le6$ these operators satisfy

$$
\gamma(\omega)+\Lambda(\omega)\le1,
\qquad\Gamma(r,\omega)=r\gamma(\omega)
\quad(0\le r\le1).
\tag{7.4}
$$

Proof. On an oriented legal pair the activity-law
projection has the matrix

$$
K_i=\begin{pmatrix}
q_i&-\sqrt{q_i(1-q_i)}\\
-\sqrt{q_i(1-q_i)}&1-q_i
\end{pmatrix}.
\tag{7.5}
$$

The parity conjugation reverses the off-diagonal sign.
Its complement exchanges $q_i$ and $1-q_i$ and has
negative off-diagonal entries, giving the projection
for reciprocal activity. On a blocked singleton,
$K_i=0$ and its complement is identity. Since
$\sum_i\omega_i=1$, these pair and singleton
calculations prove the first identity in (7.3).

For an adjacent pair $\{i,j\}$ fix the complete
exterior word. When both sites are externally free,
the allowed pair states are $00,10,01$. The two unit
projector vectors have inner product $\sqrt{q_iq_j}$.
Their weighted sum has eigenvalues
$0,d_e,\omega_i+\omega_j-d_e$; its complementary
operator therefore has minimum $d_e$. When one site
is externally blocked, its complement contributes
its entire weight, and the other complement is
nonnegative. The minimum is at least $\omega_i$ or
$\omega_j$, respectively. When both are blocked,
the complement equals $(\omega_i+\omega_j)I$.
The expression (7.2) gives
$0\le d_e\le\min(\omega_i,\omega_j)$, so every
exterior sector satisfies

$$
\omega_i(I-SK_iS)+\omega_j(I-SK_jS)\succeq d_eI.
\tag{7.6}
$$

Sum over a matching and keep the nonnegative
unmatched terms. This proves the second part of (7.3).
In particular, if an adjacent pair has positive
weights then $d_e>0$, because $q_iq_j<1$.
The complementary operator has positive minimum
energy and is not a frustration-free zero-ground
operator.

If any $\omega_i=0$, the centered occupation
$s_i-\rho_i$ is nonconstant and is unchanged by
every remaining site update. Its tangent vector
$D(s_i-\rho_i)$ is killed by those projections.
Thus $\gamma=0$; since $H\preceq I$, the inequality
in (7.4) follows. It suffices to prove the result
when every weight is positive. Length two follows
from Proposition 6.3's trace calculation and length
three from Theorem 5.2's two-projection argument.

For lengths four through six, delete selected
exclusion edges, splitting the physical path into
blocks of lengths two or three. Write $\Omega_0$
for the enlarged legal carrier, $H_0$ for the block
operator with exactly the same activities and weights,
and $J:\mathbb R^{B_n}\to\mathbb R^{\Omega_0}$ for
the coordinate embedding. Then

$$
H_{\lambda,\omega}=J^{\mathsf T}H_0J-R,\qquad
R_{ss}=\sum_{\substack{i:\ s\to s\cup\{i\}\text{ legal in }\Omega_0\\
s\to s\cup\{i\}\text{ forbidden in }B_n}}\omega_iq_i\ge0.
\tag{7.7}
$$

Indeed, surviving off-diagonal toggles have the
identical activity odds (7.5). An insertion newly
forbidden by the restored exclusion contributes
only its $\omega_iq_i$ diagonal entry to the
compression, and this is precisely the subtracted
term. A removal of an occupied site remains legal.
Thus (7.7) accounts for every entry. The auxiliary
carrier is used only for comparison.

For block $j$, let $s_j$ be its total inherited
weight, $g_j$ its gap, and $\Lambda_j$ its maximum
eigenvalue. Scale the length-two or length-three
result by $s_j$ to obtain $\Lambda_j\le s_j-g_j$.
Put $D_0=\sum_jg_j$. The tensor-sum operator $H_0$
has maximum at most $\sum_j(s_j-g_j)=1-D_0$.
Choosing either a ground vector or a first-excited
vector independently in each of the $k$ blocks
gives $2^k$ orthogonal eigenvectors with energy
at most $D_0$.

Let $c_0=|\Omega_0|-|B_n|$, with eigenvalues indexed
in increasing order starting at 1. Compression
interlacing and $R\succeq0$ give

$$
\gamma(\omega)=\lambda_2(H_{\lambda,\omega})
\le\lambda_{c_0+2}(H_0),\qquad
\Lambda(\omega)\le\lambda_{\max}(H_0).
\tag{7.8}
$$

The required dimension counts are

| $n$ | Block lengths | $|\Omega_0|$ | $|B_n|$ | $c_0+2$ | $2^k$ |
|---|---|---:|---:|---:|---:|
| 4 | $2+2$ | 9 | 8 | 3 | 4 |
| 5 | $2+3$ | 15 | 13 | 4 | 4 |
| 6 | $2+2+2$ | 27 | 21 | 8 | 8 |

Thus $\gamma\le D_0$ and $\Lambda\le1-D_0$ in
all three cases. Equation (5.8) then yields (7.4).
$\square$

### 7.2. A certificate at every length

**Theorem 7.3 (Occupation certificate and uniform-site designs).**
For arbitrary positive activities and site weights,
put

$$
U=\min_i\frac{b_i}{1-\rho_i}.
\tag{7.9}
$$

Then $\gamma\le U$, and $U\le D_{\mathcal M}$
for any matching is sufficient for
$\gamma+\Lambda\le1$. At $n\ge4$, if every weight
is positive and there are two vertex-disjoint
adjacent pairs with equal endpoint weights within
each pair, then $\gamma+\Lambda<1$. Consequently,
uniform site weights satisfy $\gamma+\Lambda\le1$
at every length $n\ge2$, for arbitrary positive
activities.

Proof. Conditional on the complete exterior of
site $i$, the bit is either blocked and zero or
is Bernoulli with parameter $q_i$. If the exterior
is free with probability $t_i$, then
$\rho_i=t_iq_i$ and
$\mathbb E_p\operatorname{Var}(s_i\mid\text{exterior})
=t_iq_i(1-q_i)=\rho_i/(1+\lambda_i)$.
Only site $i$ changes the observable $s_i$.
Its Dirichlet energy and variance are therefore

$$
\mathcal E_\omega(s_i,s_i)=b_i\rho_i,
\qquad\operatorname{Var}_p(s_i)=\rho_i(1-\rho_i).
\tag{7.10}
$$

The Rayleigh quotient gives (7.9). The marginals
$\rho_i$ are those of the actual constrained law;
the independent Bernoulli parameters $q_i$ do not
replace them. Combine $\gamma\le U$ with (7.3)
to obtain the sufficient certificate.

For adjacent $i,j$, exclusion and positive vacuum
mass give $\rho_i+\rho_j<1$. Taking a weighted
average of the two occupation bounds yields

$$
\gamma\le\min\left\{\frac{b_i}{1-\rho_i},
\frac{b_j}{1-\rho_j}\right\}
\le\frac{b_i+b_j}{2-\rho_i-\rho_j}<b_i+b_j.
\tag{7.11}
$$

If $\omega_i=\omega_j=a$, (7.2) and the
arithmetic--geometric mean inequality give

$$
d_{\{i,j\}}=a(1-\sqrt{q_iq_j})
\ge\frac{a(2-q_i-q_j)}2=\frac{b_i+b_j}2.
\tag{7.12}
$$

For the two disjoint pairs $e,f$, write
$B_e=\sum_{i\in e}b_i$, $B_f=\sum_{i\in f}b_i$.
Equations (7.3), (7.11) and (7.12) give

$$
\delta\ge d_e+d_f\ge\frac{B_e+B_f}2
\ge\min(B_e,B_f)>\gamma.
\tag{7.13}
$$

Every path of length at least four contains two
disjoint adjacent pairs. Uniform weights satisfy
their equalities; Theorem 7.2 supplies the shorter
lengths. $\square$

**Corollary 7.4 (Activity-law transfer and the remaining quantifiers).**
At $2\le n\le6$, the joint optimum in Definition 5.1
equals $\max_\omega\gamma(\omega)$, and every
overall optimum has $r=1$ and a phase-optimal site
distribution. At every $n\ge2$, $r=1$ is optimal
for the fixed uniform site distribution. At $n\ge7$,
the inequality for arbitrary positive nonuniform
weights not covered by Theorem 7.3 remains an open
question here.

Proof. The finite connected legal graph and uniform
positive weights give a positive phase gap, while
continuity on the compact weight simplex gives a
phase maximizer. Apply (7.4), or Theorem 7.3 with
(5.8), respectively. The compression argument
does not automatically extend: at $n=7$ a $3+4$
split has ambient dimension 40 and legal dimension
34, so (7.8) requires eight low-band vectors.
The length-three block supplies two; the
length-four $2+2$ compression guarantees three,
so this count supplies only six. Neither this
failed count nor the sufficient certificate proves
or refutes the remaining universal inequality.
$\square$

### 7.3. Conditional relations retain the legal carrier

**Proposition 7.5 (Activity characterization and a support obstruction).**
For a positive law on $B_n$, activity form is
equivalent to the square identities
$p_Rp_{R\cup\{i,j\}}=p_{R\cup\{i\}}p_{R\cup\{j\}}$
on every doubly free fixed-exterior square at
nonadjacent sites. It is also equivalent to
$[K_i,K_j]=0$ for every $|i-j|\ge2$.
These separated-site relations alone, if the
exclusion carrier is discarded, do not imply the
spectral inequality of Theorem 7.2.

Proof. Activity form immediately gives each square
identity. Conversely, the insertion odds
$p_{R\cup\{i\}}/p_R$ do not change when one
occupied exterior site is deleted, by the relevant
square identity. Such a site is nonadjacent to
the legally inserted $i$. Deleting all exterior
occupations gives the constant odds
$\lambda_i=p_{\{i\}}/p_0$. Successive legal
insertions then give $p_R=p_0\prod_{i\in R}\lambda_i$.
This is the conditional-factorization argument
specialized to the exclusion support, not a claim
of unconditional occupation independence.

For commutation fix the complete exterior of
nonadjacent sites. Its legal sector is a product
of two sets, each either $\{0\}$ or $\{0,1\}$.
One- and two-state sectors commute automatically.
On a four-state sector write its positive masses
as $A=p_{00},B=p_{10},C=p_{01},D=p_{11}$ and
$\Delta=AD-BC$. The two conditional-expectation
projections, transported to Euclidean coordinates,
have a common constant direction and one remaining
principal angle. Directly computing that angle gives

$$
z=\frac{\Delta^2}{(A+B)(A+C)(B+D)(C+D)},
\qquad\|[K_i,K_j]\|_F^2=2z(1-z).
\tag{7.14}
$$

The denominator minus $\Delta^2$ is
$(A+B+C+D)(ABC+ABD+ACD+BCD)>0$.
Thus $0\le z<1$, and commutation is equivalent
to $\Delta=0$, exactly the square identity.

For the support obstruction take the full two-bit
cube with uniform product law and weights $1/2,1/2$.
Its independent toggle projections commute and
have a common zero ground vector, but their sum
has spectrum $0,1/2,1/2,1$. Hence
$\gamma+\Lambda=3/2$. This restores the word $11$
forbidden in $B_2$ and is not a counterexample
on the legal carrier. $\square$

**Attribution 7.6 (Established operators and the specific comparison).**
The conditional-resampling transition operator is
$T=I-D^{-1}H_{\lambda,\omega}D$.
[Dyer--Greenhill--Ullrich][DGU7], Definition 1.1
and Lemma 1.2, establish nonnegative spectrum for
such heat-bath mixtures. This supplies $H\preceq I$,
not the stronger comparison $\gamma+\Lambda\le1$.
Projection geometry, conditional factorization,
Rayleigh quotients and compression interlacing are
established tools; the block counts and combined
two-edge bounds above are the specific deductions
on this carrier.

There is also an exact local correspondence with
[Lesanovsky][L7], equations (1)--(2). Writing
$z_i=\sqrt{\lambda_i}$, its constrained local term
is

$$
h_i(z_i)=P_{i-1}(\sigma_x+z_iP_i+z_i^{-1}n_i)P_{i+1},
\qquad SK_iS=\frac{h_i(z_i)}{z_i+z_i^{-1}}.
\tag{7.15}
$$

Its homogeneous periodic spectral formulas do not
transfer to arbitrary open-path activities and
weights. Its unpinned open-boundary conserved edge
sectors also differ from the present endpoint
updates. The correspondence gives an established
quantum parent, not a preparation or a hardware
realization. No literature priority is claimed
for the source-specific inequalities above.

[DGU7]: ../../../Library/StatisticalMechanics/dyergreenhillullrich2014heatbath.md
[L7]: ../../../Library/StatisticalMechanics/lesanovsky2012constrainedspinchain.md


## 8. Real readout completes the same local information design

### 8.1. A different supplied control menu

**Definition 8.1 (Recorded real pair readout).** Fix $n\ge2$,
a positive normalized reference law $p$ on $B_n$ and
$\psi=\sqrt p$. Orient each legal site pair $\{s,t\}$ so
that $t$ has the occupied bit at that site. Choose one
fixed parameter

$$
0<\tau<\min_{\{s,t\}\text{ oriented legal pair}}
\frac{\psi_t}{\psi_s},\qquad
c=\frac1{\sqrt{1+\tau^2}},\quad
d=\frac\tau{\sqrt{1+\tau^2}}.
\tag{8.1}
$$

The minimum is positive because the carrier and pair
set are finite and $p$ is positive. At each real site
setting use the orthonormal pair vectors

$$
R_{st,+}=ce_s+de_t,\qquad
R_{st,-}=-de_s+ce_t,
\tag{8.2}
$$

and keep every blocked word as a resolved singleton.
Choose quadrature site $i$ with probability $r\omega_i$
and real site $i$ with probability $(1-r)\eta_i$, where
$\omega,\eta$ are distributions. The common $\tau$,
setting probabilities and effects stay fixed as the
unknown state varies. Every setting and outcome remains
recorded, and each preparation uses one setting.

The real rotation axis and its calibration are supplied
additional controls. This menu replaces the mode-basis
choice of Definition 5.1; it is not identified with that
original control menu or with the same hardware cost.
The common budget being compared is the number of
preparations.

### 8.2. The unchanged local Fisher matrix and global pure injection

**Theorem 8.2 (Local equivalence and pure-state completion).**
At the reference of Definition 8.1, on the full
horizontal tangent $u+iv$, $u,v\in V$, the new menu has

$$
F_{\rm real}=4\begin{pmatrix}I_V-rB_\omega&0\\0&rB_\omega\end{pmatrix}
=F_{\rm mode},\qquad Q=4I.
\tag{8.3}
$$

This equality holds for every $r\in[0,1]$ and every
$\eta$. If $0<r<1$ and every $\omega_i,\eta_i$ is
positive, its exact observation-law map is injective
on the pure rays whose amplitudes are all nonzero.
This global statement does not assume that the unknown
state equals the supplied reference.
If any site is omitted from either readout family,
the menu is not injective on this entire full-support
pure-ray domain.

Proof. At the reference the two real overlaps on a pair
are $A=c\psi_s+d\psi_t>0$ and
$C=-d\psi_s+c\psi_t>0$, by (8.1). The probabilities
are $A^2,C^2$. Along the normalized horizontal path
(5.1), their derivatives are

$$
2A(cu_s+du_t),\qquad 2C(-du_s+cu_t).
\tag{8.4}
$$

The imaginary tangent has zero first derivative in this
real basis. Nonzero overlaps allow ordinary Fisher
division, and orthogonality gives the pair contribution

$$
4(cu_s+du_t)^2+4(-du_s+cu_t)^2
=4(u_s^2+u_t^2).
\tag{8.5}
$$

A blocked word contributes $4u_s^2$. Hence every real
site has total information $4\|u\|^2$, independent of
its site and of $\eta$. Combine this with the quadrature
calculation (5.6) to obtain (8.3). The real-basis
information algebra is a use of the pure-state machinery
of [FSIC5]; it is not a new Fisher budget.

For injection write $\rho=zz^*$ for an unknown pure
state. Every nonempty legal word has an occupied site
$i$ with a neighbor $j$, since $n\ge2$. At site $j$ that
word is blocked. Its resolved singleton probability
therefore supplies $p_s=\rho_{ss}$, after division by
the known positive setting probability. All nonvacuum
diagonals are recovered this way, and
$p_0=1-\sum_{s\ne0}p_s$ gives the remaining diagonal.

For each legal pair, the conditional quadrature and
real probabilities satisfy

$$
\begin{aligned}
q_{Y,-}-q_{Y,+}&=2\operatorname{Im}\rho_{st},\\
q_{R,+}-q_{R,-}
&=(c^2-d^2)(p_s-p_t)+4cd\operatorname{Re}\rho_{st}.
\end{aligned}
\tag{8.6}
$$

Here $Y_\pm=(e_s\pm i e_t)/\sqrt2$ fixes the sign
convention. Both $c,d$ and both setting probabilities
are positive, so all complex edge coherences are
recovered. The full legal graph is connected, and the
unknown state has nonzero amplitudes on it. Apply
Parent/Readout Theorem 8.6's existing pure-state phase
propagation result to these actual diagonals and edges.
This gives a unique pure ray. $\square$

For the necessity of coverage, if real site $i$ is
omitted, the rays $z_s=\psi_s$ and
$z'_s=(-1)^{s_i}\psi_s$ have identical records.
Every imaginary edge coherence vanishes, while all
remaining real pairs preserve bit $i$ and hence their
real coherence. If quadrature site $i$ is omitted,
take $z_s^\pm=\psi_s e^{\pm i\theta s_i}$ with
$0<\theta<\pi$. Every remaining quadrature edge has
real coherence; the real site-$i$ outcomes depend
on the same cosine for the two states. Blocked
probabilities are identical in both constructions.
The rays in each pair are distinct because both
bit values occur on the positive carrier.

The equality is at the supplied real reference. It
neither equates the menus' Fisher matrices at every
complex state nor proves global mixed-state tomography.
The recovered density entries are still only the
diagonals and legal edges; the mixed-state nonedge
kernel of Parent/Readout §8.5 remains.

### 8.3. A uniform inverse that does not divide by the vacuum

**Theorem 8.3 (Fixed-length stability across a disappearing vacuum).**
Fix $n\ge4$, $0<r<1$, positive $\omega,\eta$, and
$c,d>0$ with $c^2+d^2=1$. Put $M=|B_n|-1$ and choose
$0<\delta\le1/\sqrt M$. Let $\mathcal U_\delta$ be the
pure rays with

$$
|z_s|\ge\delta\quad(s\ne0),
\tag{8.7}
$$

allowing $z_0=0$. For each ray choose the normalized
representative whose singleton-$1$ coordinate is
positive real. Let $q(z)$ be its full recorded
observation-law vector in the quadrature/real menu.
Define

$$
\begin{aligned}
a&=r\min_i\omega_i>0,\qquad
b=(1-r)\min_i\eta_i>0,\\
C&=\frac1a+
\frac{2/b+(M+1)|c^2-d^2|/a}{4cd},\\
K_0&=\frac1{2\delta a},\qquad
K_{j+1}=\frac{C+K_j}{\delta}.
\end{aligned}
\tag{8.8}
$$

Then the map is injective on $\mathcal U_\delta$, and
for any two of its chosen representatives,

$$
\|z-z'\|_2\le\sqrt{M+1}\,K_M
\|q(z)-q(z')\|_\infty.
\tag{8.9}
$$

In particular, neither the inverse nor this bound
divides by $|z_0|$.

Proof. The nonvacuum graph is connected by the graph
argument in Theorem 6.2. Choose a spanning tree on it,
rooted at singleton $1$, and attach the vacuum as a
leaf to that singleton. All parents in this augmented
tree are nonvacuum vertices. Its maximum depth is at
most $M$.

Recover the nonvacuum diagonals from blocked outputs
as in Theorem 8.2. Root amplitude is $z_{\{1\}}$
equal to the positive square root of its diagonal.
On a tree edge with recovered parent $s$ and child $t$,
use

$$
z_t=\frac{\overline{\rho_{st}}}{\overline{z_s}}.
\tag{8.10}
$$

If the stored orientation is reversed, use the
conjugate coherence first. For the vacuum leaf use
$z_0=\rho_{0,\{1\}}/\overline{z_{\{1\}}}$.
The same formulas are valid at $z_0=0$. Thus every
coordinate is recovered without a zero denominator,
proving injection.

Put $h=\|q(z)-q(z')\|_\infty$. A chosen blocked output
gives $|p_s-p'_s|\le h/a$ for $s\ne0$. Normalization
gives $|p_0-p'_0|\le Mh/a$. Dividing the two outcomes
in (8.6) by their fixed setting probabilities gives

$$
\begin{aligned}
|\operatorname{Im}(\rho_{st}-\rho'_{st})|&\le h/a,\\
|\operatorname{Re}(\rho_{st}-\rho'_{st})|
&\le\frac{2/b+(M+1)|c^2-d^2|/a}{4cd}\,h.
\end{aligned}
\tag{8.11}
$$

The bound $M+1$ covers an edge incident to the vacuum;
two nonvacuum diagonals require only 2. Consequently
$|\rho_{st}-\rho'_{st}|\le Ch$ for every legal edge.
At the root,

$$
|z_{\{1\}}-z'_{\{1\}}|
\le\frac{|p_{\{1\}}-p'_{\{1\}}|}
{|z_{\{1\}}|+|z'_{\{1\}}|}\le K_0h.
\tag{8.12}
$$

For every child step, $\rho_{st}=z_s\overline{z_t}$,
$|z_s|,|z'_s|\ge\delta$ and $|z'_t|\le1$ give

$$
|z_t-z'_t|
\le\frac{|\rho_{st}-\rho'_{st}|+|z_s-z'_s|}{\delta}.
\tag{8.13}
$$

This holds also for the vacuum child. Induction along
the tree bounds a coordinate at depth $j$ by $K_jh$.
Since $\delta\le1$ the constants in (8.8) are
nondecreasing, so all coordinates are bounded by
$K_Mh$. Summing their squared errors proves (8.9).
$\square$

The bound is for compatible pure-state observation
laws and a fixed finite length. It is not a guarantee
for an estimator applied to arbitrary noisy vectors,
and no uniform constant as $n\to\infty$ is asserted.
The nonvacuum amplitude lower bound and both positive
setting budgets are explicit premises.

**Corollary 8.4 (The rare-vacuum comparison with completed controls).**
For every fixed $n\ge4$, in the laws (6.1) with
$0<\epsilon\le1$, use $\tau=1/2$, positive fixed
$\omega,\eta$ and $0<r<1$. The local Fisher matrix
is exactly that of the corresponding quadrature/mode
mixture. The states lie in the same
$\mathcal U_{1/\sqrt{M+1}}$, so (8.9) gives a uniform
inverse bound independent of $\epsilon$.

All recorded outcome probabilities at these real
references are at least

$$
\min\left\{\frac{a}{2(M+1)},\frac{b}{5(M+1)}\right\}>0.
\tag{8.14}
$$

With uniform quadrature sites the joint ratio tends
to $\min\{rg_n,1-r\}>0$. At the rational length-four
reference (6.12), $r=9/10$ and uniform $\omega,\eta$
retain the bound $9/500>6/707$ while the completed
menu is globally injective on full-support pure rays.
For this rational reference the best design in the
completed family is attained with $0<r<1$ and every
quadrature site weight positive. Any positive real
site distribution then supplies global pure injection.

Proof. Nonvacuum amplitudes equal
$1/\sqrt{M+\epsilon}\ge1/\sqrt{M+1}$. The oriented
amplitude ratio is 1 on a nonvacuum pair and
$1/\sqrt\epsilon\ge1$ on a vacuum pair, so (8.1)
holds with $\tau=1/2$. Here $c=2/\sqrt5,d=1/\sqrt5$.
The conditional real probabilities are

$$
\begin{aligned}
q_{R,+}^{\rm vac}&=\frac{(2\sqrt\epsilon+1)^2}{5(M+\epsilon)},&
q_{R,-}^{\rm vac}&=\frac{(2-\sqrt\epsilon)^2}{5(M+\epsilon)},\\
q_{R,+}^{\rm nonvac}&=\frac9{5(M+\epsilon)},&
q_{R,-}^{\rm nonvac}&=\frac1{5(M+\epsilon)}.
\end{aligned}
\tag{8.15}
$$

Every blocked word is nonvacuum with probability
$1/(M+\epsilon)$. The quadrature probabilities are
$(1+\epsilon)/[2(M+\epsilon)]$ on a vacuum pair and
$1/(M+\epsilon)$ on a nonvacuum pair. These formulas
prove (8.14). Apply Theorems 8.2–7.3, (6.4) and (5.8).
For (6.12) the real probabilities are $144/3505$ and
$361/3505$ on vacuum pairs, $180/701$ and $20/701$
on nonvacuum pairs. Actual setting probabilities are
$9/40$ for each quadrature site and $1/40$ for each
real site. Proposition 6.4 and (8.3) supply the same
information bound. $\square$

For attainment at the rational reference, the ratio
in (5.8) is continuous on the compact closed
$(r,\omega)$ domain. It is zero at $r=0$ or whenever
a quadrature site is omitted, by the centered-bit
kernel used below. Every $r=1$ design is bounded
by $6/707$, strictly below the exhibited interior
design. A global maximizer therefore lies in
$0<r<1$ with all quadrature weights positive.
The fixed $\tau=1/2$ is regular independently of
these weights, and (8.3) is independent of $\eta$.

### 8.4. A Fisher supremum outside the globally identifying menu

**Proposition 8.5 (A positive real budget outside an attained Fisher optimum).**
Fix any positive reference law at $n=2$ or $n=3$,
or an activity-law reference at $2\le n\le6$, and
let $\gamma^*=\max_\omega\gamma(\omega)>0$. Within
the regular menus of Definition 8.1 with both families
and every site receiving positive probability, the
joint information ratio has supremum $\gamma^*$
and no maximizer. Every $r<1$ gives a value strictly
below that supremum. The excluded $r=1$ menu has the
global sign fiber of Proposition 6.5.

Proof. Equations (8.3), (5.4), Proposition 6.3 and
the activity-law transfer of Corollary 7.4 give
$\Gamma=r\gamma(\omega)$. The phase maximum is
positive by connectedness and uniform positive site
weights, and is attained on the compact weight simplex.
If $\omega_i=0$, the nonzero tangent
$u_s=\psi_s(s_i-\mathbb E_p s_i)$ is killed by all
remaining site projections, so $\gamma(\omega)=0$.
Hence every maximizing phase distribution has all
weights positive. Use such a distribution, positive
$\eta$, an allowed $\tau$, and let $r\uparrow1$ to
approach $\gamma^*$. For any $r<1$,
$r\gamma(\omega)\le r\gamma^*<\gamma^*$, proving
nonattainment. At $r=1$ the real family is absent and
Proposition 6.5 applies. $\square$

This is a boundary of the specified global pure-ray
identification promise. A promised local neighborhood
can use the original calibrated Fisher optimum; that
is a different target. No conclusion about original
finite-producer attainment follows from this menu.

### 8.5. A regular endpoint with both vacuum coordinates

**Proposition 8.6 (Endpoint neighborhood and short-length obstruction).**
Fix $n\ge4$, $\tau=1/2$, $0<r<1$ and positive
$\omega,\eta$. The completed menu extends regularly
to the normalized real state
$\psi_*=(0,\mathbf1/\sqrt M)$ at $\epsilon=0$.
With $h=\mathbf1/\sqrt M$ on the nonvacuum words,
put

$$
C_\omega=\frac12\sum_{\{s,t\}\in E(G_n^\circ)}
\omega_{i(s,t)}(e_s-e_t)(e_s-e_t)^{\mathsf T},
\qquad g_\omega=\lambda_{\min}(C_\omega|_{h^\perp})>0.
\tag{8.16}
$$

The endpoint worst information ratio on the full
horizontal tangent is

$$
\Gamma_* =\min\{1-r,rg_\omega\}>0.
\tag{8.17}
$$

There is a fixed projective neighborhood of $\psi_*$
on which the probability-law map is injective with
a Lipschitz inverse on its image. It contains all
sufficiently small positive-$\epsilon$ references,
with one inverse constant independent of $\epsilon$.
At $n=2,3$ independent phases of the nonvacuum
connected components prevent this endpoint conclusion.

Proof. The probabilities (8.15) have strictly positive
limits at $\epsilon=0$, as do all active quadrature
and blocked probabilities. The vacuum is never a
blocked word. Therefore ordinary score Fisher
division remains valid at this endpoint. The limiting
parent and real horizontal space are

$$
H_*=1\oplus C_\omega,\qquad
V_* =\mathbb R e_0\oplus h^\perp.
\tag{8.18}
$$

The nonvacuum graph is connected by Theorem 6.2,
and all its edge weights are positive, so
$g_\omega>0$. Also $0\preceq C_\omega\preceq I$.
The local calculation of Theorem 8.2 still applies
because every measurement overlap is nonzero, even
though the vacuum coordinate itself is zero.
On $V_*$ the largest parent eigenvalue is 1 and the
smallest is $g_\omega\le1$, proving (8.17).
In particular, the real vacuum direction has ratio
$1-r$ and its imaginary counterpart has ratio $r$;
both directions remain in the tested space.

For the inverse neighborhood use the projective
chart with the singleton-$1$ coordinate positive.
Every nonvacuum coordinate at $\psi_*$ has magnitude
$1/\sqrt M$. A sufficiently small fixed neighborhood
has every such magnitude at least
$\delta=1/(2\sqrt M)$. It is contained in
$\mathcal U_\delta$ of Theorem 8.3. That theorem's
explicit bound proves injection and Lipschitz
stability of the normalized root-gauged vectors,
without division by a vacuum amplitude. The same
neighborhood contains the rare-vacuum references
for all sufficiently small $\epsilon>0$, so its
inverse constant is independent of $\epsilon$.

For $n=2,3$, deleting the vacuum leaves the components
of Proposition 6.3. At $\epsilon=0$ all vacuum edge
coherences vanish. Independently changing component
phases therefore leaves every diagonal and legal
edge coherence unchanged, hence every outcome law
unchanged. The phases can change by arbitrarily
small amounts while giving distinct rays. Thus no
injective projective neighborhood exists there.
This does not contradict full-support injection
for each positive $\epsilon$. $\square$

**Attribution 8.7 (Application and added correspondence).**
Real-basis Fisher saturation uses [FSIC5]; reconstruction
from actual diagonals and complex edges uses
Parent/Readout Theorem 8.6 and its polarization source.
The paired local controls have close predecessors in
[HPS6] and the broader $X,Y,Z$ menu of [MCHPZ6].
The source-specific correspondence here is replacement
of the mode setting by recorded real-site settings
without changing the local Fisher blocks, together
with a fixed-length inverse through the nonvacuum tree
and the associated menu-attainment boundary. It does
not assign new ownership to basis saturation, phase
propagation or Lipschitz estimates, and no literature
priority is claimed.


### 8.6. The recorded menu supplies the five-mode history readout

**Mathematical application 8.8 (A readout correspondence for phase histories).**
Use the five-mode source $(0,1,2,3,13)$, the fixed
positive base law and common initial phases of
[Probability, Phase Transport and Holonomy][PTH8],
Theorem 3.12. Its ideal coherence menu consists of
the five legal edges
$0\!-\!1,0\!-\!2,0\!-\!3,1\!-\!13,3\!-\!13$.
These are exactly the legal-toggle edges of $B_3$.
With any regular reference calibration and positive
coverage in both families of Definition 8.1, the
recorded probability-law menu realizes the same
endpoint-history equivalence relation as that ideal
menu. The compact holonomy summary supplied there
is therefore also the exact summary for these
recorded probabilities.

Indeed the endpoint occupation law is the same
fixed law for every history. For an oriented edge,
divide by its known setting probability and use
(8.6). The two ideal Hermitian expectations in
that source are recovered as

$$
\begin{aligned}
\langle A_{st}\rangle
&=2\operatorname{Re}\rho_{st}
=\frac{q_{R,+}-q_{R,-}-(c^2-d^2)(p_s-p_t)}{2cd},\\
\langle B_{st}\rangle
&=-2\operatorname{Im}\rho_{st}=q_{Y,+}-q_{Y,-}.
\end{aligned}
\tag{8.19}
$$

Conversely, the fixed diagonals and these ideal
expectations determine both pair probabilities
by their sums $p_s+p_t$ and differences (8.6).
Every blocked probability is already fixed.
Thus equality of the recorded laws is equivalent
in both directions to equality of the ideal menu.
The source's Theorem 3.12 then supplies equality
of the realized compact residual class. Its
continuous controls, reachability and symmetry
regimes remain premises of that application.

This uses Theorem 8.2's measurement correspondence
and the existing history quotient; it is not an
additional phase-propagation or controllability
theorem. Recovering that endpoint class does not
recover the path, and equality of exact laws does
not imply perfect discrimination from finitely
many preparations. The extra real-axis control
remains a supplied resource. The mode occupation
$p_{13}=\kappa$ is a diagonal probability, while
the history information used here is in complex
edge coherences; these are different entries of
the same state, with different readout roles.

[PTH8]: https://github.com/the-omega-institute/trureturing/blob/9fb5243e1b84656137d2604a8db80f06c0ae8d59/docs/develop/theory/AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md

## 追加锚（本行以下为增补区）

## 9. Collective occupation cylinders and an all-length parity family

### 9.1. A cut on the original legal carrier

**Definition 9.1 (Zero cylinders).** Keep the positive activity law,
open path, site weights and operators of Chapter 7. Let $Z_T$ denote
the activity partition function with the vertices in $T$ deleted,
so $Z_\varnothing=Z$. For a nonempty set $T\subseteq[n]$, put

$$
A_T=\{s\in B_n:s_i=0\text{ for every }i\in T\},
\qquad \alpha_T=p(A_T)=\frac{Z_T}{Z}.
\tag{9.1}
$$

Deletion evaluates an event in the original law. It does not replace
the generator by a chain on a smaller graph, rescale its weights, or
remove a tangent coordinate. Write $N(i)$ for the actual open-path
neighbors of $i$. Define

$$
\kappa_T=
\frac{Z\displaystyle\sum_{i\in T}\omega_iq_iZ_{T\cup N(i)}}
{Z_T(Z-Z_T)},
\qquad
\kappa_* = \min_{\varnothing\ne T\subseteq[n]}\kappa_T.
\tag{9.2}
$$

The vacuum belongs to $A_T$, and a singleton occupation at any site
in $T$ lies outside it. Positive activities therefore give
$0<\alpha_T<1$.

**Theorem 9.2 (Collective cylinder certificate).** For every $n\ge2$,
every positive activity vector, and every nonnegative normalized
site distribution,

$$
\gamma\le\kappa_*\le U.
\tag{9.3}
$$

For any nonempty $T$ and physical-path matching $\mathcal M$,
$\kappa_T\le D_{\mathcal M}$ is sufficient for
$\gamma+\Lambda\le1$.

Proof. For any real observable $f$ the insertion-edge Dirichlet form is

$$
\mathcal E_\omega(f,f)=
\sum_{\substack{s\in B_n,\ i\in[n]\\
s_i=0,\ s+e_i\in B_n}}
p(s)\omega_iq_i\bigl(f(s)-f(s+e_i)\bigr)^2.
\tag{9.4}
$$

Each undirected edge is counted once from its empty endpoint.
Take $f_T=\mathbf1_{A_T}-\alpha_T$. Its variance is
$\alpha_T(1-\alpha_T)$. An insertion crosses this cut exactly when
$i\in T$ and the original word has every site in $T\cup N(i)$ empty.
The empty-side mass of these words is $Z_{T\cup N(i)}/Z$. Thus

$$
\mathcal E_\omega(f_T,f_T)
=\frac1Z\sum_{i\in T}\omega_iq_iZ_{T\cup N(i)}.
\tag{9.5}
$$

Its Rayleigh quotient is (9.2), giving the first inequality in (9.3).
For $T=\{i\}$, the centered zero indicator differs by sign from the
centered occupation $s_i-\rho_i$. Equation (7.10) gives
$\kappa_{\{i\}}=b_i/(1-\rho_i)$. Taking a minimum over all subsets
includes these singleton tests, proving $\kappa_*\le U$.
Finally combine $\gamma\le\kappa_T$ with $\delta\ge D_{\mathcal M}$
and $\delta=1-\Lambda$. $\square$

The variational use of a cut is established Markov-chain mathematics.
Blanca--Galvin--Randall--Tetali [BGRT12], Section 4.1 and Theorem 4.1,
use conductance for hard-core Metropolis dynamics on two-dimensional
regions. Their rates and lattice conclusions are not imported into
(9.4). The flux (9.5) is computed here for the stipulated weighted
heat-bath path, with its original endpoints and activity law.

**Corollary 9.3 (A rational sufficient certificate).** Put

$$
r_{ij}=\frac{\omega_i\omega_j(1-q_iq_j)}{\omega_i+\omega_j},
\tag{9.6}
$$

with value zero when both weights vanish. Then $r_{ij}\le d_{ij}$.
Consequently $\kappa_T\le\sum_{ij\in\mathcal M}r_{ij}$ is sufficient
for the same two-edge comparison. It is entirely rational when the
activities and weights are rational.

Proof. The smaller root $d=d_{ij}$ satisfies
$d(\omega_i+\omega_j-d)=\omega_i\omega_j(1-q_iq_j)$ and
$0\le d\le\min(\omega_i,\omega_j)$. If the weight sum is positive,
division by $\omega_i+\omega_j-d\le\omega_i+\omega_j$ proves (9.6).
Zero weights give the stated zero cases. $\square$

Every deleted partition function is evaluated by multiplying the
partition functions of its undeleted intervals. Within an interval,

$$
Z_{[a,b]}=Z_{[a,b-1]}+\lambda_bZ_{[a,b-2]},
\qquad Z_\varnothing=1,
\qquad Z_{[a,a]}=1+\lambda_a.
\tag{9.7}
$$

### 9.2. A strict enlargement beyond singleton probes

**Proposition 9.4 (A seven-site collective certificate).** Take
$\lambda_i=100$ and

$$
\omega=\frac1{304}(1,100,1,100,1,100,1),
\qquad T=\{1,3,5,7\},
\qquad \mathcal M=\{12,34,56\}.
\tag{9.8}
$$

Then the collective certificate succeeds, while every certificate
of the form $U\le D_{\mathcal M'}$ fails.

Proof. Recurrence (9.7) gives

$$
Z=110150701,\qquad Z_T=1030301,
\qquad
\kappa_T=\frac{55620651}{845984272304}<\frac1{15000},
\tag{9.9}
$$

and direct substitution in (9.6) gives

$$
\sum_{ij\in\mathcal M}r_{ij}
=\frac{15075}{78302876}>\frac1{6000}.
\tag{9.10}
$$

Hence $\gamma<\delta$ and $\gamma+\Lambda<1$. On the other hand,
the actual constrained marginals give

$$
U=\frac{1090601}{1857622704}>\frac1{2000}.
\tag{9.11}
$$

All adjacent edges have the same $d$. Its root identity and
$d\le1/304$ imply
$d\le(1/304)(1-(100/101)^2)=201/3101104$.
Every matching has at most three edges, so

$$
\max_{\mathcal M'}D_{\mathcal M'}
\le\frac{603}{3101104}<\frac1{5000}<U.
\tag{9.12}
$$

There is also no equal-weight adjacent pair. Thus the sufficient
tests of Theorem 7.3 do not establish this instance, whereas
Theorem 9.2 does. $\square$

All separations in this proof are strict. The partition functions,
$U$, $\kappa_T$ and the finitely many matching bounds are continuous
on positive activities and the interior weight simplex. Therefore
a nonempty relatively open neighborhood of (9.8) has the same
strict separation. It contains fully nonuniform activity and
weight vectors. This is an enlargement of sufficient conditions
for the conjecture, not a violation of the conjecture.

### 9.3. Homogeneous activities and arbitrary parity imbalance

**Theorem 9.5 (All lengths with alternating site weights).** For every
$n\ge2$ and $t>0$, let $\lambda_i=t$. Set $\omega_i=a$ on odd sites
and $\omega_i=b$ on even sites, where $a,b>0$ and
$\lceil n/2\rceil a+\lfloor n/2\rfloor b=1$. Then

$$
\gamma+\Lambda\le1,
\qquad \Gamma(r,\omega)=r\gamma\quad(0\le r\le1).
\tag{9.13}
$$

There is no restriction on $t$ or on $a/b$.

Proof. Lengths through six follow from Theorem 7.2. Assume $n\ge7$,
and put $m=\lfloor n/2\rfloor$, $h=1+t$, $q=t/h$ and $c=\min(a,b)$.
A matching of $m$ adjacent edges gives

$$
\delta\ge\frac{mc}{h}.
\tag{9.14}
$$

Indeed $d(a,b)\ge c(1-q)=c/h$. When $a\le b$, the required
square-root comparison follows from

$$
(b-a+2aq)^2-\bigl((b-a)^2+4abq^2\bigr)
=4a(b-a)q(1-q)\ge0.
\tag{9.15}
$$

The other ordering is symmetric. If $t\le1$, conditional exclusion
gives $\rho_i\le q$, so $U\le c$. Since $m\ge3$ and $h\le2$,
$\gamma\le U\le c\le mc/h\le\delta$.

Now let $t\ge1$ and let $T$ be the lighter-weight parity. More
generally, for either entire parity under homogeneous activity, write
$W_T=\sum_{i\in T}\omega_i$ and
$E_T=\sum_{i\in T\cap\{1,n\}}\omega_i$. Its complement has no
internal path edges. Formula (9.2) therefore simplifies to

$$
\alpha_T=\frac{h^{n-|T|}}{Z_n},
\qquad
\kappa_T=\frac{t(W_T+tE_T)}{h^3(1-\alpha_T)}.
\tag{9.16}
$$

An interior insertion blocks two opposite-parity sites; an endpoint
insertion blocks one. This is the source of $E_T$, which cannot be
discarded for the open chain.

The homogeneous recurrence gives
$Z_{k+2}=hZ_k+tZ_{k-1}>hZ_k$ for $k\ge1$.
Also $Z_4-2h^2=t^2-1\ge0$. Hence for $n=2m$,
$\alpha_T\le1/2$. Each parity has $m$ sites and one endpoint, so

$$
\kappa_T\le\frac{2ct(m+t)}{h^3}\le\frac{mc}{h}.
\tag{9.17}
$$

The final comparison is equivalent to $(m-2)t^2+m\ge0$.

For $n=2m+1$ and the odd parity lighter, $T$ has $m+1$ sites and
both endpoints. Put $x=t-1\ge0$. Direct expansion gives

$$
Z_7-4h^3=x^4+10x^3+27x^2+23x+2>0.
\tag{9.18}
$$

The same recurrence propagates this strict bound to every odd
length at least seven. Thus $\alpha_T<1/4$ and

$$
\kappa_T<\frac{4ct(m+1+2t)}{3h^3}\le\frac{mc}{h}.
\tag{9.19}
$$

The last comparison is equivalent to
$(3m-8)t^2+(2m-4)t+3m\ge0$, valid for $m\ge3$.

For $n=2m+1$ and the even parity lighter, $T$ has $m$ sites and no
endpoints. The configurations with zero occupied even sites have
total mass $h^{m+1}$. Those with exactly one occupied even site have
mass $mt h^{m-1}$: its two odd neighbors are blocked and the
remaining $m-1$ odd sites are free. These disjoint classes give

$$
Z_{2m+1}\ge h^{m+1}+mt h^{m-1},
\qquad
\alpha_T\le\frac{h^2}{h^2+mt}.
\tag{9.20}
$$

Consequently

$$
\kappa_T\le\frac{c(h^2+mt)}{h^3}\le\frac{mc}{h}.
\tag{9.21}
$$

The last comparison is equivalent to
$(m-1)t^2+(m-2)t+(m-1)\ge0$. All cases now give
$\gamma\le\kappa_T\le mc/h\le\delta$. Equation (5.8) proves
the Fisher statement. $\square$

This theorem extends the uniform-site case along an unrestricted
parity imbalance at homogeneous activity. The universal statement
with arbitrary positive activities and arbitrary positive weights
at $n\ge7$ remains unresolved outside the preceding certificate
domains. Failure of every cylinder certificate is a necessary
condition for a counterexample candidate, not a sufficient one.

[BGRT12]: ../../../Library/StatisticalMechanics/blancagalvinrandalltetali2012slowmixing.md

## 10. A joint occupation phase escapes every linear occupation probe

### 10.1. The same positive law and the same insertion form

**Definition 10.1 (Five-site probe sufficiency).** In (9.4), take

$$
\lambda=(100,1,100,1,100),\qquad
\omega=\left(\frac{368}{2565},\frac{5101}{17955},\frac{289}{1995},
\frac{5101}{17955},\frac{368}{2565}\right).
\tag{10.1}
$$

With site one the least significant bit, the complete legal word
list is $0,1,2,4,5,8,9,10,16,17,18,20,21$. The product-activity
partition function is $Z=1030504$. Let
$L_c(s)=\sum_{i=1}^5c_is_i$ for real $c$. The probe sufficiency
assertion is the implication

$$
\left[\forall c\in\mathbb R^5,\quad
\mathcal E_\omega(L_c,L_c)\ge\frac1{10}\operatorname{Var}_p(L_c)\right]
\Longrightarrow
\left[\forall f:B_5\to\mathbb R,\quad
\mathcal E_\omega(f,f)\ge\frac1{10}\operatorname{Var}_p(f)\right].
\tag{10.2}
$$

This is a question about the sufficiency of a restricted probe family.
The earlier chapters do not assert (10.2).

**Theorem 10.2 (Linear occupation probe insufficiency).** Implication
(10.2) is false for the actual positive law and normalized weights
(10.1). The function

$$
f(s)=(1-s_1)(1-s_3)+s_2
=1-s_1-s_3+s_1s_3+s_2
\tag{10.3}
$$

has a smaller quotient than the lower bound obeyed by every linear
occupation phase.

Proof. Write $C_{ij}=\mathbb E_p(s_is_j)-\rho_i\rho_j$ and
$D=\operatorname{diag}(\omega_i\rho_i/(1+\lambda_i))$. Along a
site-$i$ edge the change in $L_c$ is $c_i$, so

$$
\operatorname{Var}_p(L_c)=c^TCc,
\qquad \mathcal E_\omega(L_c,L_c)=c^TDc.
\tag{10.4}
$$

For $P=D-C/10$ put $S=962888835832892640$. Direct product-law
moment evaluation gives $SP=M$, where

$$
M=\begin{pmatrix}
400935678147200&9435442634100&-9341106705000&91579477500&-90672750000\\
9435442634100&4008578567811&9434517772050&-92495272275&91579477500\\
-9341106705000&9434517772050&404787065336100&9434517772050&-9341106705000\\
91579477500&-92495272275&9434517772050&4008578567811&9435442634100\\
-90672750000&91579477500&-9341106705000&9435442634100&400935678147200
\end{pmatrix}.
\tag{10.5}
$$

Let $A=\operatorname{diag}(1,10,1,10,1)$ and $B=AMA$.
The diagonal-dominance remainders
$r_i=B_{ii}-\sum_{j\ne i}|B_{ij}|$ are

$$
r=(296233677576200,201992930717100,197414496485100,
201992930717100,296233677576200).
\tag{10.6}
$$

They are all positive. For $y=A^{-1}c$ the exact square decomposition is

$$
c^TPc=\frac1S\left[
\sum_i r_i y_i^2+
\sum_{i<j}|B_{ij}|\bigl(y_i+\operatorname{sgn}(B_{ij})y_j\bigr)^2
\right].
\tag{10.7}
$$

Thus $P$ is positive definite, and the antecedent of (10.2) holds
for the entire real coefficient family, not merely a finite sample.
For (10.3), evaluating the same insertion edges and the same law gives

$$
\mathcal E_\omega(f,f)=\frac{8757839}{207641403480},
\qquad
\operatorname{Var}_p(f)=\frac{131365851}{265484623504},
\tag{10.8}
$$

and hence

$$
\frac{\mathcal E_\omega(f,f)}{\operatorname{Var}_p(f)}
=\frac{132720413542}{1557033067485}<\frac1{10}.
\tag{10.9}
$$

This disproves the consequent. $\square$

The joint term is necessary for this function. On the four legal
words $0,1,4,5$, its mixed difference
$f(0)+f(5)-f(1)-f(4)$ equals one. Every affine linear occupation
function has mixed difference zero on these same four words.
The failure is therefore a loss of an actual joint-occupation
direction, with no alteration of the probability law or rates.

### 10.2. A precise quantum phase interpretation

**Mathematical application 10.3 (Diagonal joint phases).** On the
legal-word Hilbert space let
$\psi_s=\sqrt{p(s)}$ and let $\hat n_i$ be the diagonal occupation
projections. A real phase function $f$ defines

$$
\psi(\theta)_s=e^{i\theta f(s)}\psi_s,
\qquad
v_f(s)=\psi_s\bigl(f(s)-\mathbb E_pf\bigr).
\tag{10.10}
$$

All occupation probabilities remain fixed along this curve.
The common-phase component has been removed, giving
$v_f\perp\psi$ and $\|v_f\|^2=\operatorname{Var}_p(f)$.
On a legal edge the projector matrix (7.5) has ground amplitudes
in the ratio $\sqrt{\lambda_i}$. Its quadratic form on $v_f$ is
exactly that edge's summand in (9.4). Therefore

$$
\langle v_f,H_{\lambda,\omega}v_f\rangle
=\mathcal E_\omega(f,f),
\qquad
\frac{\langle v_f,H_{\lambda,\omega}v_f\rangle}{\|v_f\|^2}
=\frac{\mathcal E_\omega(f,f)}{\operatorname{Var}_p(f)}.
\tag{10.11}
$$

Linear occupation phases are generated by $\sum_i c_i\hat n_i$.
Function (10.3) instead uses the diagonal Hermitian generator

$$
\hat F=(I-\hat n_1)(I-\hat n_3)+\hat n_2
=I-\hat n_1-\hat n_3+\hat n_1\hat n_3+\hat n_2.
\tag{10.12}
$$

It contains a joint phase operation on sites one and three.
Theorem 10.2 shows a phase direction of smaller parent quadratic
form than every nonzero linear occupation direction. It explains
why a linear occupation covariance calculation cannot provide
a lower bound for the entire phase sector by itself.

The diagonal statistic $\langle\hat n_1\hat n_3\rangle$ and the
phase generator $\hat n_1\hat n_3$ use the same occupation operator
in different roles. The former is a probability; exponentiating
the latter changes relative phases while preserving those
probabilities. Neither role identifies it with an exchange
coherence $\langle\hat a_1^\dagger\hat a_3\rangle$, a gauge
curvature, or a physical energy. The parent operator in (10.11)
is dimensionless; a unitful Hamiltonian and realization require
additional choices.

Theorem 10.2 refutes probe sufficiency. It does not refute
$\gamma+\Lambda\le1$, which holds at this length by Theorem 7.2.
Nor does it establish a uniformly bounded polynomial degree
that captures the slowest phase for every length and every
positive activity law.

## 追加锚（本行以下为增补区）
