# Compatible predictive waves and relational spectra VII

## 122. A reflected scalar profile on the entire completion ball

**Definition 122.1 (Fixed source, axial coordinates and scalar profile).**
Fix an allowed source $\mathfrak s$ of Definition 114.1 in
[volume VI](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_VI.md).
Retain exactly its finite vector $P_{\mathfrak s}$ from Proposition
118.2, its parameter set $\mathcal P$ from (114.1), and both original
anchored moduli $\omega_{\mathfrak s,h_0}$ and
$\omega^{\rm all}_{\mathfrak s,h_0}$ from Definition 120.1.
In particular, alternatives still have $0<|\gamma|\le1$ and
$\|h\|\le1$. Put

$$
\begin{gathered}
\tau=\|t\|>0,\qquad e=t/\tau,\qquad \Pi=I_3-ee^\dagger,\\
h_0=(a+\mathrm i\beta)e+v_0,\qquad
a,\beta\in\mathbb R,\quad v_0\perp e,\\
A=|a|,\qquad \eta=\|v_0\|,\qquad A^2+\beta^2+\eta^2\le1,\\
q_{A,\eta}(r)=r\bigl(\eta+|r-2A|\bigr),\qquad 0\le r\le2,\\
R(\delta;A,\eta)
 =\max\{r\in[0,2]:q_{A,\eta}(r)\le\delta\},\qquad \delta\ge0.
\end{gathered}
\tag{122.1}
$$

The maximum exists since its feasible set is a nonempty closed subset
of $[0,2]$. Define the two actual law errors, including at auxiliary
zero-retention alternatives, by

$$
\begin{aligned}
d_f(\gamma,h;h_0)
 &=\|P_{\mathfrak s}(\gamma,h)-P_{\mathfrak s}(0,h_0)\|_\infty,\\
d_a(\gamma,h;h_0)
 &=\Delta_{\rm all}((\gamma,h),(0,h_0)).
\end{aligned}
\tag{122.2}
$$

These are the original raw probabilities, with the nine original
subnormalised prefix events, actual histories, labels, clocks, installed
menu and externally fixed schedules of Definitions 114.1 and 118.1.
Each hypothesis has one full ten-dimensional completion for emission,
the single forward return and every history, as in §106; the two
hypotheses may have different completions. In particular, (122.2)
does not add a preparation, repetition or selection operation.

Write $c=c_{\mathfrak s}>0$ and $C=C_{\mathfrak s}>0$ for the fixed
constants of Theorem 118.3, choosing (118.18) and (118.20), and use
its already established consequence (120.3). With the matrices of
Definition 118.1, abbreviate

$$
\begin{aligned}
Q(h;h_0)
 &=\|hh^\dagger-h_0h_0^\dagger\|_{\rm HS}
       +\|\mathsf S_h-\mathsf S_{h_0}\|_{\rm HS},\\
D_0(\gamma,h;h_0)
 &=Q(h;h_0)+|\gamma|(1+\|h-h_0\|).
\end{aligned}
\tag{122.3}
$$

Thus the mathematical premises used below are exactly

$$
cD_0\le d_f\le d_a\le CD_0.
\tag{122.4}
$$

The rank-one lifting intermediate is Balan–Zou,
[*On Lipschitz Analysis and Lipschitz Synthesis for the Phase Retrieval
Problem*, arXiv:1506.02092v1, §2.2, Theorems 2.3–2.4](https://arxiv.org/pdf/1506.02092v1).
Its frame-intensity comparison uses a phase-retrievable frame on a
global-phase quotient. The local spectral bounds in its Theorem 2.6
also assume such a frame. Here $\mathsf S_h$ is source-fixed and
phase-sensitive, and (122.4) is the source-specific comparison already
proved in §118, rather than a new frame-injectivity assumption.

**Proposition 122.2 (Exact formula, entry value and cap).**
For $A,\eta\ge0$ with $A^2+\eta^2\le1$, put

$$
d_b=2A\eta,\qquad d_c=2(\eta+2-2A).
\tag{122.5}
$$

Then $d_c\ge d_b$ and, for every $\delta\ge0$,

$$
R(\delta;A,\eta)=
\begin{cases}
\displaystyle
\frac{\eta+2A-\sqrt{(\eta+2A)^2-4\delta}}2,
 &0\le\delta<d_b,\\[6pt]
\displaystyle
\frac{2A-\eta+\sqrt{(\eta-2A)^2+4\delta}}2,
 &d_b\le\delta<d_c,\\[6pt]
2,&\delta\ge d_c.
\end{cases}
\tag{122.6}
$$

An interval in this formula can be empty. The middle expression equals
$2A$ at $\delta=d_b$ and equals $2$ at $\delta=d_c$ when extended
to those endpoints. In particular, the value at $d_b$ is always $2A$,
including $A=1,\eta=0$, when the last case applies. Moreover,

$$
R(0;A,\eta)=
\begin{cases}2A,&\eta=0,\\0,&\eta>0,\end{cases}
\qquad
R(\delta;A,\eta)=2\ \Longleftrightarrow\ \delta\ge d_c.
\tag{122.7}
$$

If $A\eta>0$, the left limit at the entry value is

$$
R(d_b-;A,\eta)=\min\{\eta,2A\}.
\tag{122.8}
$$

Consequently there is a jump precisely when $0<\eta<2A$.
At $\eta=2A>0$ the two branches meet continuously. If $\eta>2A$,
they also meet continuously. If $A\eta=0$ the entry value is the
left endpoint $0$, with no left-hand limit in this domain. For
$A=0$, the formula reduces to
$\min\{2,(\sqrt{\eta^2+4\delta}-\eta)/2\}$; for $A=\eta=0$
this is $\min\{2,\sqrt\delta\}$.

*Proof.* On the two sides of $2A$ the defining function is

$$
q_{A,\eta}(r)=
\begin{cases}
r(\eta+2A-r),&0\le r\le2A,\\
r(r+\eta-2A),&2A\le r\le2.
\end{cases}
\tag{122.9}
$$

The second part is increasing, strictly beyond its left endpoint,
and has values $d_b,d_c$ at the two endpoints. Also
$d_c-d_b=2(1-A)(\eta+2)\ge0$. Thus when $\delta\ge d_b$,
the largest feasible point is the positive root in the second part,
unless it reaches $2$. This proves the last two cases of (122.6).

Suppose $0\le\delta<d_b$. Necessarily $A\eta>0$, and no point
at or beyond $2A$ is feasible. The concave first part starts below
or at $\delta$ at $0$ and ends strictly above it at $2A$. Its
smaller root is the largest feasible point in $[0,2A]$; its larger
root lies beyond $2A$. Its discriminant is positive, since
$4\delta<8A\eta\le(2A+\eta)^2$. This gives the first case.

Substitution at $d_b$ gives $2A$ for the second root, while the
first root tends to
$(2A+\eta-|2A-\eta|)/2=\min\{2A,\eta\}$. These calculations
prove all entry and equality assertions. Since $2$ is feasible
exactly when $\delta\ge q_{A,\eta}(2)=d_c$, the cap assertion
is an equivalence. At zero error, the zeros of (122.9) are $0$
and, only when $\eta=0$, $2A$. This proves (122.7) and also
covers the coincident zero and cap at $A=1,\eta=0$. The remaining
specialisations follow by substitution. $\square$

**Lemma 122.3 (A uniform geometric upper comparison).**
For every two $h_0,h$ in the closed unit ball, put
$r=\|h-h_0\|$ and let $A,\eta$ be as in Definition 122.1. Define

$$
d_\tau=\frac3{2\tau},\qquad B_\tau=2+11d_\tau.
\tag{122.10}
$$

Then

$$
q_{A,\eta}(r)\le B_\tau Q(h;h_0).
\tag{122.11}
$$

*Proof.* Write
$h=(a+x+\mathrm i(\beta+y))e+v_0+w$, with $x,y$ real and
$w\perp e$, and put $z=\mathrm i y e+w$. The skew-matrix
diagonal and off-diagonal entries used in (120.14) give

$$
|y|\le\frac{Q}{2\tau},\qquad
\|w\|\le\frac Q\tau,\qquad
\|z\|\le d_\tau Q.
\tag{122.12}
$$

Here $x e$ and $z$ are orthogonal as vectors in the underlying real
Euclidean space, so $|x|\le r\le2$, $\|z\|\le2$, and
$0\le r-|x|\le\|z\|$. Let $\widehat h=h_0+xe=h-z$.
Although $\widehat h$ need not lie in the ball, its norm is at most
$3$. The outer-product identity gives

$$
\begin{aligned}
\widehat h\widehat h^\dagger-h_0h_0^\dagger
 &=x\bigl((2a+x)ee^\dagger+ev_0^\dagger+v_0e^\dagger\bigr),\\
\|\widehat h\widehat h^\dagger-h_0h_0^\dagger\|_{\rm HS}
 &=|x|\sqrt{(2a+x)^2+2\eta^2},\\
\|\widehat h\widehat h^\dagger-hh^\dagger\|_{\rm HS}
 &\le(\|\widehat h\|+\|h\|)\|z\|\le4\|z\|.
\end{aligned}
\tag{122.13}
$$

Since $||x|-2|a||\le|2a+x|$, it follows that

$$
q_{A,\eta}(|x|)
 \le |x|(\eta+|2a+x|)
 \le\sqrt2\,(Q+4\|z\|).
\tag{122.14}
$$

For $A,\eta\le1$, the absolute values of the two derivatives in
(122.9) are at most $5$ on $[0,2]$. Splitting an interval at
$2A$ if necessary proves that $q_{A,\eta}$ is $5$-Lipschitz.
Consequently (122.12)–(122.14) imply

$$
q_{A,\eta}(r)
 \le[\sqrt2+(4\sqrt2+5)d_\tau]Q
 \le B_\tau Q.
$$

This proof keeps $\beta$ arbitrary and does not assume either sign
of $a$ or any interior margin for either vector. $\square$

**Lemma 122.4 (Ball-preserving lower witnesses).**
For every anchor of Definition 122.1 and every $r\in[0,2]$,
there exists $h_r$ in the closed unit ball such that, with
$J_\tau=6+2\tau$,

$$
\|h_r-h_0\|\ge r/\sqrt5,\qquad
Q(h_r;h_0)\le J_\tau q_{A,\eta}(r).
\tag{122.15}
$$

One explicit choice is obtained by taking $\sigma=\operatorname{sgn}(a)$
when $a\ne0$, either sign when $a=0$, and setting

$$
z_r=h_0-\sigma r e,\qquad
m_r=\max\{1,\|z_r\|\},\qquad h_r=z_r/m_r.
\tag{122.16}
$$

For $r\le2A$ no projection occurs and the displacement is exactly
$r$. These assertions include every anchor on the unit sphere.

*Proof.* The exact norm calculation is

$$
\|z_r\|^2=\|h_0\|^2+r(r-2A)\le1+r(r-2A)\le5.
\tag{122.17}
$$

Thus $m_r\le\sqrt5$. If $r\le2A$, then $m_r=1$.
If $m_r>1$, necessarily $r>2A$; the real axial component of
$h_r-h_0$ has absolute value

$$
\frac r{m_r}+A\left(1-\frac1{m_r}\right)\ge\frac r{\sqrt5}.
\tag{122.18}
$$

This proves the displacement assertion in both cases.
The real axial displacement leaves the skew matrix unchanged, and
the outer-product calculation in (122.13), now with $x=-\sigma r$,
gives

$$
\|z_rz_r^\dagger-h_0h_0^\dagger\|_{\rm HS}
 =r\sqrt{(r-2A)^2+2\eta^2}
 \le\sqrt2\,q_{A,\eta}(r).
\tag{122.19}
$$

If projection occurs, write $d=\|z_r-h_r\|=m_r-1$.
Equation (122.17) implies

$$
d=\frac{\|z_r\|^2-1}{\|z_r\|+1}
 \le r(r-2A)\le q_{A,\eta}(r).
\tag{122.20}
$$

If no projection occurs, $d=0$. In either case the correction to
the outer product is at most
$(\sqrt5+1)d\le4d$, and that to the skew matrix is at most
$2\tau d$. Adding these bounds to (122.19) proves (122.15),
since $\sqrt2+4+2\tau\le J_\tau$.
The construction uses the full closed ball itself; (122.17) is
also valid when $\|h_0\|=1$. $\square$

## 123. Uniform original-law enclosures and the retained transition window

**Theorem 123.1 (Two horizontal rescalings for every anchor).**
For the fixed source of Definition 122.1 define the explicit positive
constants

$$
\begin{gathered}
\ell_{\mathfrak s}=1/\sqrt5,\qquad U_{\mathfrak s}=1,\\
k_{\mathfrak s}=\frac1{C(J_\tau+3)},\qquad
K_{\mathfrak s}=\frac{B_\tau}{c}+k_{\mathfrak s},\\
E_{\mathfrak s}=\min\{1,c,1/k_{\mathfrak s}\}.
\end{gathered}
\tag{123.1}
$$

Uniformly over every $\|h_0\|\le1$ and every
$0<\varepsilon\le E_{\mathfrak s}$, the two original moduli satisfy

$$
\boxed{
\ell_{\mathfrak s}R(k_{\mathfrak s}\varepsilon;A,\eta)
 \le\omega^{\rm all}_{\mathfrak s,h_0}(\varepsilon)
 \le\omega_{\mathfrak s,h_0}(\varepsilon)
 \le U_{\mathfrak s}R(K_{\mathfrak s}\varepsilon;A,\eta).
}
\tag{123.2}
$$

In particular, the constants and the positive error range do not depend
on the anchor, its imaginary axial component, its distance from the
sphere, or the sign of its real axial component.

*Proof.* For every feasible alternative for the finite modulus,
(122.4) gives $Q\le D_0\le\varepsilon/c$.
Lemma 122.3 implies $q_{A,\eta}(\|h-h_0\|)\le B_\tau\varepsilon/c$.
Since $\|h-h_0\|\le2$, the definition of $R$ and its monotonicity
in its first argument prove the last inequality of (123.2).
Inclusion of the full-law constraint in the finite constraint proves
the middle inequality.

For the first inequality put $\delta=k_{\mathfrak s}\varepsilon$
and $r=R(\delta;A,\eta)$. Here $0<\delta\le1$ and
$q_{A,\eta}(r)\le\delta$. Choose $h_r$ from Lemma 122.4 and the
strictly nonzero retention $\gamma_r=\delta$. Its modulus is at most
one. Since both vectors are in the ball, (122.3) and (122.15) give

$$
D_0(\gamma_r,h_r;h_0)
 \le J_\tau\delta+3\delta,
\qquad
d_a(\gamma_r,h_r;h_0)
 \le C(J_\tau+3)\delta=\varepsilon.
\tag{123.3}
$$

Its displacement is at least $r/\sqrt5$, as required.
This also applies when $q_{A,\eta}(r)=0$, including a reflected
zero-law alternative, because $\gamma_r$ remains strictly positive.

To realise these witnesses by full interactions, use Theorem 106.3
for each of the two vectors $z=h_0,h_r$. Explicitly, choose a unit
$a_\perp\in R^\perp\subset H$ and put
$\kappa_z=Bz+\sqrt{1-\|z\|^2}\,a_\perp$. Then
$\|\kappa_z\|=1$. A unitary $T_z:H\longrightarrow\mathcal M^\perp$
with $T_z\kappa_z=\zeta$ gives the completion $\mathsf J_z$ in
(106.2). That one completion serves emission, the forward return and
every history in its hypothesis. The anchor uses retention zero and
the alternative uses $\gamma_r$; the hypotheses may differ in their
completion as allowed in Definition 114.1. At a sphere vector the
square-root term is simply zero. Thus (123.3) is a bound for genuine
full-completion laws with all their original masses, rather than a
compression that requires an interior completion margin.

The linear comparison (122.4) is reused from §118. Its
orbit-pairing intermediate is D'Alessandro,
[*On Quantum State Observability and Measurement*,
arXiv:quant-ph/0307127v1, §2, Theorem 1](https://arxiv.org/pdf/quant-ph/0307127v1),
which characterises one-step indistinguishability by trace pairings
with the conjugation orbit, equivalently the observability space.
The full-completion premise here is exactly §106. Abbott et al.,
[*Communication Through Coherent Control of Quantum Channels*,
arXiv:1810.09826v3, §§4–5, equation (5), and Appendix C](https://arxiv.org/pdf/1810.09826v3),
describe implementation dependence through controlled-path
transformation matrices, and the distinct implementation-independent
full-switch case. Neither interface supplies a different return
operation for the present witnesses. $\square$

**Proposition 123.2 (Separated regimes and the uncollapsed window).**
Abbreviate $\ell=\ell_{\mathfrak s}$, $k=k_{\mathfrak s}$,
$K=K_{\mathfrak s}$, and put

$$
F(\varepsilon,\eta)=\frac{\varepsilon}{\eta+\sqrt\varepsilon},
\qquad T(\varepsilon;A,\eta)=\min\{2,A+F(\varepsilon,\eta)\}.
\tag{123.4}
$$

If $A\eta>0$ and
$0<\varepsilon<2A\eta/K$, also with
$\varepsilon\le E_{\mathfrak s}$, then

$$
\frac{\ell k\varepsilon}{\eta+2A}
 \le\omega^{\rm all}_{\mathfrak s,h_0}(\varepsilon)
 \le\omega_{\mathfrak s,h_0}(\varepsilon)
 \le\frac{2K\varepsilon}{\eta+2A}.
\tag{123.5}
$$

If $2A\eta/k\le\varepsilon\le E_{\mathfrak s}$, then

$$
\begin{aligned}
\frac\ell2\min\{1,k,\sqrt k\}\,T(\varepsilon;A,\eta)
 &\le\omega^{\rm all}_{\mathfrak s,h_0}(\varepsilon)\\
 &\le\omega_{\mathfrak s,h_0}(\varepsilon)
 \le2\max\{1,K,\sqrt K\}\,T(\varepsilon;A,\eta).
\end{aligned}
\tag{123.6}
$$

Thus the local and post-reflection estimates are separated by the
explicit closed window

$$
\left[\frac{2A\eta}{K},\frac{2A\eta}{k}\right]
 \cap(0,E_{\mathfrak s}],
\tag{123.7}
$$

where (123.2) with the exact formula (122.6) applies. Endpoints are
retained as written: the local assertion is strict, while the
post-reflection assertion includes its entry endpoint. If a regime
does not meet the common error range it makes no additional assertion.

*Proof.* On $0\le\delta<2A\eta$, let $R=R(\delta;A,\eta)$.
The smaller root in (122.6) is at most $(\eta+2A)/2$ and satisfies
$\delta=R(\eta+2A-R)$. Therefore

$$
\frac\delta{\eta+2A}\le R
 \le\frac{2\delta}{\eta+2A}.
\tag{123.8}
$$

Since $K>k$, applying (123.8) at $k\varepsilon$ and
$K\varepsilon$ in (123.2) proves (123.5).

For $\delta\ge2A\eta$, let $p\ge2A$ be the uncapped root in
the second line of (122.6), so $R=\min\{2,p\}$. Put
$g=(\sqrt{\eta^2+4\delta}-\eta)/2$. The equation
$\delta=p(p+\eta-2A)$ implies $p\ge g$, and also
$p\le2A+g$, since writing $p=2A+z$ gives
$\delta=(2A+z)(\eta+z)\ge z(\eta+z)$.
Rationalisation of $g$ gives

$$
F(\delta,\eta)\le g\le2F(\delta,\eta).
\tag{123.9}
$$

For the first inequality use
$\sqrt{\eta^2+4\delta}\le\eta+2\sqrt\delta$; for the second
use $\sqrt{\eta^2+4\delta}\ge\sqrt\delta$. Thus
$p\ge\max\{2A,F(\delta,\eta)\}\ge(A+F(\delta,\eta))/2$ and
$p\le2(A+F(\delta,\eta))$. Capping preserves the bounds

$$
\tfrac12 T(\delta;A,\eta)\le R(\delta;A,\eta)
 \le2T(\delta;A,\eta).
\tag{123.10}
$$

For any $b>0$ and $\varepsilon>0$,

$$
\min\{b,\sqrt b\}F(\varepsilon,\eta)
 \le F(b\varepsilon,\eta)
 \le\max\{b,\sqrt b\}F(\varepsilon,\eta).
\tag{123.11}
$$

Indeed the ratio is
$b(\eta+\sqrt\varepsilon)/(\eta+\sqrt b\sqrt\varepsilon)$,
between $b$ and $\sqrt b$. Addition of $A$ and capping at $2$
give the same comparison with factors enlarged to include $1$.
Under the hypothesis of (123.6), both rescaled errors lie at or above
$2A\eta$. Equations (123.2), (123.10) and (123.11) now prove (123.6).
The interval (123.7) is precisely what these two separated
applications leave between them. $\square$

**Proposition 123.3 (Axial limits and the restricted-family consistency).**
If $\eta=0$ and $A>0$, both original moduli obey

$$
\lim_{\varepsilon\downarrow0}
 \omega^{\rm all}_{\mathfrak s,h_0}(\varepsilon)
 =\lim_{\varepsilon\downarrow0}
 \omega_{\mathfrak s,h_0}(\varepsilon)=2A.
\tag{123.12}
$$

This includes all allowed $\beta$, either sign of $a$, and
$A^2+\beta^2=1$. At $A=0$, the profile reduces to the positive
inverse of $r\mapsto r(\eta+r)$, capped at $2$, so (123.2) has
the same small-error order as the already proved Theorem 121.2.
In particular, that theorem supplies the $F(\varepsilon,\eta)$
specialisation, including zero, every imaginary axial anchor and its
two sphere endpoints. Every sphere anchor with $A>0$ is covered by
(123.2) and (123.5)–(123.7), according to its values of $A,\eta$.

*Proof.* For $\eta=0$, Proposition 120.2 identifies the sole distinct
zero-law alternative as $h_* =(-a+\mathrm i\beta)e$, at distance
$2A$. Its outer and skew matrices agree with those of $h_0$.
Taking any sufficiently small positive $\gamma$ gives
$D_0(\gamma,h_*;h_0)=\gamma(1+2A)$, so (122.4) yields
$\omega^{\rm all}(\varepsilon)\ge2A$ for every sufficiently
small positive $\varepsilon$.

For the reverse limiting inequality, if it failed for either modulus,
there would be $\varepsilon_n\downarrow0$ and feasible alternatives
with distances greater than $2A+u$ for some $u>0$. This uses only
the definition of supremum, not attainment. Compactness of the
closed parameter domain gives a subsequential limit $(\gamma_*,h_*)$.
By (122.4), $D_0\to0$, so $\gamma_*=0$ and the two matrix
coordinates agree with those of $h_0$. Proposition 120.2 makes
$h_*$ either $h_0$ or its reflection, contradicting the distance
bound. This proves (123.12).

The assertion at $A=0$ follows by substituting $A=0$ in (122.6).
The comparison with $F$ and all of its stated special cases are
Theorem 121.2, used as a consistency consequence rather than a further
claim of new restricted-family content. The complete sphere coverage
follows from the anchor quantifier in Theorem 123.1 and the
ball-preserving construction (122.16). $\square$

## 124. Actual-law branch entry and the obstruction to continuous comparison

**Definition 124.1 (The actual reflection-side entry threshold).**
Keep the fixed source, finite vector and raw law errors of
Definition 122.1. For an anchor with $A>0$, $\eta>0$, put
$\sigma=\operatorname{sgn}(a)$ and define the closed reflection side

$$
\mathcal B_{h_0}
 =\{h:\|h\|\le1,\ \sigma\operatorname{Re}(e^\dagger h)\le0\}.
\tag{124.1}
$$

For $j=f,a$ define

$$
\begin{aligned}
\mu_j(h_0)
 &=\min_{|\gamma|\le1,\ h\in\mathcal B_{h_0}}
                              d_j(\gamma,h;h_0),\\
\mu_j^+(h_0)
 &=\inf_{0<|\gamma|\le1,\ h\in\mathcal B_{h_0}}
                              d_j(\gamma,h;h_0).
\end{aligned}
\tag{124.2}
$$

The first expression is an auxiliary compact-domain minimum, with
zero retention included; the second retains exactly the punctured
retention constraint in the original modulus. Both evaluate actual
laws, rather than the scalar profile. The minimum and the equality
of these two thresholds are justified in Theorem 124.2.

**Theorem 124.2 (Source-only entry bounds and punctured one-sided laws).**
For every $A,\eta>0$ anchor in the closed ball, both thresholds in
(124.2) are well defined and

$$
\begin{gathered}
\mu_f=\mu_f^+\le\mu_a=\mu_a^+,\\
\alpha_{\mathfrak s} A\eta\le\mu_j(h_0)
 \le\beta_{\mathfrak s} A\eta,\qquad j=f,a,\\
\alpha_{\mathfrak s}=\frac{c}{1+2/\tau}>0,
\qquad \beta_{\mathfrak s}=2\sqrt2\,C>0.
\end{gathered}
\tag{124.3}
$$

For each $j$ there is no nonzero-retention reflection-side alternative
at error $\varepsilon<\mu_j$, and at every
$\varepsilon>\mu_j$ there is such an alternative. At equality,
entry occurs if and only if an auxiliary minimiser has nonzero
retention; an auxiliary minimiser at zero retention alone does not
assert entry at equality.

Let $\Omega_f=\omega_{\mathfrak s,h_0}$ and
$\Omega_a=\omega^{\rm all}_{\mathfrak s,h_0}$. With

$$
J_0=1+1/\tau,\qquad J_1=J_0+d_\tau=1+5/(2\tau),
\qquad L_{\mathfrak s}=J_1\beta_{\mathfrak s}/c,
\tag{124.4}
$$

the following one-sided estimates hold for the original moduli:

$$
\begin{aligned}
0<\varepsilon<\mu_j:quad
 &\Omega_j(\varepsilon)
       \le\frac{J_1\varepsilon}{cA}
       \le L_{\mathfrak s}\eta,\\
\varepsilon>\mu_j:quad
 &\Omega_j(\varepsilon)\ge A.
\end{aligned}
\tag{124.5}
$$

In particular,
$\limsup_{\varepsilon\uparrow\mu_j}\Omega_j(\varepsilon)
 \le L_{\mathfrak s}\eta$ and
$\liminf_{\varepsilon\downarrow\mu_j,\,\varepsilon>\mu_j}
 \Omega_j(\varepsilon)\ge A$.
No exact numerical coefficient for either raw-law threshold is asserted.

*Proof.* Both error functions in (122.2) are continuous on the closed
parameter domain. For $d_f$ this follows from its finite continuous
coordinates. For $d_a$, the difference between its values at two
alternatives is at most their full-law distance, by the triangle
inequality in every actual coordinate followed by the supremum.
The upper comparison in Theorem 118.3 makes that distance tend to
zero when the parameters converge: all four terms in $\mathcal D$
of (118.1) then tend to zero. This proves continuity without assuming
that a history attains the full-law supremum.

The set $\{|\gamma|\le1\}\times\mathcal B_{h_0}$ is nonempty
and compact, so the auxiliary minima are attained. If a minimiser
has $\gamma=0$, keep its same $h$ and take nonzero
$\gamma_n\to0$. Continuity gives errors converging to the minimum.
If its retention is nonzero it already belongs to the punctured set.
In either case $\mu_j^+=\mu_j$. Since $d_f\le d_a$, minimising
on the same compact set gives $\mu_f\le\mu_a$.

For the lower bound in (124.3), every $h\in\mathcal B_{h_0}$ has
$\|h-h_0\|\ge A$. The established off-axis inversion (120.15)
gives, using $\eta\le1$,

$$
\|h-h_0\|
 \le\left[\frac1\tau+\frac{1+1/\tau}{\eta}\right]Q(h;h_0)
 \le\frac{1+2/\tau}{\eta}Q(h;h_0).
\tag{124.6}
$$

Together with $d_j\ge cD_0\ge cQ$, this proves the claimed
positive lower bound for each minimum.

For the upper bound use the actual reflected vector

$$
h_\#=(-a+\mathrm i\beta)e+v_0.
\tag{124.7}
$$

It has the same norm as $h_0$ and belongs to $\mathcal B_{h_0}$.
The skew matrices agree and

$$
h_\#h_\#^\dagger-h_0h_0^\dagger
 =-2a(ev_0^\dagger+v_0e^\dagger),\qquad
Q(h_\#;h_0)=2\sqrt2 A\eta.
\tag{124.8}
$$

At retention zero, (122.4) therefore gives
$d_j(0,h_\#;h_0)\le\beta_{\mathfrak s}A\eta$.
This proves the upper bound by a concrete actual-law comparison.
Theorem 106.3 realises $h_\#$, just as it realises every vector
in the compact minimisation, by one fixed full completion per
hypothesis; the construction in Theorem 123.1 applies at the sphere
as well.

The definition of the infimum excludes all punctured reflection-side
alternatives below $\mu_j$. If $\varepsilon>\mu_j$, its equality
with the punctured infimum supplies one with error strictly less
than $\varepsilon$. At $\varepsilon=\mu_j$, any such alternative
is itself an auxiliary minimiser, and a nonzero auxiliary minimiser
conversely supplies one. This proves the exact equality qualification;
it does not assume punctured attainment.

It remains to prove the one-sided modulus bounds directly from the
law geometry. Write an alternative as
$h=(u+\mathrm i b)e+v$, with $u,b$ real. If $D=D_0(\gamma,h;h_0)$,
the same skew entries as in (122.12), and then the axial
outer-product entry, give

$$
\|v-v_0\|\le D/\tau,\qquad
|b-\beta|\le D/(2\tau),\qquad
|u^2-A^2|\le J_0D.
\tag{124.9}
$$

For the last inequality use
$|u^2+b^2-A^2-\beta^2|\le D$ and
$|b^2-\beta^2|\le2|b-\beta|$, since $|b|,|\beta|\le1$.
If $\sigma u>0$, then

$$
|u-a|=\frac{|u^2-A^2|}{|u|+A}\le J_0D/A,
\qquad \|h-h_0\|\le J_1D/A.
\tag{124.10}
$$

Here the remaining components have norm at most $d_\tau D$, and
$A\le1$. If $\varepsilon<\mu_j$, every feasible alternative
has $\sigma u>0$ by the entry definition. Equation (122.4) gives
$D\le\varepsilon/c$, proving the first bound in (124.5) after
taking the supremum. Substituting
$\varepsilon<\mu_j\le\beta_{\mathfrak s}A\eta$ proves its
second bound. Above $\mu_j$, the already supplied punctured
reflection-side alternative has displacement at least $A$, proving
the other line of (124.5) and both stated one-sided limits.

The calculation additionally locates the other branch: if
$\sigma u\le0$, division by $|u|+A$ in (124.9) gives
$|u+a|\le J_0D/A$, including $u=0$. Thus every such alternative
satisfies

$$
\|h-h_\#\|\le J_1D/A,
\qquad
\bigl|\|h-h_0\|-2A\bigr|\le J_1D/A.
\tag{124.11}
$$

For $\eta/A$ small, (124.10) and (124.11) separate the local and
reflected components near the actual threshold. This is an estimate
for the actual finite and full raw-law feasible sets. The threshold
proof did not infer their entry from the scalar jump in (122.8).
$\square$

**Theorem 124.3 (No continuous-in-error uniform multiplicative family).**
Fix any allowed source. For either choice $j=f$ or $j=a$, there do
not exist constants $m,M,E>0$ and functions

$$
f_{h_0}:(0,E]\longrightarrow(0,\infty),
\quad\text{continuous in their error argument},
\tag{124.12}
$$

one for every singleton anchor $\|h_0\|\le1$, such that

$$
mf_{h_0}(\varepsilon)
 \le\Omega_{j,h_0}(\varepsilon)
 \le Mf_{h_0}(\varepsilon)
\quad(0<\varepsilon\le E)
\tag{124.13}
$$

holds simultaneously for all these anchors. The functions may depend
on the entire anchor, with no regularity required in that dependence.
The conclusion therefore also excludes a single such family comparable
to both original moduli on a common positive error range.

*Proof.* Fix a unit vector $f\perp e$, set $A_0=1/2$, and choose
any sequence $\eta_n>0$ tending to zero with
$A_0^2+\eta_n^2\le1$. The anchors

$$
h_{0,n}=A_0 e+\eta_n f
\tag{124.14}
$$

are singleton anchors by Proposition 120.2. For each of the two
choices of $j$, Theorem 124.2 gives actual-law thresholds
$0<\mu_{j,n}\le\beta_{\mathfrak s}A_0\eta_n\to0$.
In particular, eventually $\mu_{j,n}$ lies strictly inside $(0,E)$.
For $0<\varepsilon<\mu_{j,n}$, (124.5) and the first inequality
in (124.13) imply

$$
f_{h_{0,n}}(\varepsilon)\le L_{\mathfrak s}\eta_n/m.
\tag{124.15}
$$

For $\mu_{j,n}<\varepsilon\le E$, the other lines of (124.5)
and (124.13) imply

$$
f_{h_{0,n}}(\varepsilon)\ge A_0/M.
\tag{124.16}
$$

Continuity at the positive error $\mu_{j,n}$ forces
$A_0/M\le L_{\mathfrak s}\eta_n/m$. This is impossible for
large $n$. The argument uses only strict inequalities on the two
sides of the threshold; no value or attainment assertion at the
threshold is needed. It applies separately to the finite modulus
and to the full raw-law modulus, with their respective thresholds.

For the comparison with affine retrieval, Gao–Sun–Wang–Xu,
[*Phase Retrieval From the Magnitudes of Affine Linear Measurements*,
arXiv:1608.06117v1, Theorems 3.1 and 4.1](https://arxiv.org/pdf/1608.06117v1),
assume global affine injectivity; Theorem 3.1 equivalently requires
full real Jacobian rank everywhere in the complex signal space,
and Theorem 4.1 gives compact-set Lipschitz comparisons under that
hypothesis. Zhuang,
[*On stability of generalized phase retrieval and generalized affine
phase retrieval*, Theorem 2.3 and Theorem 3.1](https://doi.org/10.1186/s13660-019-1968-z),
gives the real generalized quadratic product-distance comparison
under generalized phase retrievability and the real generalized
affine injectivity/Jacobian criterion, respectively. Those hypotheses
do not remove the reflected zero-retention fibers (114.7) of this
source. Balan–Zou's local bounds cited in Definition 122.1 are also
bounds for their phase-retrievable quotient interface. Here a
reflected fiber is approached by off-axis singleton anchors, and
(124.15)–(124.16) concern entry of a remote component into each
actual raw-law error ball.

All conclusions keep one fixed source and concern exact laws and
the terminal-relevant vector $h$. They assert neither a sampling
guarantee nor identification of an entire completion unitary.
The constants and the retained decoder length need not be uniform
over sources. The common-error obstruction (124.13) is compatible
with the two different horizontal error rescalings in (123.2).
$\square$

## 追加锚（本行以下为增补区）
