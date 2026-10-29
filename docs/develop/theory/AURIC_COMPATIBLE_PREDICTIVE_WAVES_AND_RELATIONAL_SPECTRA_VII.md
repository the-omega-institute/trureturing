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

## 125. The literal reflected tangent rows

**Definition 125.1 (Source-specific eight-real-variable coefficients; repo-derived).**
Fix one allowed source of Definition 114.1, once and for all, and fix
$0<A<1$ and a complex unit vector $f\perp e=t/\tau$, where
$\tau=\|t\|>0$. The anchor, limiting reflected point and reflected
comparison curve are

$$
h_0(\eta)=Ae+\eta f,\qquad h_-=-Ae,\qquad
h_\#(\eta)=-Ae+\eta f.
\tag{125.1}
$$

Write $c_\theta=\cos\theta$, $s_\theta=\sin\theta$, and retain the
source's $b,D,W,r_i,Q_w,a_w$ without changing their meanings. In
particular $r_i$ is subnormalised and $a_w=2^{-k(w)}$ is the
original mass. Let $q_\rho=q_{i,w}$, $\rho=(i,w)$, be exactly the
real functional (116.2), with (116.1). Keep the particular finite
length $L_{\mathfrak s}$ chosen in Proposition 118.2 and set

$$
\mathscr R_f=\{(i,w):1\le i\le9,\ |w|\le L_{\mathfrak s}\},
\qquad
\mathscr R_a=\{(i,w):1\le i\le9,\ w\text{ any finite actual history}\}.
\tag{125.2}
$$

For $z\in\mathbb C^3$ and $g\in\mathbb C$ define

$$
\begin{aligned}
H(z)&=-A(ez^\dagger+ze^\dagger),\\
S(z)&=\mathrm i\tau(ze^\dagger-ez^\dagger),\\
H_1(z)&=H(z)+H(f),\qquad S_1(z)=S(z)-S(f),\\
K_-&=K_{h_-}=-A\tau ee^\dagger
       +\mathrm i s_\theta c_\theta(D-bA^2ee^\dagger),\\
X_1(z)&=s_\theta^2bH_1(z)+s_\theta c_\theta S_1(z),\\
Y_1(z)&=c_\theta^2bH_1(z)-s_\theta c_\theta S_1(z),\\
\ell_\rho(z,g)&=q_\rho(X_1(z),Y_1(z),gK_-),\\
\mathcal F_j(z,g)&=\sup_{\rho\in\mathscr R_j}|\ell_\rho(z,g)|,
                  \qquad j=f,a.
\end{aligned}
\tag{125.3}
$$

The supremum for $j=f$ is a maximum. To specify all eight real
columns explicitly, choose a unit $k$ making $(e,f,k)$ a complex
orthonormal basis, put
$(v_1,\ldots,v_6)=(e,\mathrm i e,f,\mathrm i f,k,\mathrm i k)$,
and write $z=\sum_{r=1}^6x_rv_r$, $g=y_1+\mathrm i y_2$.
Then

$$
\begin{aligned}
\beta_\rho&=q_\rho\bigl(
 s_\theta^2bH(f)-s_\theta c_\theta S(f),
 c_\theta^2bH(f)+s_\theta c_\theta S(f),0\bigr),\\
U_{\rho r}&=q_\rho\bigl(
 s_\theta^2bH(v_r)+s_\theta c_\theta S(v_r),
 c_\theta^2bH(v_r)-s_\theta c_\theta S(v_r),0\bigr),\\
(V_{\rho1},V_{\rho2})
 &=\bigl(q_\rho(0,0,K_-),q_\rho(0,0,\mathrm iK_-)\bigr),\\
\ell_\rho(z,g)&=\beta_\rho+U_\rho\cdot x+V_\rho\cdot y.
\end{aligned}
\tag{125.4}
$$

Thus every coefficient contains the literal factor $a_w/2$ and
trace pairing with the literal $r_i$. The outcome-$0$ difference is
the negative of the outcome-$1$ difference, so (125.2) retains both
original error norms exactly. Define, initially as infima,

$$
m_j=\inf_{z\in\mathbb C^3,\ g\in\mathbb C}\mathcal F_j(z,g),
\qquad
n_j=\inf_{z\in\mathbb C^3}\mathcal F_j(z,0),
\qquad \delta_j=n_j-m_j.
\tag{125.5}
$$

The zero-retention coefficient is the restriction of the same affine
rows, not a separately chosen approximation. The complex variable $g$
has both real coordinates free. These definitions use the completion
vector only as in Theorem 106.3: each admissible vector is realised by
one full ten-dimensional completion shared by emission, the single
forward return and every history of its hypothesis. Compared hypotheses
may have different completions. The rows add no preparation, repetition,
selection, record phase, menu entry, clock or schedule.

**Lemma 125.2 (Uniform expansion of the actual rows).**
For radii $R>0$, $G\ge0$, put

$$
\begin{aligned}
R_{\mathfrak s}&=\max_i\|r_i\|_{\rm HS},\qquad
k_A=\tau+2|s_\theta c_\theta|bA,\\
\mathcal E(R,G)&=\frac{R_{\mathfrak s}}2
 \left[b(R^2+1)+2G\left(k_AR+|s_\theta c_\theta|bR^2\right)\right].
\end{aligned}
\tag{125.6}
$$

If $0<\eta\le1$, $\|z\|\le R$, $|g|\le G$, and
$(\eta g,-Ae+\eta z),(0,h_0(\eta))$ belong to $\mathcal P$, then,
for each $j=f,a$,

$$
\left|d_j(\eta g,-Ae+\eta z;h_0(\eta))
                         -\eta\mathcal F_j(z,g)\right|
 \le\mathcal E(R,G)\eta^2.
\tag{125.7}
$$

*Proof.* Use the exact blocks (114.2) and paired lift (118.9).
The unscaled outer-product and skew differences are exactly

$$
\begin{aligned}
\mathsf H_{-Ae+\eta z}-\mathsf H_{Ae+\eta f}
 &=\eta H_1(z)+\eta^2(zz^\dagger-ff^\dagger),\\
\mathsf S_{-Ae+\eta z}-\mathsf S_{Ae+\eta f}
 &=\eta S_1(z).
\end{aligned}
\tag{125.8}
$$

Also the exact quadratic expansion of the cross block is

$$
\begin{aligned}
K_{-Ae+\eta z}&=K_-+\eta K_1(z)+\eta^2K_2(z),\\
K_1(z)&=\tau(s_\theta^2ez^\dagger+c_\theta^2ze^\dagger)
           +\mathrm i s_\theta c_\theta bA(ez^\dagger+ze^\dagger),\\
K_2(z)&=-\mathrm i s_\theta c_\theta bzz^\dagger,\\
\|K_1(z)\|_{\rm HS}&\le k_A\|z\|,\qquad
\|K_2(z)\|_{\rm HS}\le|s_\theta c_\theta|b\|z\|^2.
\end{aligned}
\tag{125.9}
$$

If $(X,Y,Z)$ is the exact paired lift against $(0,h_0(\eta))$,
then $Z=\eta gK_{-Ae+\eta z}$ and (125.8) gives

$$
\begin{aligned}
\|X-\eta X_1\|_{\rm HS}+\|Y-\eta Y_1\|_{\rm HS}
 &\le b\eta^2(R^2+1),\\
\|Z-\eta gK_-\|_{\rm HS}
 &\le\eta^2G(k_AR+|s_\theta c_\theta|bR^2).
\end{aligned}
\tag{125.10}
$$

For every actual row separately, unitary invariance and the trace
Cauchy–Schwarz inequality give

$$
\begin{aligned}
&|q_{i,w}(X,Y,Z)-\eta\ell_{i,w}(z,g)|\\
&\quad\le\frac{a_w}{2}\|r_i\|_{\rm HS}
 \bigl(\|X-\eta X_1\|_{\rm HS}+\|Y-\eta Y_1\|_{\rm HS}
                  +2\|Z-\eta gK_-\|_{\rm HS}\bigr)\\
&\quad\le\mathcal E(R,G)\eta^2.
\end{aligned}
\tag{125.11}
$$

The last inequality uses $a_w\le1$ only to obtain one common bound;
the row on its left still has its original weight. The outcome-$0$
identity following (114.3) gives the same bound for that label.
The difference of two suprema of absolute values is at most the
supremum of the absolute coordinate differences. Applying this fact
to the finite set and, separately, to all actual histories proves
(125.7). No history need attain the latter supremum. $\square$

## 126. Positive coefficients and quadratic threshold remainders

**Theorem 126.1 (Coercivity and minimisers of both tangent problems; repo-derived).**
Let $\underline c=c_{\mathfrak s}>0$, $\overline C=C_{\mathfrak s}>0$
be the constants fixed in Definition 122.1, and retain
$J_1=1+5/(2\tau)$ and $\alpha_{\mathfrak s}$ from (124.3)–(124.4).
For each $j=f,a$, $\mathcal F_j$ is finite, continuous and convex,
and is coercive on the underlying eight-dimensional real space.
Its restriction $\mathcal F_j(z,0)$ is coercive on the underlying
six-dimensional real space. More explicitly, for every $z,g$,

$$
\mathcal F_j(z,g)\ge
\max\left\{\alpha_{\mathfrak s}A,
 \frac{A\underline c}{J_1}\|z-f\|,
 \underline c(1+2A)|g|\right\}.
\tag{126.1}
$$

Both infima in (125.5) are attained, with

$$
0<\alpha_{\mathfrak s}A\le m_j\le n_j\le M,
\qquad M=2\sqrt2\,\overline C A,
\qquad m_f\le m_a,\quad n_f\le n_a.
\tag{126.2}
$$

Set the explicit positive bounds

$$
R=1+\frac{J_1M}{A\underline c},\qquad G=\frac M{\underline c}.
\tag{126.3}
$$

Every minimiser of either coefficient problem satisfies $\|z\|\le R$;
every unrestricted minimiser additionally satisfies $|g|\le G$.

*Proof.* The row bound used in (125.11), now applied to the affine
rows themselves, proves finiteness. It also gives, for either norm,

$$
\begin{aligned}
|\mathcal F_j(z,g)-\mathcal F_j(z',g')|
 &\le R_{\mathfrak s}(Ab+2|s_\theta c_\theta|\tau)\|z-z'\|
             +R_{\mathfrak s}\|K_-\|_{\rm HS}|g-g'|.
\end{aligned}
\tag{126.4}
$$

Thus continuity holds even for the full-history supremum. Convexity
follows because each absolute affine row is convex.

For arbitrary fixed $z,g$, the strict interior condition $0<A<1$
makes $(\eta g,-Ae+\eta z)$ a reflection-side admissible pair and
$h_0(\eta)$ an admissible anchor for all sufficiently small positive
$\eta$. Lemma 125.2 shows $d_j/\eta\to\mathcal F_j(z,g)$.
On the same curve (122.3) gives the exact limit

$$
\frac{D_0(\eta g,-Ae+\eta z;h_0(\eta))}{\eta}
 \longrightarrow T(z,g):=
 \|H_1(z)\|_{\rm HS}+\|S_1(z)\|_{\rm HS}+(1+2A)|g|.
\tag{126.5}
$$

Consequently (122.4) implies
$\underline cT\le\mathcal F_j\le\overline CT$.
In (124.11), $h-h_\#=\eta(z-f)$. Dividing that inequality by
$\eta$ and taking the limit yields
$\|z-f\|\le J_1T/A\le J_1\mathcal F_j/(A\underline c)$.
This proves the second and third bounds in (126.1).
Every point on this curve has $d_j\ge\mu_j(h_0(\eta))$;
the lower bound (124.3), divided by $\eta$ and passed to the limit,
proves its first bound.

The second and third bounds make all sublevel sets bounded;
continuity makes them closed. Hence the two infima are minima.
At the common trial $(z,g)=(f,0)$ one has $S_1=0$ and
$H_1=-2A(ef^\dagger+fe^\dagger)$ of Hilbert–Schmidt norm
$2\sqrt2 A$. Thus $\mathcal F_j(f,0)\le M$ by (126.5).
This proves the upper bound in (126.2), and restriction to $g=0$
proves $m_j\le n_j$. The inclusion $\mathscr R_f\subset\mathscr R_a$
proves both inequalities between the two norms' minima.
Finally (126.1), at any of these minimisers with value at most $M$,
gives (126.3) by $\|z\|\le1+\|z-f\|$. $\square$

**Definition 126.2 (Zero-retention minimum on the same reflection side).**
Keep $\mu_j$ exactly as in (124.1)–(124.2), and only abbreviate
$\mu_j(\eta)=\mu_j(h_0(\eta))$. Define its zero-retention restriction
by

$$
\nu_j(\eta)=\min_{h\in\mathcal B_{h_0(\eta)}}
                        d_j(0,h;h_0(\eta)),\qquad j=f,a.
\tag{126.6}
$$

In particular the compact threshold $\mu_j$ still minimises the
original nonlinear raw-law error over the full complex retention disk;
it has not been replaced by $D_0$, $T$, or a tangent norm.

**Theorem 126.3 (The original finite and full thresholds to first order; repo-derived).**
With $R,G$ from (126.3), let

$$
E=\mathcal E(R,G)>0,\qquad
\eta_* =\min\left\{1,\frac A{2R},\frac{1-A}{2R},\frac1{2G}\right\}>0.
\tag{126.7}
$$

For every $0<\eta\le\eta_*$, both minima in (126.6) exist and are
positive, and the four explicit error bounds are

$$
\begin{aligned}
|\mu_f(\eta)-\eta m_f|&\le E\eta^2,&
|\nu_f(\eta)-\eta n_f|&\le E\eta^2,\\
|\mu_a(\eta)-\eta m_a|&\le E\eta^2,&
|\nu_a(\eta)-\eta n_a|&\le E\eta^2.
\end{aligned}
\tag{126.8}
$$

Every compact $\mu_j$ minimiser, and every $\nu_j$ minimiser with
retention set to zero, has the form

$$
h=-Ae+\eta z,\qquad \gamma=\eta g,\qquad
\|z\|\le R,\quad |g|\le G.
\tag{126.9}
$$

All these statements hold for each fixed source, $A$ and $f$ as
quantified in Definition 125.1; no uniform assertion as $A\to0$ or
$A\to1$ is made.

*Proof.* The anchor and $h_\#(\eta)$ are in the unit ball on the
stated interval. Continuity of $d_j$ and compactness, already established
in Theorem 124.2, prove existence for $\nu_j$ as well as $\mu_j$.
The same reflected trial as in (124.8) gives

$$
\alpha_{\mathfrak s}A\eta\le\mu_j(\eta)
 \le\nu_j(\eta)\le d_j(0,h_\#(\eta);h_0(\eta))\le M\eta.
\tag{126.10}
$$

In particular both minima are positive. For any minimiser of either
problem, (122.4) gives $D_0\le M\eta/\underline c$.
The actual branch localisation (124.11) then gives

$$
\|h-h_\#(\eta)\|
 \le\frac{J_1M\eta}{A\underline c},\qquad
|\gamma|\le\frac{M\eta}{\underline c}.
\tag{126.11}
$$

Writing $h=-Ae+\eta z$ proves (126.9) for every minimiser.
This step does not select a favourable subsequence or a favourable
minimiser.

Conversely, every coefficient minimiser in Theorem 126.1 lifts to
an admissible reflection-side point on the entire interval (126.7):

$$
\|-Ae+\eta z\|\le A+\eta R\le\frac{1+A}2<1,\qquad
\operatorname{Re}(e^\dagger(-Ae+\eta z))\le-A+\eta R\le-A/2,
\qquad |\eta g|\le1/2.
\tag{126.12}
$$

The anchor obeys $\|h_0(\eta)\|\le A+\eta\le(1+A)/2<1$ as well.
For an unrestricted coefficient minimiser, (125.7) and (126.12)
therefore give $\mu_j\le\eta m_j+E\eta^2$.
For a nonlinear compact minimiser, (126.9) and (125.7) instead give
$\mu_j\ge\eta\mathcal F_j(z,g)-E\eta^2\ge\eta m_j-E\eta^2$.
These prove the two $\mu_j$ bounds. Applying the same two arguments
with $g=0$ throughout proves the two $\nu_j$ bounds.
The uniform estimate (125.11) applies to every actual history, so
this proof of the full-law bounds uses its own supremum and does not
assert that the finite decoder is an exact norming set for it.
Every lift is realised by the one-completion construction of Theorem
106.3, with its original emission and single forward return. $\square$

## 127. A strict coefficient gap forces every compact minimiser into the puncture

**Theorem 127.1 (Quantitative entry at the actual threshold; repo-derived).**
Fix $j=f$ or $j=a$, with that norm's coefficients in (125.5).
Suppose a number $\Delta>0$ satisfies $\delta_j\ge\Delta$.
Keep $M,E,\eta_*$ from §126 and put

$$
\begin{aligned}
K_*&=\tau+|s_\theta c_\theta|(\|D\|_{\rm HS}+b),\qquad
L=R_{\mathfrak s}K_*>0,\\
\eta_\Delta&=\min\{\eta_*,\Delta/(4E)\}>0.
\end{aligned}
\tag{127.1}
$$

For every $0<\eta\le\eta_\Delta$ and every compact minimiser
$(\gamma,h)$ of the unchanged $\mu_j(\eta)$,

$$
\begin{gathered}
\nu_j(\eta)-\mu_j(\eta)\ge\tfrac12\Delta\eta>0,\\
\boxed{\quad
\frac{\Delta}{2L}\eta\le|\gamma|
 \le\frac{M-3\Delta/4}{\underline c}\eta\le G\eta.
\quad}
\end{gathered}
\tag{127.2}
$$

The two linear bounds have strictly positive coefficients.
In particular, every compact minimiser belongs to the original
punctured reflection side, and entry there occurs at exactly
$\varepsilon=\mu_j(\eta)$, including that endpoint. One may take
$\Delta=\delta_j$ whenever that strict gap is known. The hypothesis
belongs separately to each norm.

*Proof.* By (126.8),

$$
\nu_j-\mu_j\ge\eta(n_j-m_j)-2E\eta^2
 \ge\eta(\Delta-2E\eta)\ge\tfrac12\Delta\eta.
\tag{127.3}
$$

For every fixed $\|h\|\le1$, the exact difference between the laws
at $(\gamma,h)$ and $(0,h)$ has paired lift $(0,0,\gamma K_h)$.
The bound $\|K_h\|_{\rm HS}\le K_*$ in (118.19) gives, in each
actual coordinate, magnitude at most $a_w\|r_i\|_{\rm HS}K_*|\gamma|$.
Thus for either original norm the triangle inequality yields

$$
d_j(0,h;h_0)\le d_j(\gamma,h;h_0)+L|\gamma|.
\tag{127.4}
$$

At any compact minimiser $h$ is on the same reflection side used
in (126.6), so $\nu_j\le\mu_j+L|\gamma|$.
Combine this with (127.3) to prove the lower retention bound for
every minimiser. For the upper bound use
$|\gamma|\le D_0\le\mu_j/\underline c$ and

$$
\mu_j\le\eta(m_j+E\eta)
 \le\eta(n_j-\Delta+\Delta/4)
 \le\eta(M-3\Delta/4).
\tag{127.5}
$$

Since $0<\Delta\le\delta_j=n_j-m_j<M$, the upper coefficient is
positive. The lower one is positive since $L>0$.
The nonzero minimiser, with its one fixed full completion, is an
actual admissible alternative at error $\mu_j$. Below $\mu_j$
no reflection-side alternative exists by Theorem 124.2. Its equality
characterisation now proves the stated exact endpoint entry. $\square$

Theorems 126.1 and 126.3 do not assume a strict gap. If
$\delta_j=0$, they still give both original nonlinear thresholds to
first order, but finite-$\eta$ nonzero-retention attainment at
$\varepsilon=\mu_j(\eta)$ remains unresolved by these results.
Indeed $0\le\nu_j-\mu_j\le2E\eta^2$ in that case, and (127.4)
provides no positive linear retention lower bound. Retention of size
$o(\eta)$ is not excluded, nor is a zero-retention compact minimiser.

## 128. Signed actual-row lower witnesses paired with trial upper witnesses

**Proposition 128.1 (A sufficient checkable gap certificate; repo-derived).**
Fix one of the two row families $\mathscr R_j$ in (125.2). Choose
finitely many actual rows $\rho_1,\ldots,\rho_q\in\mathscr R_j$,
signs $\sigma_l\in\{-1,1\}$ and weights $\lambda_l\ge0$ such that

$$
\sum_{l=1}^q\lambda_l=1,\qquad
\sum_{l=1}^q\lambda_l\sigma_lU_{\rho_l r}=0
                    \quad(1\le r\le6).
\tag{128.1}
$$

Let $B=\sum_l\lambda_l\sigma_l\beta_{\rho_l}$. Pair this signed
lower witness with an unrestricted trial $(\bar z,\bar g)$ and a
number $U\ge0$ satisfying

$$
|\beta_\rho+U_\rho\cdot\bar x+V_\rho\cdot\bar y|\le U
                 \quad\text{for every }\rho\in\mathscr R_j.
\tag{128.2}
$$

If $B>U$, then

$$
n_j\ge B>U\ge m_j,\qquad
\delta_j\ge\Delta:=B-U>0.
\tag{128.3}
$$

Consequently Theorem 127.1 applies with this explicit certified
$\Delta$, including all of its retention bounds and its positive
$\eta$ range. For $j=f$, (128.2) is a finite list of inequalities.
For $j=a$, it must cover every actual history. One sufficient
all-history upper witness, using only the displayed trial matrices,
is

$$
U=\frac{R_{\mathfrak s}}2
 \left(\|X_1(\bar z)\|_{\rm HS}+\|Y_1(\bar z)\|_{\rm HS}
                      +2|\bar g|\|K_-\|_{\rm HS}\right),
\tag{128.4}
$$

or any larger number. A sharper $U$ is allowed only with the
corresponding all-actual-row inequality (128.2).

*Proof.* For every $z$, the six cancellation equalities give

$$
\begin{aligned}
\mathcal F_j(z,0)
 &\ge\sum_l\lambda_l\sigma_l\ell_{\rho_l}(z,0)\\
 &=\sum_l\lambda_l\sigma_l\beta_{\rho_l}=B.
\end{aligned}
\tag{128.5}
$$

Minimising proves $n_j\ge B$. The unrestricted trial gives
$m_j\le\mathcal F_j(\bar z,\bar g)\le U$, proving (128.3).
The trace bound with the original row is

$$
|\ell_{i,w}(\bar z,\bar g)|
 \le\frac{a_w}{2}\|r_i\|_{\rm HS}
 \left(\|X_1(\bar z)\|_{\rm HS}+\|Y_1(\bar z)\|_{\rm HS}
                         +2|\bar g|\|K_-\|_{\rm HS}\right).
\tag{128.6}
$$

Since $a_w\le1$ for every actual $w$, this proves (128.4) for the
entire family, with no restriction on history length.

The classical intermediate is Chebyshev approximation and weak LP
duality, not an additional source-specific theorem. In the finite
case the epigraph problem has the inequalities
$-t\le\beta_\rho+U_\rho\cdot x+V_\rho\cdot y\le t$;
setting $y=0$ gives its zero-retention restriction. This is the
minimax LP of Boyd–Vandenberghe,
[*Convex Optimization*, §6.1.1, printed pp. 291–293](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf).
Its signed annihilating lower bound is the dual-norm certificate in
Example 5.6 and Exercise 5.6, equation (5.104), of the same book.
The existing [Library entry](../../../Library/QuadraticForms/boydvandenberghe2004convex.md)
records the book; the approximation result cited here is distinct
from that entry's S-procedure application. Sukhorukova–Ugon–Yost,
[*Chebyshev approximation for multivariate functions*,
arXiv:1510.06076v1, §2, equations (2.3)–(2.5) and Theorem 2.1](https://arxiv.org/pdf/1510.06076v1),
give the convex supremum formulation and signed active-gradient
criterion for their finite-set or continuous-hyperbox approximation
problems. Here (128.5) uses only their elementary convex-combination
intermediate, with the literal source rows and six completion
columns specified in (125.4). It does not require maximal deviations
to be attained by an actual history.

The all-history conclusion uses its own lower witness and its own
valid upper bound. The finite decoder supplies neither (128.2) for
all histories nor an exact norming set for $\mathcal F_a$.
Only actual rows enter (128.1); no coefficient-closure point is
asserted to be a history or an installed operation. The result is a
sufficient certificate. It certifies no particular allowed source
with $B>U$, and asserts neither universal endpoint entry nor a
resolution of an external open problem. $\square$

## 追加锚（本行以下为增补区）

## 129. Exact truncation by the number of native instrument labels

**Definition 129.1 (The fixed paired laws and their instrument layers).**
Fix any allowed source $\mathfrak s$ of VI Definition 114.1. In this
section $L_{\mathfrak s}$ always denotes the integer decoder length
of VI Proposition 118.2, not the real comparison constant in (124.4).
Use precisely the constants $c_{\mathfrak s},C_{\mathfrak s}$ of
(118.18), (118.20). For $x=(\gamma,h),x'=(\gamma',h')\in\mathcal P$
write $D_{\rm pair}(x,x')=\mathcal D(x,x')$ from (118.1), and put

$$
\begin{aligned}
\Delta^{[k]}(x,x')
 &=\sup_{1\le i\le9,\ k(w)=k,\ \beta\in\{0,1\}}
       |p_{\gamma,h}(u_i,w,\beta)-p_{\gamma',h'}(u_i,w,\beta)|,\\
\Delta^{[\le K]}(x,x')&=\max_{0\le k\le K}\Delta^{[k]}(x,x'),\\
K_{\mathfrak s}
 &=\max\left\{L_{\mathfrak s},0,
       \left\lceil\log_2(C_{\mathfrak s}/c_{\mathfrak s})\right\rceil\right\}.
\end{aligned}
\tag{129.1}
$$

The integer $k(w)$ counts the actual $0,1$ labels in V (91.2).
Every occurrence of the same installed deterministic $N$ contributes
zero to that count. All histories and their clocks are still those
of the original externally fixed schedules. The prefix $u_i$, its
subnormalised $r_i$, both terminal outcomes, and the factor
$a_w/2=2^{-k(w)}/2$ remain part of each coordinate. The finite vector
$P_{\mathfrak s}$ remains exactly (118.3). Every point of $\mathcal P$
is realised by one full ten-dimensional completion used for emission,
the single forward return and every history within that hypothesis,
as in VI Theorem 106.3; different hypotheses may differ. This notation
does not change the sole original preparation, the complex retention
disk, the installed menu, the record bases or any schedule.

**Theorem 129.2 (Exact full-domain instrument cutoff; repo-derived).**
For every fixed allowed source and every $x,x'\in\mathcal P$, the
integer in (129.1) satisfies

$$
2^{-(K_{\mathfrak s}+1)}C_{\mathfrak s}<c_{\mathfrak s},\qquad
\boxed{\ \Delta_{\rm all}(x,x')
                   =\Delta^{[\le K_{\mathfrak s}]}(x,x').\ }
\tag{129.2}
$$

Any integer $K\ge L_{\mathfrak s}$ satisfying the displayed strict
inequality can replace $K_{\mathfrak s}$. This is equality for the
original raw-law error on the full paired closed domain, including
both retention boundaries and both completion-ball boundaries. If
$D_{\rm pair}=0$, every probability difference and both sides of
(129.2) are zero. If $D_{\rm pair}>0$, all discarded layers together
have supremum strictly smaller than $\Delta_{L_{\mathfrak s}}$.
No maximum over a finite set of actual histories is asserted here.

*Proof.* Retain the factor $a_w$ in the first line of (118.21).
The bounds (118.19) and the choice (118.20) give, for every actual
coordinate separately,

$$
|\Delta p_{i,w,\beta}|
 \le 2^{-k(w)}C_{\mathfrak s}D_{\rm pair},
                   \qquad \beta=0,1.
\tag{129.3}
$$

For outcome $0$ use the unchanged total mass
$a_w\operatorname{Tr}r_i$, so its difference is the negative of the
outcome-$1$ difference. If $D_{\rm pair}=0$, (129.3) proves all
zero assertions without division. Otherwise the decoder rows, whose
ordinary lengths are at most $L_{\mathfrak s}$, are included among
$k(w)\le K$, since $k(w)\le|w|$. Thus (118.12) gives

$$
\begin{aligned}
\sup_{k(w)>K,\ i,\beta}|\Delta p_{i,w,\beta}|
 &\le2^{-(K+1)}C_{\mathfrak s}D_{\rm pair}\\
 &<c_{\mathfrak s}D_{\rm pair}
 \le\Delta_{L_{\mathfrak s}}
 \le\Delta^{[\le K]}.
\end{aligned}
\tag{129.4}
$$

The full supremum is the larger of the retained and discarded
suprema, proving equality. The explicit $K_{\mathfrak s}$ obeys
$2^{-K_{\mathfrak s}}C_{\mathfrak s}\le c_{\mathfrak s}$, so it
has the required strict inequality after the extra factor $1/2$.
This deduction uses the source-specific decoder and row estimates
of VI §118; it does not replace their finite vector. $\square$

**Lemma 129.3 (Ordinary length does not provide the suppression).**
For every allowed source there are two hypotheses in $\mathcal P$
and a constant $b_0>0$ such that, for every integer $n\ge0$,

$$
\max_{1\le i\le9,\ \beta\in\{0,1\}}
 |p_{0,h}(u_i,N^n,\beta)-p_{0,0}(u_i,N^n,\beta)|\ge b_0.
\tag{129.5}
$$

Consequently the instrument cutoff in Theorem 129.2 supplies no
ordinary-length decay estimate: the retained layer $k=0$ contains
undamped runs of arbitrarily large ordinary length.

*Proof.* Choose any $0<\|h\|\le1$. Since the literal $r_i$ span
$\operatorname{Herm}_3$, choose real $d_i$ with
$I_3=\sum_i d_i r_i$. At zero retention the paired lift against
$(0,0)$ has $Z=0$ and, by (118.9), $X+Y=bhh^\dagger$.
For every unitary $Q$, cyclicity of trace and $W^2=I_3$ give
$\operatorname{Tr}\Phi_Q(X,Y,0)=b\|h\|^2$. For $w=N^n$,
$a_w=1$, so (116.2) yields

$$
\sum_i d_i q_{i,N^n}(X,Y,0)=\tfrac12 b\|h\|^2.
$$

Taking absolute values proves (129.5) with
$b_0=b\|h\|^2/(2\sum_i|d_i|)>0$. These are admissible
zero-retention hypotheses with the completions supplied by VI
Theorem 106.3. This nondecay statement alone asserts neither a
particular maximizing history nor impossibility of additional
source-specific coincidences between row values. $\square$

**Corollary 129.4 (Exact truncation of the literal reflected tangent rows).**
Under Definition 125.1, for every $z\in\mathbb C^3,g\in\mathbb C$,

$$
\mathcal F_a(z,g)
 =\sup_{1\le i\le9,\ k(w)\le K_{\mathfrak s}}
               |\ell_{i,w}(z,g)|.
\tag{129.6}
$$

The finite tangent problem remains the maximum over
$|w|\le L_{\mathfrak s}$ in (125.2), with exactly the same
$\beta_\rho,U_\rho,V_\rho$ as (125.4). Formula (129.6) does
not assert norming of arbitrary elements of the entire lift
$\mathscr V$ by these layers.

*Proof.* For fixed $z,g$ the hypotheses
$(\eta g,-Ae+\eta z),(0,Ae+\eta f)$ lie in $\mathcal P$ for
all sufficiently small positive $\eta$, because $0<A<1$.
Apply (129.2), divide by $\eta$, and use the uniform per-row
remainder (125.11). That estimate bounds the difference between
the scaled retained-layer supremum and the right side of (129.6)
by $\mathcal E(R,G)\eta$ for fixed sufficiently large $R,G$.
Lemma 125.2 gives the full-side limit $\mathcal F_a(z,g)$.
This proves (129.6) without altering any row or requiring an
actual history to attain either supremum. $\square$

## 130. The same installed control and compact polynomial maximizations

**Definition 130.1 (Projective powers and labelled layer patterns).**
Fix the same source and a spectral decomposition of its installed
control,

$$
\begin{gathered}
N=S\operatorname{diag}(\lambda_1,\lambda_2,\lambda_3)S^\dagger,
\qquad |\lambda_j|=1,\qquad S\in U(3),\\
\alpha=(\lambda_2/\lambda_1,\lambda_3/\lambda_1),\qquad
\Lambda_N=\{a\in\mathbb Z^2:\alpha_1^{a_1}\alpha_2^{a_2}=1\},\\
T_N=\{z\in(S^1)^2:z_1^{a_1}z_2^{a_2}=1
                              \text{ for every }a\in\Lambda_N\},\\
M(z)=S\operatorname{diag}(1,z_1,z_2)S^\dagger.
\end{gathered}
\tag{130.1}
$$

For $k\ge0$, a native label pattern
$\epsilon=(\epsilon_1,\ldots,\epsilon_k)\in\{0,1\}^k$ and
$\mathbf z=(z^{(0)},\ldots,z^{(k)})\in T_N^{k+1}$, put

$$
\begin{aligned}
Q_{\epsilon}(\mathbf z)
 &=M(z^{(k)})V_{\epsilon_k}M(z^{(k-1)})\cdots
                     V_{\epsilon_1}M(z^{(0)})V_0,\\
\bar q_{i,k,\epsilon}(\mathbf z;X,Y,Z)
 &=\frac{2^{-k}}2\operatorname{Tr}
                   [r_i\Phi_{Q_\epsilon(\mathbf z)}(X,Y,Z)].
\end{aligned}
\tag{130.2}
$$

For $k=0$ the first formula means $M(z^{(0)})V_0$. For a paired
hypothesis let $X,Y$ be exactly (118.9) and
$Z=\gamma K_h-\gamma'K_{h'}$. Define two outcome differences
$F_{i,k,\epsilon,1}=\bar q_{i,k,\epsilon}$ and
$F_{i,k,\epsilon,0}=-\bar q_{i,k,\epsilon}$, evaluated on that
paired lift. The associated unpaired probabilities are exactly

$$
\begin{aligned}
\bar p_{\gamma,h}(i,k,\epsilon,\mathbf z,1)
 &=\frac{2^{-k}}2\operatorname{Tr}
                 [r_iE_{\gamma,h}(Q_\epsilon(\mathbf z))],\\
\bar p_{\gamma,h}(i,k,\epsilon,\mathbf z,0)
 &=2^{-k}\operatorname{Tr}r_i
                -\bar p_{\gamma,h}(i,k,\epsilon,\mathbf z,1).
\end{aligned}
\tag{130.3}
$$

These definitions extend the actual rows continuously for a
mathematical supremum; they do not install $M(z)$ as an operation.

**Theorem 130.2 (Exact compact representation and semialgebraicity; repo-derived).**
For every fixed allowed source, the unchanged full paired-law error
on $\mathcal P^2$ is the following finite collection of compact
polynomial maximizations:

$$
\boxed{\quad
\Delta_{\rm all}(x,x')
 =\max_{\substack{0\le k\le K_{\mathfrak s},\
          \epsilon\in\{0,1\}^k,\ 1\le i\le9,\\
          \beta\in\{0,1\},\ \sigma\in\{-1,1\}}}
       \ \max_{\mathbf z\in T_N^{k+1}}
               \sigma F_{i,k,\epsilon,\beta}(\mathbf z;x,x').
\quad}
\tag{130.4}
$$

Here $T_N$ is compact and real algebraic, and the objectives are real
polynomials in the real and imaginary coordinates of $\mathbf z$
and both hypotheses. Thus $\Delta_{\rm all}$ is semialgebraic in
all sixteen real hypothesis coordinates, on the entire $\mathcal P^2$.
The original finite error has its own semialgebraic representation

$$
\Delta_{\rm finite}(x,x')
 =\max_{\substack{1\le i\le9,\ |w|\le L_{\mathfrak s},\\
                    \beta\in\{0,1\},\ \sigma\in\{-1,1\}}}
       \sigma\bigl(p_{\gamma,h}(u_i,w,\beta)
                     -p_{\gamma',h'}(u_i,w,\beta)\bigr),
\tag{130.5}
$$

a maximum of finitely many real polynomials in those coordinates.
Moreover, (129.6) has the identical compact representation (130.4)
with $\bar q$ applied to $(X_1(z),Y_1(z),gK_-)$ and absolute
values, so $\mathcal F_a$ is semialgebraic in its eight real
variables. These are the literal extensions of the rows of §125.

A maximizing closure point in (130.4) represents a supremum of
actual raw-law coordinates. It need not be an actual history,
an attainable terminal event, or a physical control. Neither an
ordinary-length cutoff for general $N$, nor a finite actual-history
norming set for general $N$, nor a source-uniform length is part of
these conclusions. No effective integer-relation computation or
complexity bound for arbitrary real source data is asserted.

*Proof.* The nonnegative-power torus criterion already stated by
$\texttt{D5.S3.Fourier.TorusOrbitClosure.result}$, applied to the two
coordinates of $\alpha$, gives

$$
\overline{\{\alpha^n:n\in\mathbb N_0\}}=T_N.
\tag{130.6}
$$

This is the scope recorded in the existing
[Onishchik Library note](../../../Library/Fourier/onishchik2020kronecker.md):
no rational independence or algebraicity is required, and torsion is
included. The same arbitrary-unit-circle-tuple statement is
Ouaknine–Worrell, [*Ultimate Positivity is Decidable for Simple Linear
Recurrence Sequences*, arXiv:1309.1914v4, Proposition 2 and Theorem
3.2 (Kronecker)](https://arxiv.org/html/1309.1914v4).
Their algebraic-input basis bounds and effective computation are
Theorem 3.1 and Corollary 1, and are not applied to arbitrary real
entries of the present $N$.

For completeness, the finite algebraic description needed here
requires only existence of a finite basis of $\Lambda_N\le\mathbb Z^2$.
Indeed its first-coordinate image is $d\mathbb Z$. If $d>0$,
choose a vector with first coordinate $d$; subtraction of its
integer multiples leaves the first coordinate zero. That kernel
is generated by at most one vector $(0,e)$. If $d=0$, the whole
subgroup is such a kernel. Thus at most two vectors generate
$\Lambda_N$. For each chosen generator $a$, write
$a=a^+-a^-$ with nonnegative integer coordinates. On $(S^1)^2$
its relation is equivalent to

$$
\prod_{j=1}^2 z_j^{a_j^+}
       =\prod_{j=1}^2 z_j^{a_j^-}.
\tag{130.7}
$$

The real and imaginary parts of these finitely many equations,
together with $(\operatorname{Re}z_j)^2+(\operatorname{Im}z_j)^2=1$,
define $T_N$. Relations for the generating vectors imply those for
their integer combinations since all $z_j$ are nonzero. This proves
that $T_N$ is real algebraic and compact, without computing the basis.

Every actual word with exactly $k$ native labels has the unique
chronological form

$$
w=N^{n_0}\epsilon_1N^{n_1}\cdots\epsilon_kN^{n_k},
       \qquad n_0,\ldots,n_k\in\mathbb N_0.
\tag{130.8}
$$

For each such tuple there is an original fixed schedule with those
instrument positions and those deterministic runs; $\epsilon$ names
its actual retained label event. These statements do not select a
label during execution. Since
$N^n=\lambda_1^nM(\alpha^n)$, its $Q_w$ equals the first line of
(130.2) at $z^{(l)}=\alpha^{n_l}$ up to a scalar phase.
Every term of $\Phi_Q$ is unchanged by that phase. Consequently
(130.2)–(130.3) agree exactly with both original coordinates, including
their raw masses, on this dense set of tuples. The $k+1$ exponents
in (130.8) are independently arbitrary integers; hence (130.6)
makes these tuples dense in $T_N^{k+1}$. Continuity shows that the
supremum over actual tuples equals the maximum over this compact
product, for each fixed $k,\epsilon,i,\beta,\sigma$. Taking the
finite outer maximum and using Theorem 129.2 proves (130.4).
This closure is only that of powers of the same $N$. In particular,
the positive-word $PU(3)$ density used for exact identification in
VI §114 does not replace $T_N$ by $U(3)$ at a fixed instrument count.
Lemma 129.3 explains why large ordinary lengths cannot be removed
by probability suppression: the undamped $N$ runs remain in (130.8).

In real coordinates conjugation, matrix multiplication and trace
are polynomial operations; $S,V_0,V_1,W,r_i,D,t,b$ are fixed
coefficients. The expressions (114.2)–(114.3), including the full
complex $\gamma$, are also polynomial. Thus all signed objectives
in (130.4) are real polynomials. If they are indexed by a finite
set $\mathcal J$ and written $F_\lambda(y;x,x')$, their maximum
has the exact graph description

$$
\begin{gathered}
v\ge0,\quad
\forall\lambda\in\mathcal J\ \forall y\in T_N^{k(\lambda)+1},
                 \quad F_\lambda(y;x,x')\le v,\\
\exists\lambda\in\mathcal J\ \exists y\in T_N^{k(\lambda)+1},
                 \quad F_\lambda(y;x,x')=v.
\end{gathered}
\tag{130.9}
$$

Finite indexing means finite conjunctions and disjunctions. All
quantifiers over $y$ can be written over real coordinates with
polynomial membership tests. Real quantifier elimination therefore
makes this graph semialgebraic; it is used only as an existence
statement with the fixed real coefficients. The intermediate is
Basu, [*Algorithms in Real Algebraic Geometry: A Survey*,
arXiv:1409.1534v1, Theorem 2.1](https://arxiv.org/pdf/1409.1534v1),
or Guo–Kim–Jiao–Pham, [*On types of KKT points in polynomial
optimization*, arXiv:2004.12315v1, §2.1, Theorem 2.1](https://arxiv.org/html/2004.12315v1).
Formula (130.5) follows directly from the original finite set and
the same polynomial calculation, independently of any equality
between its norm and the full norm. Finally apply (129.6) and
(130.8) to the affine matrices of (125.3). This gives the claimed
tangent representation and semialgebraicity using those same rows.
All closure operations in this proof concern numerical suprema;
none merges physically distinct clocks or records. $\square$

## 131. Semialgebraic minima for the unchanged reflection-side problems

**Definition 131.1 (Compact argmin fibers and extremal retention radii).**
Fix the source, $0<A<1$ and the unit $f\perp e$ of Definition
125.1. Choose any $0<\bar\eta<\sqrt{1-A^2}$. For
$0\le\eta\le\bar\eta$ retain $h_0(\eta)=Ae+\eta f$, and put

$$
\begin{aligned}
\mathcal C
 &=\{(\gamma,h):|\gamma|\le1,\ \|h\|\le1,
                         \operatorname{Re}(e^\dagger h)\le0\},\\
\Gamma_j(\eta)
 &=\{(\gamma,h)\in\mathcal C:
                 d_j(\gamma,h;h_0(\eta))=\mu_j(\eta)\},\\
r_j^-(\eta)&=\min_{(\gamma,h)\in\Gamma_j(\eta)}|\gamma|,
\qquad
r_j^+(\eta)=\max_{(\gamma,h)\in\Gamma_j(\eta)}|\gamma|,
                         \qquad j=f,a.
\end{aligned}
\tag{131.1}
$$

For positive $\eta$, $\mu_j,\nu_j$ are exactly (124.2), (126.6);
at $\eta=0$ use those same compact minimizations to extend them.
The set $\mathcal C$ is the original reflection side with the
auxiliary zero-retention slice included, not a tangent feasible set.

**Theorem 131.2 (Semialgebraic values and compact argmin relation; repo-derived).**
For each $j=f,a$ separately, $\mu_j,\nu_j,r_j^-,r_j^+$ are
semialgebraic functions on $[0,\bar\eta]$. The relation

$$
\Gamma_j=\{(\eta,\gamma,h):0\le\eta\le\bar\eta,
                                  (\gamma,h)\in\Gamma_j(\eta)\}
\tag{131.2}
$$

is a compact semialgebraic set with nonempty compact fibers.
The two value functions $\mu_j,\nu_j$ are continuous there, and
$0\le r_j^-\le r_j^+\le1$. For $0<\eta\le\eta_*$ in
Theorem 126.3 all compact minimizers, and hence both extremal radii,
satisfy $|\gamma|\le G\eta$.

*Proof.* The source-fixed polynomial description of $\mathcal P$
and Theorem 130.2 show that each $d_j(\gamma,h;h_0(\eta))$ is
semialgebraic on the indicated domain. This is the original finite
error for $j=f$ and the original full error for $j=a$. Continuity
of both is already proved in Theorem 124.2. The feasible set
$\mathcal C$ is a fixed nonempty compact semialgebraic set,
independent of $\eta$. In particular minima exist. An exact
value-graph formula for $\mu_j$ is

$$
\begin{aligned}
v=\mu_j(\eta)\quad\Longleftrightarrow\quad
 &\exists x\in\mathcal C:\ d_j(x;h_0(\eta))=v,\\
 &\forall x'\in\mathcal C:\ d_j(x';h_0(\eta))\ge v.
\end{aligned}
\tag{131.3}
$$

When $d_j$ is represented by its semialgebraic graph, these are
real polynomial quantifiers after introducing its value variables.
The same formula with $\gamma=0$ throughout gives $\nu_j$.
The real projection/complement theorem cited in Theorem 130.2
therefore proves both value graphs semialgebraic. Equality to the
value gives a semialgebraic graph for $\Gamma_j$.

Uniform continuity of $d_j$ on $[0,\bar\eta]\times\mathcal C$
shows that the change in each minimum is bounded by the supremum
of the corresponding change of the objective. This proves
continuity of both values, using the zero-retention compact slice
for $\nu_j$. The equality defining $\Gamma_j$ is thus closed
in a compact product, so (131.2) is compact as well as semialgebraic.
Each fiber is nonempty and compact.

The retention function has the polynomial graph
$r\ge0$, $r^2=(\operatorname{Re}\gamma)^2+
(\operatorname{Im}\gamma)^2$. Existential attainment and universal
lower, respectively upper, bounds for $r$ over the nonempty fiber
$\Gamma_j(\eta)$ give value-graph formulas just as in (131.3).
They prove semialgebraicity and existence of both radii. This
argument requires no choice of a minimizer. Their order and unit
bound follow from $\mathcal C$. Finally, (126.9) bounds retention
for every compact minimizer by $G\eta$, so it bounds both extrema.
The source-specific content is the application to the unchanged
raw-law objectives and their entire minimizer fibers; the real
projection intermediate is the classical one already cited. $\square$

## 132. Eventual endpoint trichotomy, including tangent ties

**Theorem 132.1 (A stable endpoint type for each original error; repo-derived).**
Fix the source, $A,f$ as in Definition 131.1, and fix either $j=f$
or $j=a$. There is $\varepsilon_j>0$, depending on these fixed
choices, such that exactly one of the following patterns holds
for every $0<\eta<\varepsilon_j$:

(I) $r_j^+(\eta)=0$. Every compact minimizer has zero retention,
$\nu_j(\eta)=\mu_j(\eta)$, and the original punctured
reflection-side endpoint at error $\mu_j(\eta)$ is absent.

(II) $r_j^-(\eta)=0<r_j^+(\eta)$. Zero and nonzero retention
minimizers coexist, $\nu_j(\eta)=\mu_j(\eta)$, and the
original punctured endpoint is present.

(III) $r_j^-(\eta)>0$. Every compact minimizer is punctured,
$\nu_j(\eta)>\mu_j(\eta)$, and the original punctured endpoint
is present.

In particular there is no infinite switching of endpoint types
accumulating at $\eta=0$, also when $\delta_j=n_j-m_j=0$.
The result classifies possible eventual behavior; it selects no
one pattern for an unspecified allowed source. Equality of the
two values alone does not distinguish (I) from (II).

*Proof.* At any fixed positive $\eta$, nonempty compact fibers
make exactly one of

$$
r_j^+=0,\qquad r_j^-=0<r_j^+,\qquad r_j^->0
\tag{132.1}
$$

hold. Since a radius is nonnegative, $r_j^+=0$ means that every
minimizer has zero retention. If $r_j^-=0<r_j^+$, attainment of
both extrema supplies the two kinds of minimizers. If $r_j^->0$,
no zero-retention minimizer exists. Moreover,

$$
\nu_j(\eta)=\mu_j(\eta)
       \quad\Longleftrightarrow\quad r_j^-(\eta)=0.
\tag{132.2}
$$

For the forward direction take an attained zero-retention minimum
in (126.6); equality makes it a compact unrestricted minimizer.
For the reverse direction take the attained radius-zero minimizer
and compare with the restricted minimum. If $r_j^->0$, the
restricted minimum still exists, so absence of equality and
$\nu_j\ge\mu_j$ imply strict inequality.

The endpoint equality criterion of Theorem 124.2 says exactly
that the original punctured endpoint is present if and only if
there is a compact minimizer with nonzero retention, equivalently
$r_j^+>0$. This proves all pointwise pattern assertions, with the
same raw probabilities and feasible set as that theorem.

By Theorem 131.2, each of the three subsets of
$(0,\bar\eta)$ defined in (132.1) is semialgebraic. A
semialgebraic subset of the real line is a finite union of points
and intervals: partition the line at the finitely many real roots
of the nonzero polynomials in a Boolean description and observe
that every sign is constant on each remaining interval. Choose
$\varepsilon_j>0$ below every positive boundary point of these
three sets and below $\bar\eta$. Their membership is then
constant on $(0,\varepsilon_j)$; since they partition it, precisely
one contains the whole interval. This uses no assumption on the
tangent gap. If both $j$ are considered, shrinking to the smaller
of their two intervals stabilizes both, without requiring their
types to agree. This is the source-specific consequence of the
real semialgebraic finiteness in Guo–Kim–Jiao–Pham, §2.1 cited
above, not a conclusion that a particular source has a strict gap.
$\square$

## 133. Rational leading orders for extremal retention and tied gaps

**Theorem 133.1 (Scalar growth restrictions at the original thresholds; repo-derived).**
For each fixed source, $0<A<1$, unit $f\perp e$ and $j=f,a$,
shrink the positive interval of Theorem 132.1 if necessary.
Each of its two extremal scalar radii is either identically zero
there or is positive there and satisfies

$$
r_j^\pm(\eta)=c_j^\pm\eta^{q_j^\pm}
                         +o(\eta^{q_j^\pm}),
\qquad c_j^\pm>0,\quad q_j^\pm\in\mathbb Q,\quad q_j^\pm\ge1.
\tag{133.1}
$$

Only radii that are positive have coefficients in (133.1).
If $\delta_j=n_j-m_j=0$, the original nonnegative nonlinear gap
either vanishes identically on a final positive interval or obeys

$$
\nu_j(\eta)-\mu_j(\eta)
       =d_j^{\rm gap}\eta^{q_j^{\rm gap}}
                         +o(\eta^{q_j^{\rm gap}}),
\qquad d_j^{\rm gap}>0,\quad q_j^{\rm gap}\in\mathbb Q,
\quad q_j^{\rm gap}\ge2.
\tag{133.2}
$$

Thus a positive gap cannot be flatter than every power of $\eta$.
These statements concern the extremal scalar functions themselves,
not arbitrary selections from the minimizer relation. They allow
positive retention of order $o(\eta)$, and do not select an endpoint
type in a tangent tie. All intervals and coefficients are for the
fixed source and fixed interior $A$; no uniformity at $A=0,1$ or
over sources is asserted.

*Proof.* The zero sets of the nonnegative semialgebraic functions
$r_j^-,r_j^+$ and $\nu_j-\mu_j$ have finitely many boundary
points. On a sufficiently small positive interval each function
is therefore either zero everywhere or positive everywhere.
For a nonzero scalar semialgebraic function $u$ on $(0,\epsilon)$,
the classical growth dichotomy gives
$u(\eta)=c\eta^q+o(\eta^q)$ with $c\ne0$ and $q\in\mathbb Q$.
The intermediate is Duan–Jiao–Wu–Zhou,
[*Existence of Pareto solutions for vector polynomial optimization
problems with constraints*, arXiv:2109.07304v1, §2, Lemma 2.2](https://arxiv.org/pdf/2109.07304v1).
Its hypotheses here hold for the scalar functions by Theorem 131.2,
without any analyticity assumption on a chosen minimizer. Positivity
forces $c>0$.

For either positive radius, Theorem 126.3 gives $u(\eta)\le G\eta$.
If its growth exponent were $q<1$, then
$u(\eta)/\eta\sim c\eta^{q-1}\to+\infty$, contradicting this
bound. Hence $q\ge1$. When $\delta_j=0$, the two remainder
bounds in (126.8), with the same original minima, give

$$
0\le\nu_j(\eta)-\mu_j(\eta)\le2E\eta^2.
\tag{133.3}
$$

For a positive gap the same argument after division by $\eta^2$
forces its rational exponent to be at least two, proving (133.2).
A positive function with the asymptotic (133.2) is not
$o(\eta^{q_j^{\rm gap}})$ and hence is not smaller than every
power. Identically zero gaps occur in both patterns (I) and (II)
of Theorem 132.1, whereas a positive gap occurs in (III).
Consequently a zero tangent gap and even equality of the nonlinear
values do not decide punctured attainment. No regularity of an
arbitrarily varying choice of minimizers has been inferred. $\square$

## 134. Finite projective order and actual finite norming families

**Corollary 134.1 (An exact actual-history family and its full tangent LP; repo-derived).**
Suppose the same installed $N$ of an allowed source satisfies
$N^p=\lambda I_3$ for an integer $p\ge1$ and $|\lambda|=1$.
Let $K=K_{\mathfrak s}$ and define the finite set of actual words

$$
\begin{gathered}
\mathscr W_{K,p}
 =\{N^{n_0}\epsilon_1N^{n_1}\cdots\epsilon_kN^{n_k}:
       0\le k\le K,\ \epsilon\in\{0,1\}^k,
                     \ 0\le n_l\le p-1\},\\
B_{\mathfrak s,p}=K+(K+1)(p-1).
\end{gathered}
\tag{134.1}
$$

For every paired hypothesis in the full closed domain,

$$
\begin{aligned}
\Delta_{\rm all}(x,x')
 &=\max_{\substack{1\le i\le9,\ w\in\mathscr W_{K,p},\\
                                      \beta\in\{0,1\}}}
          |p_{\gamma,h}(u_i,w,\beta)-p_{\gamma',h'}(u_i,w,\beta)|\\
 &=\Delta_{B_{\mathfrak s,p}}(x,x').
\end{aligned}
\tag{134.2}
$$

This is a finite norming family of actual existing rows for the
full paired-law error; it is distinct in definition from the
original decoder $P_{\mathfrak s}$. No equality of those two
vectors or their error norms is presumed. With the literal
coefficients of (125.4) and
$\mathscr H=\{(i,w):1\le i\le9,w\in\mathscr W_{K,p}\}$,
the full tangent coefficients are exactly the finite linear programs

$$
\begin{aligned}
m_a&=\min_{x\in\mathbb R^6,\ y\in\mathbb R^2,\ v\in\mathbb R}v
 &&\text{subject to }-v\le\beta_\rho+U_\rho\cdot x+V_\rho\cdot y
                                 \le v\quad(\rho\in\mathscr H),\\
n_a&=\min_{x\in\mathbb R^6,\ v\in\mathbb R}v
 &&\text{subject to }-v\le\beta_\rho+U_\rho\cdot x
                                 \le v\quad(\rho\in\mathscr H).
\end{aligned}
\tag{134.3}
$$

Both optima are attained. No periodicity of $V_0$ or $V_1$ is required.

*Proof.* For each exponent in (130.8), write $n_l=pq_l+r_l$ with
$0\le r_l<p$. Replacing $N^{n_l}$ by $N^{r_l}$ multiplies the
unitary product only by the scalar $\lambda^{q_l}$, even with
arbitrary intervening native labels. Their product phase cancels
from $\Phi_Q$ and $E_{\gamma,h}(Q)$. The number $k$ and therefore
the actual weight $2^{-k}/2$ are unchanged. Thus both raw
probability values of the original word equal those of the reduced
actual word, at the same prefix, for every hypothesis. The reduced
word has length at most $k+(k+1)(p-1)\le B_{\mathfrak s,p}$.
Theorem 129.2 now proves the first equality of (134.2).
The reduced family is contained in all words of length at most
$B_{\mathfrak s,p}$, which are contained in all histories; the two
inclusions prove its second equality.

The identical phase cancellation holds for the literal affine
rows in (125.3). Corollary 129.4 therefore gives
$\mathcal F_a(z,g)=\max_{\rho\in\mathscr H}|\ell_\rho(z,g)|$.
Substitute the eight real columns (125.4) and take its epigraph;
restriction to $g=0$ is exactly $y=0$. This proves (134.3), and
Theorem 126.1 supplies attained minima. This uses only the
finite epigraph identity already credited to Boyd–Vandenberghe
in §128. Physically different original and reduced clocks or
records remain different events; equality of their row functionals
here is a mathematical equality, not a merger or a new control.
$\square$

**Proposition 134.2 (A nonempty allowed subclass of projective order two).**
For every $0<d<1$ and every $\theta$ with $\sin(2\theta)\ne0$,
choose any complex unit $v\perp\xi$ and put

$$
u=\frac{\xi+v}{\sqrt2},\qquad N=I_3-2uu^\dagger.
\tag{134.4}
$$

This gives a legitimate allowed control with $N^2=I_3$ and
$[N,P_\xi]\ne0$. The actual eight-plus-one prefix construction
of V §§92–93 supplies an allowed source for it, so the subclass
in Corollary 134.1 is nonempty. This statement evaluates neither
$\delta_j$ nor any of the three endpoint types for that source.

*Proof.* Since $u^\dagger u=1$, the matrix $uu^\dagger$ is an
orthogonal projection, so $N=N^\dagger$ and $N^2=I_3$.
Moreover $N\xi=-v$, hence $NP_\xi N^\dagger=vv^\dagger\ne P_\xi$.
A unitary commuting with $P_\xi$ would preserve that projection
under conjugation, proving the mixing condition. For these original
$d,\theta$, V Theorem 92.1 supplies eight actual native prefix
columns with their original masses. V Theorem 92.2 supplies a ninth
column by applying this same mixing $N$ to one of them, with no
new preparation or normalization. They span $\operatorname{Herm}_3$,
so all clauses of VI Definition 114.1 hold. In this subclass $p=2$
in (134.1) gives the valid source-dependent bound $2K+1$.
Neither mixing nor finite projective order compares the two tangent
optima, so this construction is not a positive-gap example. The
strict-gap existence question, and the choice between the eventual
endpoint types for a specified but unevaluated source, remain
unresolved by these conclusions. No sampling, entire-unitary
recovery, or external named-problem conclusion follows. $\square$

## 追加锚（本行以下为增补区）

## 135. The reflection relation with its original history weights

**Definition 135.1 (Distance from the source reflection to the same control powers; repo-derived).**
Fix any allowed source $\mathfrak s$ of VI Definition 114.1 and retain
Definition 125.1 literally, for any $0<A<1$ and any complex unit
$f\perp e=t/\tau$. All matrix norms below denoted $\|\cdot\|_{\rm op}$
are operator norms for the standard complex Euclidean norm;
$\|\cdot\|_{\rm HS}$ remains the Hilbert–Schmidt norm. Put

$$
\begin{gathered}
\Pi=I_3-ee^\dagger,\qquad W=I_3-2ee^\dagger,\qquad
\mathscr T(z,g)=(Wz,-g),\\
\mathscr G_N=\overline{\{\omega N^n:
                  n\in\mathbb N_0,\ \omega\in S^1\}}\subset U(3),\\
\epsilon_N=\operatorname{dist}_{\rm op}(W,\mathscr G_N)
 =\inf_{\substack{n\in\mathbb N_0\\ |\lambda|=1}}
                    \|N^n-\lambda W\|_{\rm op}.
\end{gathered}
\tag{135.1}
$$

The $W$ in this definition is the original source matrix of V (54.1),
not a freely chosen reflection: VI (106.3), (106.7) give
$e=(1,-1,0)^{\mathsf T}/\sqrt2$. Thus (135.1) measures a relation
between that source reflection and powers of its one installed $N$.
The closure is in the operator norm. It is compact, so the distance
is attained in $\mathscr G_N$, and $\epsilon_N=0$ means exactly
$W\in\mathscr G_N$. It need not mean $N^n=\lambda W$ for an actual
finite exponent.

The same-power description (130.1), (130.6) gives, using its fixed
spectral coordinates,

$$
\mathscr G_N=\{\omega M(\zeta):\omega\in S^1,\ \zeta\in T_N\}.
\tag{135.2}
$$

Indeed $N^n=\lambda_1^nM(\alpha^n)$ and the scalar in (135.1)
absorbs $\lambda_1^n$; the dense tuples $\alpha^n$ of (130.6)
and compactness give both inclusions. The topological intermediary
here is the nonnegative-power criterion in Ouaknine–Worrell,
[*Ultimate Positivity is Decidable for Simple Linear Recurrence
Sequences*, arXiv:1309.1914v4, §3, Theorem 3.4 and Proposition
3.5](https://arxiv.org/pdf/1309.1914v4), and the torus criterion
already used in §130 and recorded in the
[Onishchik note](../../../Library/Fourier/onishchik2020kronecker.md).
Theorem 3.4 and the proof of Proposition 3.5 use arbitrary real
angles for this closure statement. The algebraic-input assumptions
for the effective bounds in that paper's Theorem 3.1 and Corollary
3.2 are not imposed here, and no effective procedure for arbitrary
real source data is part of (135.1)–(135.2). Neither formula replaces
the same-power closure by unrestricted $U(3)$.

For the literal tangent matrices (125.3) define the nonnegative number

$$
\mathscr B_A(z,g)=R_{\mathfrak s}
 \bigl(\|X_1(z)\|_{\rm HS}+\|Y_1(z)\|_{\rm HS}
                      +2|g|\|K_-\|_{\rm HS}\bigr),\qquad
R_{\mathfrak s}=\max_i\|r_i\|_{\rm HS}.
\tag{135.3}
$$

In particular the $r_i$ in this number are still the subnormalised
original prefixes. The norms $\mathcal F_f,\mathcal F_a$ and the
numbers $m_j,n_j,\delta_j$ keep precisely (125.2)–(125.5).

**Lemma 135.2 (The weighted source-row relation; repo-derived).**
For every source, $A,f$ in Definition 135.1, every
$z\in\mathbb C^3,g\in\mathbb C$, every original prefix $i$, every
finite actual intermediate history $w$, every $n\in\mathbb N_0$
and every $|\lambda|=1$, one has

$$
\begin{aligned}
X_1(Wz)&=-WX_1(z)W,\qquad Y_1(Wz)=-WY_1(z)W,\\
(-g)K_-&=-W(gK_-)W,\\
\bigl|\ell_{i,w}(Wz,-g)+\ell_{i,wN^n}(z,g)\bigr|
 &\le a_w\mathscr B_A(z,g)\|N^n-\lambda W\|_{\rm op}.
\end{aligned}
\tag{135.4}
$$

Here $wN^n$ is the chronological word with the deterministic run
after $w$. Its prefix remains $u_i$, its native labels remain those
of $w$, and $a_{wN^n}=a_w$, without division by any probability.
Moreover $\mathscr B_A(Wz,-g)=\mathscr B_A(z,g)$ and

$$
\left|\mathcal F_a(Wz,-g)-\mathcal F_a(z,g)\right|
                     \le\epsilon_N\mathscr B_A(z,g).
\tag{135.5}
$$

*Proof.* To distinguish the original vectors of V (54.1) from the
arbitrary tangent $f$, write
$v_-=(1,-1,0)^{\mathsf T}/\sqrt2$ for that source's minus vector.
VI (106.3) says $t=\eta\alpha v_-$ with
$\eta=(\sqrt2+1)/\sqrt{12}>0$ and $\alpha=\sqrt6/4>0$.
Consequently $e=v_-$, $We=-e$, and $Wf=f$ for every allowed complex
transverse $f$. The same source gives
$D=a_+a_+^\dagger+\alpha^2ee^\dagger$ with $a_+=P_+Uq$.
Since $Wa_+=a_+$, one has $WDW=D$. Formula (125.3) now gives
$WK_-W=K_-$.

From the definitions of $H,S$ in (125.3), direct conjugation yields

$$
\begin{gathered}
H(Wz)=-WH(z)W,\qquad S(Wz)=-WS(z)W,\\
WH(f)W=-H(f),\qquad WS(f)W=-S(f).
\end{gathered}
\tag{135.6}
$$

Adding $H(f)$ and subtracting $S(f)$, respectively, shows
$H_1(Wz)=-WH_1(z)W$ and $S_1(Wz)=-WS_1(z)W$.
Their fixed real linear combinations in (125.3) prove the first
line of (135.4); commutation of $K_-$ proves its second line.
These identities and unitary invariance of Hilbert–Schmidt norm
also prove the asserted identity for $\mathscr B_A$.

For an arbitrary lift $L=(X,Y,Z)\in\mathscr V$ of VI Definition
116.1 set
$\mathscr J L=(-WXW,-WYW,-WZW)$ and abbreviate

$$
q_i(Q,a;L)=\frac a2\operatorname{Tr}[r_i\Phi_Q(L)].
$$

Every occurrence of $Q$ in $\Phi_Q$ is a conjugation, including
those followed or preceded by the fixed $W$. Linearity therefore gives

$$
q_i(Q_w,a_w;\mathscr J L)=-q_i(WQ_w,a_w;L).
\tag{135.7}
$$

For unitaries $U,V$ and any complex matrix $M$, expansion into two
terms gives

$$
\begin{aligned}
\|U^\dagger MU-V^\dagger MV\|_{\rm HS}
 &\le\|(U^\dagger-V^\dagger)MU\|_{\rm HS}
                  +\|V^\dagger M(U-V)\|_{\rm HS}\\
 &\le2\|U-V\|_{\rm op}\|M\|_{\rm HS}.
\end{aligned}
\tag{135.8}
$$

Apply this with $U=N^nQ_w$ and $V=\lambda WQ_w$ to each of
$X,Y,Z,Z^\dagger$ in (116.1). Multiplication by $W$ preserves
the norm; a scalar phase of $Q$ cancels. Trace Cauchy–Schwarz and
the original factor $a_w/2$ then give

$$
\begin{aligned}
&|q_i(N^nQ_w,a_w;L)-q_i(WQ_w,a_w;L)|\\
&\quad\le a_w R_{\mathfrak s}\|N^n-\lambda W\|_{\rm op}
          (\|X\|_{\rm HS}+\|Y\|_{\rm HS}+2\|Z\|_{\rm HS}).
\end{aligned}
\tag{135.9}
$$

The chronological rule V (91.2) gives
$Q_{wN^n}=N^nQ_w$ and $k(wN^n)=k(w)$.
Substitute $L=(X_1(z),Y_1(z),gK_-)$ into (135.7)–(135.9)
to prove the last line of (135.4), with its actual weight intact.
For each fixed $n,\lambda$, taking the supremum over actual $i,w$
and only then using $a_w\le1$ gives

$$
\mathcal F_a(Wz,-g)\le\mathcal F_a(z,g)
                      +\mathscr B_A(z,g)\|N^n-\lambda W\|_{\rm op}.
$$

Taking the infimum over $n,\lambda$ gives the same inequality with
$\epsilon_N$. Repeat it at $(Wz,-g)$, using $\mathscr T^2=I$
and the identity for $\mathscr B_A$, to obtain (135.5).
The supremum uses all original schedules; it does not alter a
schedule already fixed for one history or select a native label.
A limiting closure witness is only a limit of these numerical rows,
not an installed operation or an attained history. $\square$

## 136. Quantitative obstruction and the zero-defect tangent optimum

**Theorem 136.1 (A source-dependent reflection bound; repo-derived).**
For every allowed source $\mathfrak s$, let
$\underline c,\overline C,J_1$ be exactly the positive constants
in Theorem 126.1, and define from this source alone

$$
\begin{aligned}
G_0&=\frac{2\sqrt2\,\overline C}{\underline c},&
R_0&=1+J_1G_0,\\
\kappa_{\mathfrak s}
 &=\tau+|s_\theta c_\theta|(\|D\|_{\rm HS}+b),\\
C_{\rm ref}
 &=R_{\mathfrak s}\bigl[
       (b+2|s_\theta c_\theta|\tau)(R_0+1)
                           +\kappa_{\mathfrak s}G_0\bigr]>0.
\end{aligned}
\tag{136.1}
$$

Then for every $0<A<1$ and every complex transverse unit $f$ of
Definition 125.1,

$$
\boxed{\quad 0\le\delta_a=n_a-m_a\le C_{\rm ref}\epsilon_N.\quad}
\tag{136.2}
$$

The constant is independent of $A,f$ for this fixed source, but no
bound uniform over allowed sources is asserted. More precisely, for
all complex $z,g$, without a boundedness restriction,

$$
\mathcal F_a(\Pi z,0)
 \le\mathcal F_a(z,g)+\tfrac12\epsilon_N\mathscr B_A(z,g).
\tag{136.3}
$$

If $\epsilon_N=0$, the full-law tangent problem has

$$
\begin{gathered}
\mathcal F_a(Wz,-g)=\mathcal F_a(z,g),\qquad
\mathcal F_a((I_3+W)z/2,0)\le\mathcal F_a(z,g)
                      \quad(z\in\mathbb C^3,g\in\mathbb C),\\
0<\alpha_{\mathfrak s}A\le
m_a=n_a=\min_{z\perp e}\mathcal F_a(z,0).
\end{gathered}
\tag{136.4}
$$

The last minimum is attained on the complex two-dimensional space
$e^\perp$, hence is a minimization over four real variables. There
exists a zero-retention tangent minimizer. Neither uniqueness nor
zero retention of every tangent minimizer is asserted.

*Proof.* Convexity of $\mathcal F_a$ is Theorem 126.1. The midpoint
of $(z,g)$ and $\mathscr T(z,g)$ is $(\Pi z,0)$, so (135.5) gives

$$
\begin{aligned}
\mathcal F_a(\Pi z,0)
 &\le\tfrac12\bigl(\mathcal F_a(z,g)+\mathcal F_a(Wz,-g)\bigr)\\
 &\le\mathcal F_a(z,g)+\tfrac12\epsilon_N\mathscr B_A(z,g).
\end{aligned}
\tag{136.5}
$$

This proves (136.3) for every point of the eight-real-variable space.
To bound its remainder at an unrestricted minimizer, use the
rank-one norm identity $\|uv^\dagger\|_{\rm HS}=\|u\|\|v\|$ and
(125.3). They imply

$$
\begin{aligned}
\|H_1(z)\|_{\rm HS}&\le2A(\|z\|+1),\\
\|S_1(z)\|_{\rm HS}&\le2\tau(\|z\|+1),\\
\|X_1(z)\|_{\rm HS}+\|Y_1(z)\|_{\rm HS}
 &\le b\|H_1(z)\|_{\rm HS}
                +2|s_\theta c_\theta|\|S_1(z)\|_{\rm HS}\\
 &\le2(Ab+2|s_\theta c_\theta|\tau)(\|z\|+1),\\
\|K_-\|_{\rm HS}
 &\le A\tau+|s_\theta c_\theta|(\|D\|_{\rm HS}+bA^2)
 \le\kappa_{\mathfrak s}.
\end{aligned}
\tag{136.6}
$$

Let $(z_*,g_*)$ be any attained unrestricted minimizer from
Theorem 126.1. Its bounds (126.3), with
$M=2\sqrt2\,\overline C A$, are exactly

$$
\|z_*\|\le R_0,\qquad |g_*|\le AG_0\le G_0.
\tag{136.7}
$$

Equations (135.3), (136.6) and $A<1$ give
$\mathscr B_A(z_*,g_*)/2\le C_{\rm ref}$. Restriction to $g=0$
and (136.3) yield

$$
m_a\le n_a\le\mathcal F_a(\Pi z_*,0)
                       \le m_a+C_{\rm ref}\epsilon_N,
$$

proving (136.2). Every quantity in (136.1) comes from the fixed
source, including its actual weighted decoder bounds; it is not a
constant for a normalized collection of states.

When $\epsilon_N=0$, (135.5) proves full tangent invariance and
(136.5) proves fixed-subspace nonincrease. Apply them to the same
minimizer: its projection $(\Pi z_*,0)$ has value at most $m_a$,
so its value is $m_a$. Since $\Pi z_*\perp e$, this also attains the
restricted minimum in (136.4); the reverse inequalities follow
from inclusion of feasible sets. Positivity is (126.2).
For a complex unit $k$ making $(e,f,k)$ orthonormal, write every
transverse vector uniquely as

$$
z=(x_1+\mathrm i x_2)f+(x_3+\mathrm i x_4)k,\qquad x\in\mathbb R^4.
\tag{136.8}
$$

This proves the claimed four-variable reduction without imposing
reality on $f,z$ or $g$ in the original problem.

The convex midpoint step is the classical Reynolds averaging
intermediary: Gatermann–Parrilo,
[*Symmetry groups, semidefinite programs, and sums of squares*,
arXiv:math/0211450v1, §3, Definition 3.1 and Theorem
3.3](https://arxiv.org/pdf/math/0211450v1), prove fixed-subspace
reduction for invariant convex semidefinite problems. The paragraph
following their proof explicitly distinguishes nonconvex problems,
whose minimizers need not be symmetric. Here convexity is supplied
by the literal affine-row supremum of Theorem 126.1, and the needed
source invariance is proved by (135.4)–(135.5). Averaging is solely
an inequality between these tangent parameters. It asserts neither
convexity of the nonlinear completion image nor an averaging protocol
for installations, preparations or retention channels. Every
admissible nonlinear lift of a parameter still uses its one shared
full completion as in VI Theorem 106.3. $\square$

## 137. Original mixing sources with a square equal to the reflection

**Proposition 137.1 (A nonempty order-four family and its evaluated full tangent gap; repo-derived).**
Keep the original matrices and vectors of V Definition 54.1, with

$$
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\qquad
v_+=(1,1,-2)^{\mathsf T}/\sqrt6,\qquad
e=(1,-1,0)^{\mathsf T}/\sqrt2.
$$

For arbitrary parameters

$$
0<\chi<\pi/2,\qquad \phi\in\mathbb R,\qquad \sigma\in\{-1,1\},
$$

define the installed source control by

$$
u=\cos\chi\,\xi+e^{\mathrm i\phi}\sin\chi\,v_+,
\qquad N=\Pi-2uu^\dagger+\sigma\mathrm i\,ee^\dagger.
\tag{137.1}
$$

For every $0<d<1$ and every real $\theta$ with
$\sin(2\theta)\ne0$, this control satisfies

$$
N\in U(3),\qquad [N,P_\xi]\ne0,\qquad
N^2=W,\qquad N^4=I_3.
\tag{137.2}
$$

For every valid original eight-plus-one prefix choice in V
Theorems 92.1–92.2 and Definition 93.1, these data form an allowed
source of VI Definition 114.1. For every such source, every $0<A<1$
and every complex unit $f\perp e$, the actual full-law tangent gap is

$$
\delta_a=0,\qquad
m_a=n_a=\min_{z\perp e}\mathcal F_a(z,0)>0.
\tag{137.3}
$$

*Proof.* The three displayed source vectors are orthonormal, so
$u\in e^\perp$ and $\|u\|=1$. The orthogonal projections
$uu^\dagger,\Pi-uu^\dagger,ee^\dagger$ resolve $I_3$.
On their respective ranges $N$ has eigenvalues $-1,1,\sigma\mathrm i$.
It is unitary and its square is
$uu^\dagger+(\Pi-uu^\dagger)-ee^\dagger=W$, proving (137.2)'s
power identities. Since $N^4=I_3$ and $N^2=W$ is not scalar,
$N$ has projective order four. Directly,

$$
N\xi=-\cos(2\chi)\,\xi-e^{\mathrm i\phi}\sin(2\chi)\,v_+.
\tag{137.4}
$$

The $v_+$ coefficient is nonzero for every permitted $\chi$.
Thus $N$ does not preserve the line $\mathbb C\xi$; a unitary
commuting with $P_\xi$ would preserve that line. This proves mixing.
For example $\chi=\pi/4,\phi=0,\sigma=1$ gives $N\xi=-v_+$,
so the parameter family is nonempty.

To check the source rather than a different state collection, retain
V (91.1)'s sole preparation and its original angle:

$$
\begin{gathered}
\psi=\sqrt d\,Uq+\mathrm i\sqrt{1-d}\,Uv_-,\qquad
v_-=e,\qquad \rho_0=\psi\psi^\dagger,\\
V_j=U\exp(\mathrm i\theta W)W^j,\qquad
A_j=\tfrac12\operatorname{Ad}_{V_j},\qquad A_N=\operatorname{Ad}_N.
\end{gathered}
\tag{137.5}
$$

V Proposition 91.3 gives this original pure preparation its
five-dimensional source and full matrix response, for every
$0<d<1$. Under exactly $\sin(2\theta)\ne0$, V Theorem 92.1
states that any native basis selected there has

$$
\begin{gathered}
r_i=A_{u_i}\rho_0
 =2^{-|u_i|}U_{u_i}\rho_0U_{u_i}^\dagger\quad(1\le i\le8),\\
u_1=\varnothing,\qquad |u_i|\le7,\qquad
\operatorname{span}_{\mathbb R}\{r_1,\ldots,r_8\}
 =\mathscr S_{d/2}.
\end{gathered}
\tag{137.6}
$$

The just-proved mixing condition is exactly the hypothesis of V
Theorem 92.2. For every such basis it supplies an index $k$ with
$r_9=Nr_kN^\dagger\notin\mathscr S_{d/2}$. Every choice of such
an escaping index is valid, and its actual prefix is
$u_9=u_kN$, with $|u_9|\le8$. Hence the nine columns span
$\operatorname{Herm}_3$. Their masses remain

$$
\operatorname{Tr}r_i=2^{-|u_i|}\quad(1\le i\le8),\qquad
\operatorname{Tr}r_9=\operatorname{Tr}r_k=2^{-|u_k|}.
\tag{137.7}
$$

No basis column has been normalized or substituted by a closure
state. V Definition 93.1 keeps precisely these chronological
prefixes and its original weighted suffix effects in the four
finite tables; Theorem 93.2 uses their full trace pairing.
Its effect-basis determinant (93.9) is nonzero for the same permitted
angles, independently of which valid nine columns were selected.
These suppliers apply also at $d=2/3$; no argument here excludes that
interior value or divides by $1-3d/2$. They verify every source
condition of VI Definition 114.1 for every stated $d,\theta$ and
valid prefix choice.

Finally $N^2=W$ makes $\epsilon_N=0$ in (135.1), using exponent
two and scalar one. Theorem 136.1 now proves (137.3) with the
literal rows of that source for every permitted $A,f$.
Specifying (137.1) is a mathematical subfamily of the assumed
installed controls; it does not supply an acquisition or calibration
service. The comparison retains the original preparation (137.5),
menu, complex retention disk, terminal labels and one forward return.
Each hypothesis has one full ten-dimensional completion shared
across its emission, return and all histories, and compared
hypotheses may differ as in VI Definition 114.1. $\square$

## 138. Finite-length comparisons and the nonlinear remainder boundary

**Proposition 138.1 (Length change without decoder symmetry; repo-derived).**
For a fixed source suppose $N^r=\lambda W$ for an integer $r\ge0$
and $|\lambda|=1$. For every lift $L=(X,Y,Z)\in\mathscr V$ and
integer $L_0\ge0$, put

$$
\mathcal Q_{L_0}(L)=\max_{1\le i\le9,\ |w|\le L_0}|q_{i,w}(L)|,
\qquad \mathscr J L=(-WXW,-WYW,-WZW).
\tag{138.1}
$$

The lawful original-row relation and length-bounded consequences are

$$
\begin{gathered}
q_{i,w}(\mathscr J L)=-q_{i,wN^r}(L),\qquad
\mathcal Q_{L_0}(\mathscr J L)\le\mathcal Q_{L_0+r}(L),\\
\mathcal Q_{L_0}(L)\le\mathcal Q_{L_0+r}(\mathscr J L).
\end{gathered}
\tag{138.2}
$$

In particular, writing
$\mathcal F_{\le L_0}(z,g)=\max_{i,|w|\le L_0}|\ell_{i,w}(z,g)|$
with precisely (125.3), one has

$$
\begin{aligned}
\mathcal F_{\le L_0}(Wz,-g)&\le\mathcal F_{\le L_0+r}(z,g),\\
\mathcal F_{\le L_0}(\Pi z,0)
 &\le\tfrac12\bigl(\mathcal F_{\le L_0}(z,g)
                          +\mathcal F_{\le L_0+r}(z,g)\bigr)
 \le\mathcal F_{\le L_0+r}(z,g).
\end{aligned}
\tag{138.3}
$$

For the family of Proposition 137.1 take $r=2$. Separately, let
$K=K_{\mathfrak s}$ of (129.1) and use the actual finite family
$\mathscr W_{K,4}$ of (134.1). For all paired hypotheses in
$\mathcal P^2$ and all tangent parameters,

$$
\begin{aligned}
\Delta_{\rm all}(x,x')&=
 \max_{\substack{1\le i\le9,\ w\in\mathscr W_{K,4}\\\beta\in\{0,1\}}}
                  |p_x(u_i,w,\beta)-p_{x'}(u_i,w,\beta)|
 =\Delta_{4K+3}(x,x'),\\
\mathcal F_a(z,g)&=\max_{1\le i\le9,\ w\in\mathscr W_{K,4}}
                                              |\ell_{i,w}(z,g)|.
\end{aligned}
\tag{138.4}
$$

Consequently its common positive tangent optimum has the attained
linear-program epigraph below, with four transverse coordinates and
one epigraph variable, using the original columns of (125.4):

$$
 m_a=n_a=\min_{x\in\mathbb R^4,\ v\in\mathbb R}v
 \quad\text{subject to}\quad
 -v\le\beta_\rho+\sum_{j=1}^4U_{\rho,j+2}x_j\le v
 \quad(\rho=(i,w),\ w\in\mathscr W_{K,4}).
\tag{138.5}
$$

The finite norming family in (138.4) is the separate full-law family
of §134, not the fixed decoder $P_{\mathfrak s}$.
Neither (138.2) nor (138.4) asserts invariance of the decoder's
fixed length $L_{\mathfrak s}$ or $m_f=n_f$.

*Proof.* Equations (135.7), the chronological identity
$Q_{wN^r}=N^rQ_w=\lambda WQ_w$ and phase cancellation give the
first equality of (138.2). The appended word has length $|w|+r$
and unchanged native-label count, so it has exactly the same row
weight $a_w/2$ and unchanged prefix mass. Taking maxima gives the
first inequality; applying it to $\mathscr J L$ and using
$\mathscr J^2=I$ gives the second. The tangent lift satisfies
$L(Wz,-g)=\mathscr J L(z,g)$ by Lemma 135.2, proving the first
line of (138.3). Convexity of the finite maximum and its midpoint
then prove the second line. The comparison enlarges the length
bound; a word at the old bound need not stay inside that bound.
It therefore supplies no equality for that fixed finite decoder.

For the specified family $N^4=I_3$, so apply Corollary 134.1 with
$p=4$. Its length bound is $K+3(K+1)=4K+3$ and its two full-law
norming identities are exactly (138.4). This invocation concerns
actual histories and preserves every original weight. Original and
reduced clocks and records remain distinct even where their row
values coincide. Apply (136.4), express the transverse vector by
(136.8), and use (125.4): the four retained columns are precisely
columns $3,4,5,6$, and $g=0$ removes both retention columns.
The epigraph of the resulting finite maximum is (138.5).
Theorem 126.1 and the projection in Theorem 136.1 supply attainment.
This does not identify (138.4) with the error of $P_{\mathfrak s}$.
$\square$

**Corollary 138.2 (Only the justified nonlinear gap bound; repo-derived).**
For every source, $A,f$ in Definition 135.1, retain the original
nonlinear minima $\mu_a(\eta),\nu_a(\eta)$ of Definition 126.2
and the supplied $E,\eta_*$ of (126.7), without enlarging that
interval. Then

$$
0\le\nu_a(\eta)-\mu_a(\eta)
 \le C_{\rm ref}\epsilon_N\eta+2E\eta^2
                    \qquad(0<\eta\le\eta_*).
\tag{138.6}
$$

In particular, zero defect, including every source in Proposition
137.1, gives only

$$
0\le\nu_a(\eta)-\mu_a(\eta)\le2E\eta^2.
\tag{138.7}
$$

*Proof.* The zero-retention feasible set is contained in the full
complex-retention feasible set, so $\mu_a\le\nu_a$. The two
full-law estimates of Theorem 126.3 give on exactly its interval

$$
\nu_a(\eta)-\mu_a(\eta)
 \le\eta(n_a-m_a)+2E\eta^2.
$$

Insert (136.2) to prove (138.6); set $\epsilon_N=0$ for (138.7).
These estimates compare the original nonlinear laws, not a chosen
lift outside their image. The tangent midpoint proof establishes
no symmetry theorem for that nonlinear image. Accordingly (138.7)
does not assert equality of the nonlinear minima or determine an
endpoint type from §132. Formula (136.2) makes positive defect
necessary for a positive full tangent gap, but gives no converse.
Concrete positive-gap existence, evaluation of the original finite
gap $\delta_f$, and the nonlinear endpoint type for the order-four
family remain unresolved by these statements. All source and $A$
endpoints excluded in Definition 125.1 remain excluded. $\square$

## 追加锚（本行以下为增补区）

## 139. Exact original-image feasibility of numerical reflection averages

**Definition 139.1 (The full raw residual image and its numerical reflection).**
Fix any allowed original source of Proposition 137.1, including any
one fixed valid choice of the nine actual prefixes of V §§91–93.
Thus $N^2=W=I_3-2ee^\dagger$, $N^4=I_3$, $e=t/\|t\|$, and
$\Pi=I_3-ee^\dagger$. Retain the source constants of VI (106.3):

$$
\tau=\|t\|>0,\qquad b=\frac{3+2\sqrt2}{12},\qquad
s=\sin\theta,\quad c=\cos\theta,\quad sc\ne0.
\tag{139.1}
$$

For arbitrary $0<A<1$, complex unit $f\perp e$, and
$\eta>0$ with $A^2+\eta^2\le1$, set $h_0=Ae+\eta f$. On the
entire original domain $\mathcal P$ of VI (114.1), define

$$
\begin{gathered}
R_x=\mathcal O_{\mathfrak s}(\gamma,h)
              -\mathcal O_{\mathfrak s}(0,h_0),\qquad x=(\gamma,h),\\
\mathscr D_\eta=\{R_x:|\gamma|\le1,\ \|h\|\le1\},\qquad
\mathscr D_\eta^-=\{R_x:|\gamma|\le1,\ \|h\|\le1,
                                      \operatorname{Re}(e^\dagger h)\le0\},\\
(Jy)_{i,w,\beta}=-y_{i,wN^2,\beta},\qquad
P_Jy=\tfrac12(y+Jy),\qquad
\|y\|_\infty=\sup_{i,w,\beta}|y_{i,w,\beta}|.
\end{gathered}
\tag{139.2}
$$

The indices include every original history and both terminal labels.
In particular the defining raw probabilities retain the original
subnormalised $r_i$ and the exact factor $a_w/2$ of VI (114.3).
Each physical parameter pair is realized by one full ten-dimensional
completion shared across emission, the single forward return and all
histories, by VI Theorem 106.3; compared pairs may use different such
completions. The maps $J,P_J$ are numerical comparisons of original
rows, with no additional physical operation or identification of clocks.

For the real lift space $\mathscr V$ of VI Definition 116.1 write

$$
\begin{aligned}
\mathcal Q(L)_{i,w,\beta}&=(2\beta-1)q_{i,w}(L),\\
L_x&=(A_h-A_{h_0},\ B_h-B_{h_0},\ \gamma K_h),\\
\mathscr J(X,Y,Z)&=(-WXW,-WYW,-WZW).
\end{aligned}
\tag{139.3}
$$

Here $A_h,B_h,K_h$ are exactly VI (114.2), so $R_x=\mathcal Q(L_x)$.
Equation (135.7) gives $J\mathcal Q(L)=\mathcal Q(\mathscr J L)$.
On the row range $\mathcal U=\mathcal Q(\mathscr V)$, one therefore
has $J^2=I$, $P_J^2=P_J$ and $\|Jy\|_\infty=\|y\|_\infty$.
Indeed appending $N^2$ leaves $a_w$ unchanged and is norm
nonincreasing by restriction of the supremum; applying this twice
and using $N^4=I_3$ proves the reverse inequality on $\mathcal U$.
Words and clocks remain distinct even when their numerical rows agree.

For $y\in\mathcal U$, use the fixed finite linear decoders of
VI Proposition 118.2 on its outcome-$1$ entries. Denote their
outputs by $\mathsf D_Hy,\mathsf D_Sy,\mathsf D_Vy$, and define
the reference-added decoded coordinates

$$
\widehat H(y)=h_0h_0^\dagger+\mathsf D_Hy,\qquad
\widehat S(y)=\mathsf S_{h_0}+\mathsf D_Sy,\qquad
\widehat V(y)=\mathsf D_Vy.
\tag{139.4}
$$

These are linear decoding followed by addition of fixed matrices;
being defined does not assert physical realizability. For $y=R_x$
they equal $hh^\dagger,\mathsf S_h,\Pi_v(\gamma K_h)$, respectively,
where $\mathsf S_h=\mathrm i(ht^\dagger-th^\dagger)$ and $v$ is
the fixed decoder vector of VI (118.4).

**Theorem 139.2 (Complete feasibility classification; repo-derived).**
For every source and every parameter in Definition 139.1, every
$x=(\gamma,h)\in\mathcal P$ and every $0<\lambda\le1$, the
following equivalence holds on the full original domain:

$$
(1-\lambda)R_x+\lambda JR_x\in\mathscr D_\eta
\quad\Longleftrightarrow\quad
\gamma=0,\qquad
h=\epsilon Ae+\eta\zeta f,
\quad \epsilon\in\{-1,1\},\quad |\zeta|=1.
\tag{139.5}
$$

In the feasible case $JR_x=R_x$ and the representing parameter pair
is uniquely $x$. If $x$ is restricted to
$\operatorname{Re}(e^\dagger h)\le0$, only $\epsilon=-1$ occurs;
the same equivalence then holds with $\mathscr D_\eta^-$ as target.
In particular the signed reflection ($\lambda=1$) and the midpoint
($\lambda=1/2$) are feasible exactly in the same cases. Uniqueness
here concerns $(\gamma,h)$, not the full completion behind a given $h$.

*Proof.* Put $\kappa=1-2\lambda$, write
$h=\alpha e+v_\perp$ with $v_\perp\perp e$, and suppose the left
side is $R_{x'}$ for $x'=(\gamma',h')\in\mathcal P$. Write
$h'=\alpha'e+v'_\perp$. By (139.3) its lift is equal, modulo the
common kernel of VI Lemma 116.2, to
$(1-\lambda)L_x+\lambda\mathscr J L_x$.

The maps (118.8) on the entire lift space give
$\mathfrak H(L)=(X+Y)/b$ and
$\mathfrak S(L)=\Pi_v(X-s^2(X+Y))/(sc)$.
The decoder vector $v$ is perpendicular to $t$, so $Wv=v$;
consequently $\Pi_v(WMW)=W\Pi_v(M)W$. Both maps therefore
intertwine $\mathscr J$ with $M\mapsto-WMW$. Since
$W\mathsf S_{h_0}W=-\mathsf S_{h_0}$, (139.4) implies

$$
\begin{aligned}
h'h'^\dagger
 &=(1-\lambda)hh^\dagger-\lambda Whh^\dagger W
                  +2\lambda(A^2ee^\dagger+\eta^2ff^\dagger),\\
\mathsf S_{h'}
 &=(1-\lambda)\mathsf S_h-\lambda W\mathsf S_hW.
\end{aligned}
\tag{139.6}
$$

In the decomposition $\mathbb Ce\oplus e^\perp$, the right side
of the first line has diagonal blocks
$\kappa|\alpha|^2+2\lambda A^2$ and
$\kappa v_\perp v_\perp^\dagger+2\lambda\eta^2ff^\dagger$,
and upper-right block $\alpha v_\perp^\dagger$.
The second line, using

$$
\mathsf S_h=-2\tau\operatorname{Im}(\alpha)ee^\dagger
 +\mathrm i\tau(v_\perp e^\dagger-ev_\perp^\dagger),
\tag{139.7}
$$

first forces
$v'_\perp=v_\perp$ and
$\operatorname{Im}\alpha'=\kappa\operatorname{Im}\alpha$.
The transverse block of the first line now gives

$$
v_\perp v_\perp^\dagger=\eta^2ff^\dagger.
\tag{139.8}
$$

Since $\eta>0$, this means $v_\perp=\eta\zeta f$ for one
$|\zeta|=1$, and $v_\perp\ne0$. The upper-right block gives
$\alpha'v_\perp^\dagger=\alpha v_\perp^\dagger$, hence
$\alpha'=\alpha$. As $\lambda>0$, (139.7) then makes $\alpha$
real. The $ee^\dagger$ entry of (139.6) gives $\alpha^2=A^2$.
Thus $h'=h=\epsilon Ae+\eta\zeta f$.

It remains to exclude every nonzero complex retention. The $Z$
component of the common-kernel relation says, for some real $y$,

$$
\gamma'K_h-\gamma\bigl((1-\lambda)K_h-\lambda WK_hW\bigr)
                                      =\mathrm i yI_3.
\tag{139.9}
$$

Use the actual source functional $\ell(M)=\operatorname{Tr}(FM)$
of VI Lemma 116.3. Its $F$ is supported on $e^\perp$, so
$WFW=F$. It annihilates scalars, and
$\ell(K_h)=\mathrm i scq_h$ with $q_h\ge5/8-b>0$ on the whole
completion ball. Applying $\ell$ to (139.9) yields
$\gamma'=\kappa\gamma$, including complex $\gamma,\gamma'$.
Let $K_h^-=(K_h-WK_hW)/2$. Taking the $W$-odd part of
(139.9) gives $(\gamma'-\gamma)K_h^-=0$. If
$a=\epsilon A$ and $v_\perp=\eta\zeta f$, the original formula
for $K_h$ gives

$$
K_h^-=(\tau s^2-\mathrm i scba)ev_\perp^\dagger
             +(\tau c^2-\mathrm i scba)v_\perp e^\dagger.
\tag{139.10}
$$

Its first coefficient has strictly positive real part $\tau s^2$,
and $v_\perp\ne0$, so $K_h^-\ne0$. Therefore
$-2\lambda\gamma=0$, proving $\gamma=\gamma'=0$.
This proves necessity and uniqueness of the representing pair.

Conversely for either sign and every $|\zeta|=1$, the diagonal
blocks of $hh^\dagger-h_0h_0^\dagger$ vanish, and
$\mathsf S_h-\mathsf S_{h_0}$ has only off-diagonal blocks.
Both are fixed by $M\mapsto-WMW$. With $\gamma=0$, (118.9)
then makes $L_x$ fixed by $\mathscr J$. Hence $JR_x=R_x$, and
all averages in (139.5) equal that original residual. Its norm
condition is $\|h\|^2=A^2+\eta^2\le1$. Since $A>0$, exactly
the negative sign lies in the stated half-ball. This also proves
the signed-reflection and midpoint consequences. $\square$

## 140. A disk of actual-law mixtures outside every single-completion image

**Theorem 140.1 (Affine disk, decoded rank and exact physical boundary; repo-derived).**
For every source and every $A,f$ in Definition 139.1, suppose

$$
0<\eta\le\min\{A,\sqrt{1-A^2}\}.
\tag{140.1}
$$

For $|\zeta|\le1$ put
$h_\zeta=-Ae+\eta\zeta f$ and $Y_\zeta=P_JR_{(0,h_\zeta)}$.
Then $\zeta\mapsto Y_\zeta$ is an injective real-affine map of
the closed complex unit disk into $\mathcal U$, and $JY_\zeta=Y_\zeta$.
Its reference-added decoded coordinates are exactly

$$
\begin{aligned}
M_\zeta:=\widehat H(Y_\zeta)
 &=A^2ee^\dagger+\eta^2ff^\dagger
             -A\eta(\bar\zeta ef^\dagger+\zeta fe^\dagger),\\
\widehat S(Y_\zeta)
 &=\mathrm i\tau\eta(\zeta fe^\dagger-\bar\zeta ef^\dagger),\\
\widehat V(Y_\zeta)&=0.
\end{aligned}
\tag{140.2}
$$

The algebraic normal-form recovery (118.6), applied to these
coordinates, gives retention $0$ and retention-weighted vector $0$.
For $|\zeta|=1$, $Y_\zeta=R_{(0,h_\zeta)}$ is an actual
zero-retention residual in $\mathscr D_\eta^-$. For $|\zeta|<1$,
$Y_\zeta$ is a mathematical convex combination of two boundary
residuals, but belongs to neither $\mathscr D_\eta$ nor
$\mathscr D_\eta^-$. Thus no single original completion realizes
an interior point, even with arbitrary complex retention in the
entire disk and arbitrary completion in the entire original ball.

*Proof.* In (139.6) put $\lambda=1/2$, $\gamma=0$ and
$h=h_\zeta$. Formula (139.7) and the two diagonal blocks give
(140.2). More explicitly the lift whose rows are $Y_\zeta$ is

$$
\left(
 s^2b(M_\zeta-h_0h_0^\dagger)
            +sc(\widehat S(Y_\zeta)-\mathsf S_{h_0}),\quad
 c^2b(M_\zeta-h_0h_0^\dagger)
            -sc(\widehat S(Y_\zeta)-\mathsf S_{h_0}),\quad0
\right).
\tag{140.3}
$$

Every term in this lift is real-affine in $\zeta$, proving
real-affineness in the full original row space. The difference of
the second decoded coordinates at $\zeta,\zeta'$ has norm
$\sqrt2\tau\eta|\zeta-\zeta'|$, so the map is injective.
Projection on $\mathcal U$ gives $J$-fixity. The matrix $M_\zeta$
is positive semidefinite, with trace $A^2+\eta^2\le1$; for example
its two-dimensional matrix in the basis $(e,f)$ is

$$
\begin{pmatrix}A^2&-A\eta\bar\zeta\\
                -A\eta\zeta&\eta^2\end{pmatrix}.
\tag{140.4}
$$

Consequently the denominator of the recovery formula satisfies
$5/8-b\ell(M_\zeta)\ge5/8-b>0$, because $F\preceq I_3$.
With $\widehat V=0$, (118.6) therefore returns $\gamma=0$ and
$z_{\gamma,h}=0$. This calculation is a statement about decoded
coordinates; the existence of a vector with outer product
$M_\zeta$ is a separate condition.

On the boundary (140.2) is precisely the normal form of
$(0,h_\zeta)$, and Theorem 139.2 gives the asserted actual residual.
For an interior point write $\zeta=r\omega$, where $0\le r<1$
and $|\omega|=1$, choosing any $\omega$ when $r=0$.
Real-affineness proves the literal full-vector identity

$$
Y_\zeta=\frac{1+r}{2}R_{(0,-Ae+\eta\omega f)}
       +\frac{1-r}{2}R_{(0,-Ae-\eta\omega f)}.
\tag{140.5}
$$

Both coefficients are strictly positive. Adding the same reference
law to both sides expresses the corresponding mathematical mixture
of two actual original laws, each using its own single shared full
completion. No lottery, randomization or preparation mixture is
installed by this vector identity.

For $r<1$ the determinant of (140.4) is
$A^2\eta^2(1-r^2)>0$, so $M_\zeta$ has rank two.
If $Y_\zeta=R_{(\gamma,h)}$ for any $|\gamma|\le1$, $\|h\|\le1$,
the full-domain linear decoder (139.4) would force
$hh^\dagger=M_\zeta$, impossible for a rank-at-most-one outer
product. This argument excludes the entire original domain,
including parameters not in the reflected half-ball. $\square$

The rank-one versus positive-semidefinite lifting used as an
intermediary here is explicitly described by Candès–Strohmer–Voroninski,
[*PhaseLift: Exact and Stable Signal Recovery from Magnitude
Measurements*, arXiv:1109.4499v1, §§1.1–1.3](https://arxiv.org/pdf/1109.4499v1).
Their §1.1 distinguishes the rank constraint from its trace-minimizing
semidefinite relaxation; §1.2's recovery theorem uses independent
uniform random measurement vectors, and §1.3 discusses that recovery
geometry. No random-measurement exactness theorem supplies (140.2),
which follows from this source's original lift and row kernel.

**Theorem 140.2 (Quadratic separation from the entire original image; repo-derived).**
Fix any of the finite outer-product decoders already supplied by
VI Proposition 118.2. Write its outcome-$1$ input as
$y_{\rm fin}$ and its map as $\mathsf D_H$; its defining identity
and source constant are

$$
\begin{gathered}
\mathsf D_H\bigl((q_{i,w}(X,Y,Z))_{i,\,|w|\le L_{\mathfrak s}}\bigr)
                                      =(X+Y)/b
                  \quad\text{for every }(X,Y,Z)\in\mathscr V,\\
B_H=\|\mathsf D_H\|_{\ell^\infty\to\mathrm{HS}}\in(0,\infty).
\end{gathered}
\tag{140.6}
$$

The finitely many real coefficients of that decoder determine
$B_H$; it depends only on the fixed source and the fixed decoder.
For $|\zeta|\le1$ let

$$
\lambda_-(\zeta)=\frac{A^2+\eta^2-
 \sqrt{(A^2-\eta^2)^2+4A^2\eta^2|\zeta|^2}}2,
\qquad \delta_\zeta=\eta^2(1-|\zeta|^2).
\tag{140.7}
$$

Under (140.1), in the original full raw-law supremum norm,

$$
\begin{aligned}
\frac{\delta_\zeta}{2B_H}
 &\le\frac{\lambda_-(\zeta)}{B_H}
 \le\operatorname{dist}_\infty(Y_\zeta,\mathscr D_\eta)\\
 &\le\operatorname{dist}_\infty(Y_\zeta,\mathscr D_\eta^-)
 \le\frac b2\delta_\zeta.
\end{aligned}
\tag{140.8}
$$

At the center the stronger lower bound is
$\operatorname{dist}_\infty(Y_0,\mathscr D_\eta)\ge\eta^2/B_H$.
In particular every interior point has strictly positive distance
from the entire original image, of quadratic order in $\eta$ with
the displayed $1-|\zeta|^2$ factor. These are bounds, not a claim
of equality of the constants or of the optimal distance.

*Proof.* The full-space identity in (140.6) is the first map of
VI (118.8) factored through finitely many actual rows. Every one
of its matrix coordinates annihilates the common kernel, so the
finite dual-span construction in VI Proposition 118.2 proves the
identity on all of $\mathscr V$, before any restriction to physical
pairs. A finite linear map has finite operator norm; it is nonzero
by its value at $(I_3,0,0)$, so $B_H>0$.

For every original $x=(\gamma,h)$, subtract the lift (140.3) from
$L_x$ and apply this full-space identity. It gives

$$
\|hh^\dagger-M_\zeta\|_{\rm HS}
 \le B_H\|(R_x-Y_\zeta)_{\rm fin}\|_\infty
 \le B_H\|R_x-Y_\zeta\|_\infty.
\tag{140.9}
$$

This directly justifies the decoder at the virtual lift. An
estimate stated only for physical pairs would not justify (140.9).
The two nonzero-block eigenvalues of $M_\zeta$ are
$\lambda_+\ge\lambda_-\ge0$, with $\lambda_-$ given by (140.7).
For any $h\in\mathbb C^3$ choose a unit $u$ in
$\operatorname{span}_{\mathbb C}\{e,f\}$ perpendicular to $h$.
There is such a vector since this span has complex dimension two.
Then

$$
\|M_\zeta-hh^\dagger\|_{\rm HS}
 \ge|u^\dagger(M_\zeta-hh^\dagger)u|
 =u^\dagger M_\zeta u\ge\lambda_-.
\tag{140.10}
$$

Thus (140.9) bounds every pair in the full complex domain, regardless
of its retention. Taking the infimum gives the lower distance bound.
Since
$\lambda_+\lambda_-=A^2\eta^2(1-|\zeta|^2)$ and
$0<\lambda_+\le A^2+\eta^2\le2A^2$, one obtains
$\lambda_-\ge\delta_\zeta/2$. At $\zeta=0$, (140.1) instead gives
$\lambda_-=\min(A^2,\eta^2)=\eta^2$, proving the sharper assertion.

For the upper bound use the actual reflected-domain witness
$x_\zeta=(0,-Ae+\eta\zeta f)$. Its vector is in the original ball.
Its skew coordinate equals (140.2), and
$M_\zeta-h_\zeta h_\zeta^\dagger=\delta_\zeta ff^\dagger$.
The virtual-minus-physical lift is consequently
$(s^2b\delta_\zeta ff^\dagger,c^2b\delta_\zeta ff^\dagger,0)$.
Its outcome-$1$ row is exactly

$$
\frac{a_wb\delta_\zeta}{2}\operatorname{Tr}\!\left[
 r_i\left(s^2Q_w^\dagger ff^\dagger Q_w
       +c^2WQ_w^\dagger ff^\dagger Q_wW\right)\right].
\tag{140.11}
$$

The matrix in parentheses lies between $0$ and $I_3$.
Since $a_w\le1$ and $\operatorname{Tr}r_i\le1$ for every actual
prefix, this row is between $0$ and $b\delta_\zeta/2$.
The outcome-$0$ row is its negative, so the same bound holds in the
full original supremum norm. Infimizing over the reflected domain
and then using $\mathscr D_\eta^-\subseteq\mathscr D_\eta$ proves
the rest of (140.8). Strict positivity in the interior follows
from $A\eta>0$ and $|\zeta|<1$. $\square$

The matrix-distance intermediary is also the lift in Balan–Zou,
[*On Lipschitz Analysis and Lipschitz Synthesis for the Phase Retrieval
Problem*, arXiv:1506.02092v1, §2.2, (9)–(11) and Theorems
2.3–2.4](https://arxiv.org/pdf/1506.02092v1): (9)–(11) relate
intensity data to a linear map on selfadjoint matrices and the
rank-at-most-one positive cone. Theorem 2.3 characterizes a
phase-retrievable frame by its kernel and a lower comparison;
Theorem 2.4 gives an upper comparison under that frame assumption.
Here the needed full-space decoder is (140.6), proved from the
original source rows, and (140.10) is the direct two-dimensional
rank obstruction. No phase-retrievable-frame assumption is imported.

## 141. A concrete complex member and the nonlinear optimization boundary

**Proposition 141.1 (An explicit original source with actual nine prefixes; repo-derived).**
In the original matrices of V Definition 54.1 put

$$
\begin{gathered}
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\quad
v_+=(1,1,-2)^{\mathsf T}/\sqrt6,\quad
e=(1,-1,0)^{\mathsf T}/\sqrt2,\\
d=\tfrac12,\qquad \theta=\tfrac\pi4,\qquad
N=-(\xi v_+^\dagger+v_+\xi^\dagger)+\mathrm i ee^\dagger,\\
(u_1,\ldots,u_9)
 =(\varnothing,0,1,00,10,000,010,100,N),\\
A=\tfrac12,\qquad f=(\xi+\mathrm i v_+)/\sqrt2,
                    \qquad 0<\eta\le\tfrac12.
\end{gathered}
\tag{141.1}
$$

These data are an allowed source and parameters for Theorems
139.2, 140.1 and 140.2 on this entire nonzero $\eta$ interval.
The transverse vector is genuinely complex: no common scalar
phase makes it real. Every column is its actual weighted prefix
event, and the ninth is the chronological single call $N$ after
the empty prefix.

*Proof.* The vectors $(\xi,v_+,e)$ are a real orthonormal basis.
This is (137.1) with $\chi=\pi/4$, $\phi=0$, $\sigma=1$.
Thus $N\in U(3)$, $N\xi=-v_+$, $N^2=W$ and $N^4=I_3$.
The mixing condition follows from $N\xi\perp\xi$, and
$0<d<1$, $\sin(2\theta)=1$. Use exactly the sole preparation
of V (91.1):

$$
\psi=2^{-1/2}Uq+\mathrm i2^{-1/2}Ue,\qquad
\rho_0=\psi\psi^\dagger.
\tag{141.2}
$$

V Proposition 91.3 supplies its original five-dimensional CPTP
source and full matrix response, with no additional preparation.
For completeness, the particular actual prefixes in (141.1) can
be checked directly. In the ordered basis $(\xi,v_+,e)$, removing
only the common scalar phase from $V_0,V_1$ for the purpose of
computing their conjugations gives

$$
\psi=\begin{pmatrix}1/2\\(-1+\mathrm i\sqrt6)/4\\
                         (\sqrt3+\mathrm i\sqrt2)/4\end{pmatrix},
\quad V'_0=\begin{pmatrix}
1&0&0\\0&-1/2&-\mathrm i\sqrt3/2\\
0&\sqrt3/2&-\mathrm i/2
\end{pmatrix},
\quad V'_1=V'_0\operatorname{diag}(1,1,-1),
\quad N=\begin{pmatrix}0&-1&0\\-1&0&0\\0&0&\mathrm i\end{pmatrix}.
\tag{141.3}
$$

For a Hermitian matrix $M$ in this basis define the real column

$$
\mathbf c(M)=(M_{11},M_{22},M_{33},
 \operatorname{Re}M_{12},\operatorname{Im}M_{12},
 \operatorname{Re}M_{13},\operatorname{Im}M_{13},
 \operatorname{Re}M_{23},\operatorname{Im}M_{23})^{\mathsf T}.
\tag{141.4}
$$

For each of the first eight words let
$\psi_{b_1\cdots b_n}=V'_{b_n}\cdots V'_{b_1}\psi$ and
$r_i=2^{-|u_i|}\psi_{u_i}\psi_{u_i}^\dagger$; let
$r_9=N\rho_0N^\dagger$. Multiplication of the displayed matrices
and the real coordinates (141.4) gives

$$
\det\bigl(\mathbf c(r_1),\ldots,\mathbf c(r_9)\bigr)
                 =\frac{11421+12960\sqrt6}{2^{41}}>0.
\tag{141.5}
$$

Thus the nine actual columns span $\operatorname{Herm}_3$.
Each of the first eight belongs to $\mathscr S_{1/4}$ by
V Theorem 92.1; since (141.5) makes them independent, they form
one of that theorem's valid native bases. The escape in
V Theorem 92.2 is here already at $k=1$, because

$$
\operatorname{Tr}(P_\xi\rho_0)=\tfrac14,\qquad
\operatorname{Tr}(P_\xi N\rho_0N^\dagger)=\tfrac7{16}\ne\tfrac14.
\tag{141.6}
$$

Their raw masses are exactly $2^{-|u_i|}$ for $i\le8$ and $1$
for $i=9$. V Definition 93.1 uses precisely these prefixes with
its original eight suffixes, trace row and weighted tables;
its effect-basis determinant (93.9) is nonzero at $\theta=\pi/4$.
Consequently these are the original source suppliers of
VI Definition 114.1, with actual prefixes, both labels and the
original schedules. The scalar phase removed in (141.3) cancels
inside the same conjugations; it changes no installed control,
record basis or record phase.

VI (106.3) gives $t=\tau e$, $\tau>0$, for this same source.
The chosen $f$ is a complex unit in $e^\perp$. Its coefficients
along the two real vectors $\xi,v_+$ have ratio $\mathrm i$;
a common phase making both real would make that ratio real,
a contradiction. Finally $A=1/2$ and $0<\eta\le1/2$ imply
$\eta\le A$ and $A^2+\eta^2\le1/2<1$. Thus $h_0$ and all
$h_\zeta$ lie in the original completion ball. VI Theorem 106.3
realizes each by a full ten-dimensional completion with all five
prescribed ready columns, shared within its hypothesis across
emission, return and every history. This proves all the claimed
admissibility conditions without substituting a normalized state
collection for the original raw laws. $\square$

**Proposition 141.2 (Scope of the separation and the remaining optimization question).**
The source-image distances in (140.8) do not supply a lower bound
on the nonlinear optimum difference $\nu_a-\mu_a$ of §126.
They supply no nonlinear minimizer, equality of nonlinear minima,
positive physical optimum gap, or endpoint type from §132.
For the sources considered here the applicable bound on that
optimum difference remains (138.7), on its stated interval.
An actual source-specific global nonlinear argmin and active-row
certificate, or a concrete positive-gap source outside this
reflection obstruction, is a separate unresolved mathematical
requirement.

*Proof.* The infima in $\mu_a,\nu_a$ are norms of actual residuals
in their respective physical parameter sets. In contrast, (140.8)
is the distance of a specified interior vector $Y_\zeta$ from all
physical residuals, and Theorem 140.1 excludes that vector from
the feasible image. There is no minimizing or active-row identity
in (139.5), (140.2) or (140.8) relating this external distance to
either physical infimum. The available comparison of those two
infima is precisely Corollary 138.2. The classification in
Theorem 139.2 describes feasibility of numerical averages and
does not change either optimization domain.

The relevant convexity intermediary is Gatermann–Parrilo,
[*Symmetry groups, semidefinite programs, and sums of squares*,
arXiv:math/0211450v1, §3, Definition 3.1 and Theorem
3.3](https://arxiv.org/pdf/math/0211450v1). Their theorem assumes
invariance of the feasible semidefinite set and objective under
a finite orthogonal group representation; convexity makes the
Reynolds average feasible. The paragraph following the proof
explicitly distinguishes the nonconvex case, where symmetric
minimizers need not exist. Here Theorem 140.1 gives the exact
source-specific rank-two obstruction, and Theorem 139.2 classifies
all feasible numerical averages, beyond a general nonconvexity
caveat. The literature supplies these intermediate ideas, not a
global nonlinear certificate for the present original source.
All theorems above are conditional on their stated original source
and return premises and make no assertion of global originality
or resolution of an external named open problem. $\square$

## 追加锚（本行以下为增补区）
## 142. An order-three source and its literal length-two decoder

**Definition 142.1 (The order-three member).**
Use the original source of V Definition 91.1, with the sole preparation
$\psi=2^{-1/2}Uq+\mathrm i2^{-1/2}Ue$, where the present
$e=(1,-1,0)^{\mathsf T}/\sqrt2$ is V's vector $f$. In the ordered
orthonormal basis $(\xi,v_+,e)$ of (141.1), fix

$$
\begin{gathered}
d=\tfrac12,\quad\theta=\tfrac\pi4,\quad W=\operatorname{diag}(1,1,-1),\qquad
N=\begin{pmatrix}-1/2&\mathrm i\sqrt3/2&0\\
\mathrm i\sqrt3/2&-1/2&0\\0&0&1\end{pmatrix},\\
\psi=\begin{pmatrix}1/2\\(-1+\mathrm i\sqrt6)/4\\
(\sqrt3+\mathrm i\sqrt2)/4\end{pmatrix},\qquad
V=\begin{pmatrix}1&0&0\\0&-1/2&-\mathrm i\sqrt3/2\\
0&\sqrt3/2&-\mathrm i/2\end{pmatrix},\\
U_0=V,\quad U_1=VW,\quad U_N=N,\qquad
U_{b_1\cdots b_k}=U_{b_k}\cdots U_{b_1},\quad U_\varnothing=I_3,\\
(u_1,\ldots,u_9)=(\varnothing,0,1,00,10,000,010,100,N),\\
\kappa(u)=\#\{j:u_j\in\{0,1\}\},\qquad
r_i=2^{-\kappa(u_i)}U_{u_i}\psi\psi^\dagger U_{u_i}^\dagger,\\
\mathcal W_2=(\varnothing,0,1,N,00,01,0N,10,11,1N,N0,N1,NN),\\
a_w=2^{-\kappa(w)},\qquad Q_w=U_wV,\qquad
\rho(i,w)=13(i-1)+\operatorname{pos}_{\mathcal W_2}(w).
\end{gathered}
\tag{142.1}
$$

Here $V=e^{-\mathrm i\pi/4}V_0$ is used only inside system
conjugations. This common scalar cancels from every original
probability, including mixed histories containing $N$; it is not
a rotation of the retained record. Keep all original schedules,
clocks, labels and installed operations. Every occurrence of $0$ or
$1$ denotes its original random label, with no label selection.
In the present coordinates the original return constants are

$$
\begin{gathered}
b=\frac{3+2\sqrt2}{12},\qquad t=\tau e,\qquad
\tau=\frac{2+\sqrt2}{8},\\
D=\begin{pmatrix}1/2&-1/4&0\\-1/4&1/8&0\\0&0&3/8\end{pmatrix},
\qquad \|D\|_{\rm HS}=\frac{\sqrt{34}}8,\\
A=\tfrac12,\qquad f=(\xi+\mathrm i v_+)/\sqrt2,\qquad
h_0(\eta)=Ae+\eta f.
\end{gathered}
\tag{142.2}
$$

**Theorem 142.2 (Nine actual columns and the complete scalar kernel; repo-derived).**
The source (142.1) is allowed by VI Definition 114.1. Its ninth
prefix is the required escape from $\mathscr S_{1/4}$. With the
coordinate map $\mathbf c$ in (141.4), its weighted source determinant is

$$
\det(\mathbf c(r_1),\ldots,\mathbf c(r_9))
 =\frac{34263+45684\sqrt2+103680\sqrt3+38880\sqrt6}{2^{43}}>0.
\tag{142.3}
$$

The 117 literal rows $q_{i,w}$ of VI (116.2), with $w\in\mathcal W_2$,
have real rank 34 on the full 36-dimensional lift
$\operatorname{Herm}_3\oplus\operatorname{Herm}_3\oplus M_3(\mathbb C)$.
Their kernel is precisely

$$
\mathscr K=\{(xI_3,-xI_3,\mathrm i yI_3):x,y\in\mathbb R\}.
\tag{142.4}
$$

Thus $L_{\mathfrak s}=2$ is a valid choice for VI Proposition 118.2.
For this choice $d_f$ is exactly the maximum of the absolute 117
original outcome-$1$ differences; each corresponding outcome-$0$
difference is its negative.

*Proof.* The first two coordinates of $N$ have eigenvalues
$e^{2\pi\mathrm i/3}$ and $e^{-2\pi\mathrm i/3}$, while $Ne=e$.
Consequently $N$ is unitary of order three, and $N^2\ne W$, since
$N^2e=e$ and $We=-e$. Also $[N,P_\xi]\ne0$. The assumptions
$0<d<1$ and $\sin(2\theta)\ne0$ hold. V Proposition 91.3 gives
the sole preparation's original five-dimensional source and full
matrix response. Multiplying the matrices in (142.1) gives (142.3)
and

$$
\operatorname{Tr}(P_\xi r_1)=\tfrac14,\qquad
\operatorname{Tr}(P_\xi r_9)=\frac{25+12\sqrt2}{64}>\tfrac14,
\qquad\operatorname{Tr}r_9=1.
\tag{142.5}
$$

The first eight columns lie in $\mathscr S_{1/4}$ by V Theorem 92.1;
(142.3) makes them independent, and (142.5) proves the escape of the
literal prefix $N$. Their masses are $2^{-|u_i|}$ for $i\le8$ and
$1$ for $i=9$, without normalization. These are the suppliers in
V §§92–93 and VI Definition 114.1. Applying VI (106.3), with
$a_+=(1/\sqrt2,-1/(2\sqrt2),0)^{\mathsf T}$, gives (142.2).

Here is an exact rank certificate. Let $E_{ab}$ be the matrix units,
and order the real Hermitian basis as

$$
\mathcal H=(E_{11},E_{22},E_{33},E_{12}+E_{21},
 \mathrm i(E_{12}-E_{21}),E_{13}+E_{31},
 \mathrm i(E_{13}-E_{31}),E_{23}+E_{32},\mathrm i(E_{23}-E_{32})).
\tag{142.6}
$$

Order the complex-matrix real basis as
$\mathcal Z=(E_{11},\mathrm iE_{11},E_{12},\mathrm iE_{12},\ldots,
E_{33},\mathrm iE_{33})$, with matrix units in row order. Let
$\mathcal L$ have row $\rho(i,w)$ equal to

$$
\bigl((q_{i,w}(H,0,0))_{H\in\mathcal H},
(q_{i,w}(0,H,0))_{H\in\mathcal H},
(q_{i,w}(0,0,Z))_{Z\in\mathcal Z}\bigr).
\tag{142.7}
$$

Let $T$ be the submatrix in the first 34 rows and all columns except
columns 3 and 36. All entries of $\mathcal L$ lie in
$\mathbb Z[1/2,\sqrt2,\sqrt3]$. Reduce this ring to $\mathbb F_{97}$
by $\sqrt2\mapsto14$, $\sqrt3\mapsto10$; their squares are $2,3$
modulo 97. In forming complex matrices one can equivalently use
$\mathrm i\mapsto22$, whose square is $-1$. Gaussian elimination
on $T$ uses the successive row swaps
$(22,23),(23,24),(24,25),(25,26)$ and gives the following pivot residues:

$$
\begin{aligned}
(&85,37,16,57,36,37,54,37,42,38,83,31,16,50,34,38,53,\\
 &30,11,93,53,10,22,78,38,32,80,92,36,7,83,21,88,32).
\end{aligned}
\tag{142.8}
$$

For precision, at step $j$ swap the indicated rows if there is a
swap with first coordinate $j$, retain the pivot row unscaled, and
replace every subsequent entry by
$T_{kl}-T_{kj}T_{jj}^{-1}T_{jl}$ for $k,l>j$.
The product of (142.8) is $3$ modulo 97; the four swaps have positive
combined sign. Thus $\det T\not=0$. This calculation uses the
original factors $a_w/2$ and original $r_i$ in (142.7).
Every row annihilates (142.4) directly, so the rank is at most 34;
the minor proves equality and the exact kernel claim. The maps
VI (118.8), as well as the retention functionals VI (116.11),
annihilate this kernel. They therefore factor through these 117 rows,
which proves the asserted decoder length. The coordinate minor proves
rank only: neither it nor an inverse-coordinate norm replaces $d_f$.
The two-label assertion follows from VI (114.3). $\square$

## 143. Exact algebraic witnesses for a strict finite tangent gap

**Definition 143.1 (Coefficients in all complex tangent directions).**
Use Definition 125.1 with (142.1)–(142.2) and $L_{\mathfrak s}=2$.
For $z=(x_1+\mathrm i x_2)\xi+(x_3+\mathrm i x_4)v_+
 +(x_5+\mathrm i x_6)e$ and $g=y_1+\mathrm i y_2$, write

$$
\ell_{i,w}(z,g)=\beta_{i,w}+U_{i,w}x+V_{i,w}y.
\tag{143.1}
$$

All eight real coordinates are unrestricted. This is a change of
coordinates for (125.4), not a restriction to real completions.
For a fully specified algebraic evaluation of these coefficients put

$$
\begin{aligned}
H(z)&=-\tfrac12(ez^\dagger+ze^\dagger),&
S(z)&=\mathrm i\tau(ze^\dagger-ez^\dagger),\\
X_1(z)&=\tfrac12\{b[H(z)+H(f)]+S(z)-S(f)\},&
Y_1(z)&=\tfrac12\{b[H(z)+H(f)]-S(z)+S(f)\},\\
K_-&=-\tfrac12\tau ee^\dagger+\tfrac{\mathrm i}2(D-\tfrac14bee^\dagger),\\
\ell_{i,w}(z,g)&=\frac{a_w}{2}\operatorname{Tr}r_i
 \{Q_w^\dagger X_1(z)Q_w+WQ_w^\dagger Y_1(z)Q_wW\\
 &\hspace{42mm}+WQ_w^\dagger gK_-Q_w
                      +Q_w^\dagger\bar gK_-^\dagger Q_wW\}.
\end{aligned}
\tag{143.2}
$$

Set $\mathcal F_f(z,g)=\max_{1\le i\le9,\ w\in\mathcal W_2}|\ell_{i,w}(z,g)|$,
$m_f=\min_{z,g}\mathcal F_f(z,g)$ and
$n_f=\min_z\mathcal F_f(z,0)$, as in (125.5).
For an integer quadruple $a$ abbreviate
$[a]=a_0+a_1\sqrt2+a_2\sqrt3+a_3\sqrt6$.

**Theorem 143.2 (A seven-row lower certificate; repo-derived).**
On the entire complex tangent domain, $n_f\ge163/4000$.

*Proof.* Choose the following seven literal signed rows, in the given order:

$$
((i_j,w_j,\sigma_j))_{j=1}^7
 =((1,N0,+1),(1,N1,-1),(1,NN,-1),(3,1N,+1),
   (5,NN,+1),(9,0,+1),(9,NN,-1)).
\tag{143.3}
$$

Let $M$ be the $7\times7$ matrix whose first row is all ones and
whose entry in row $r+1$, column $j$ is $\sigma_jU_{i_j,w_j,r}$,
$1\le r\le6$. Put $c_j=\sigma_j\beta_{i_j,w_j}$,
$d_0=\det M$, and $d_j=\det M^{(j)}$, where $M^{(j)}$ replaces
column $j$ by $(1,0,0,0,0,0,0)^{\mathsf T}$.
The following integer quadruples give the exact determinants:
$d_j=[p_j]/(3\cdot2^{69})$.

| $j$ | $p_j$ |
|---|---|
| 0 | $(-31220053431162,-22073591298906,100293003605827,70917713152081)$ |
| 1 | $(-45484145366184,-32162113122336,28572580689496,20203972682396)$ |
| 2 | $(-1558616643432,-1101578522784,21070201204248,14898880792756)$ |
| 3 | $(1422651311326,1005908484762,4148583120107,2933487112869)$ |
| 4 | $(-65894129011488,-46593623215968,60314417694432,42648266573880)$ |
| 5 | $(52680843320784,37252123958808,-18757220296288,-13263213464480)$ |
| 6 | $(39364427549952,27834693731904,-8967243112384,-6340716360072)$ |
| 7 | $(-11751084592120,-8309002613292,13911684306216,9837035814732)$ |

The other required exact identity is

$$
\begin{aligned}
\mathscr H&:=\sum_{j=1}^7d_j(c_j-163/4000)\\
 &=\frac{[123146034328974498,87074386961004549,
             -71087808719360658,-50266456519073999]}
 {56668397794435742564352000}.
\end{aligned}
\tag{143.4}
$$

These identities can be expanded entirely in the four-dimensional
ring basis $(1,\sqrt2,\sqrt3,\sqrt6)$: multiply using
$(\sqrt2)^2=2$, $(\sqrt3)^2=3$ and
$\sqrt2\sqrt3=\sqrt6$, and use
$\det A=\sum_{\pi\in S_7}\operatorname{sgn}(\pi)
\prod_{r=1}^7A_{r,\pi(r)}$. In particular all columns in these
identities are the six columns of (143.2), with their original weights.
Here are rational enclosures, including the small positive remainder
in (143.4):

| Quantity | Strict lower bound times $10^{15}$ | Strict upper bound times $10^{15}$ |
|---|---:|---:|
| $d_0$ | 160929462 | 160929463 |
| $d_1$ | 4523349 | 4523350 |
| $d_2$ | 39456393 | 39456394 |
| $d_3$ | 9721862 | 9721863 |
| $d_4$ | 43563844 | 43563845 |
| $d_5$ | 22805932 | 22805933 |
| $d_6$ | 26916103 | 26916104 |
| $d_7$ | 13941977 | 13941978 |
| $\mathscr H$ | 581 | 582 |

To specify and verify the rational inequalities without decimal
assumptions, put $B_0=10^{40}$ and

$$
\begin{aligned}
b_2&=14142135623730950488016887242096980785696,\\
b_3&=17320508075688772935274463415058723669428,\\
b_6&=24494897427831780981972840747058913919659.
\end{aligned}
\tag{143.5}
$$

For $n=2,3,6$ the integer inequalities
$b_n^2<nB_0^2<(b_n+1)^2$ hold. Thus
$b_n/B_0<\sqrt n<(b_n+1)/B_0$. For any integer quadruple $a$ define

$$
\begin{aligned}
\mathscr L(a)&=a_0B_0+\sum_{n=2,3,6}
 \bigl(a_n^+b_n+a_n^-(b_n+1)\bigr),\\
\mathscr U(a)&=a_0B_0+\sum_{n=2,3,6}
 \bigl(a_n^+(b_n+1)+a_n^-b_n\bigr),
\end{aligned}
\tag{143.6}
$$

where in these sums $a_2,a_3,a_6$ mean the coefficients of
$\sqrt2,\sqrt3,\sqrt6$, respectively, and
$a_n^+=\max(a_n,0)$, $a_n^-=\min(a_n,0)$.
Then $\mathscr L(a)\le B_0[a]\le\mathscr U(a)$.
Substitution of each displayed quadruple and its positive denominator
in (143.6) gives the enclosure table by integer comparisons alone.
Hence $d_j>0$ for every $0\le j\le7$ and $\mathscr H>0$.

Define $\lambda_j=d_j/d_0$. Cramer's rule gives
$M\lambda=(1,0,\ldots,0)^{\mathsf T}$, so
$\lambda_j>0$, $\sum_j\lambda_j=1$ and
$\sum_j\lambda_j\sigma_jU_{i_j,w_j}=0$ in all six real columns.
Furthermore

$$
\sum_j\lambda_jc_j
 =\frac{163}{4000}+\frac{\mathscr H}{d_0}>\frac{163}{4000}.
\tag{143.7}
$$

Apply Proposition 128.1's lower-witness argument to get
$\mathcal F_f(z,0)\ge\sum_j\lambda_jc_j$ for every
$z\in\mathbb C^3$, proving the claim. The classical intermediate is
weak duality for Chebyshev approximation, as in Boyd–Vandenberghe,
[*Convex Optimization*, §6.1.1 and Exercise 5.6, equation (5.104)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf).
The new assertion here is the concrete original-source certificate
(143.3)–(143.7), rather than that general duality. $\square$

**Theorem 143.3 (A rational complex trial for every finite row; repo-derived).**
The unrestricted coefficient satisfies $m_f\le813/20000$.
Together with Theorem 143.2 this gives

$$
\boxed{\qquad \delta_f=n_f-m_f\ge\frac1{10000}>0.\qquad}
\tag{143.8}
$$

*Proof.* In the coordinates of Definition 143.1 take

$$
10^8(\bar x_1,\ldots,\bar x_6,\bar y_1,\bar y_2)
 =(50771868,-2991479,28578480,59147508,
   -8123372,-8052542,4897427,-3873175).
\tag{143.9}
$$

The following exact residual table uses the common denominator
$D_R=629145600000000=3\cdot2^{21}\cdot10^8$:

$$
\ell_{i,w}(\bar z,\bar g)=\frac{[A_{i,w}]}{D_R}.
\tag{143.10}
$$

Each entry below is an integer quadruple $A_{i,w}$; all prefix
masses and all $a_w/2$ occur in the expansion (143.2).

| $i$ | $w$ | $A_{i,w}$ |
|---:|---|---|
| 1 | $\varnothing$ | $(-5677751998464,2855897604096,2157988216832,-818022383616)$ |
| 1 | $0$ | $(-7298773894656,1258290075648,-2936920829952,-3259541929984)$ |
| 1 | $1$ | $(678611532288,3666403891200,604992696320,-1873113890816)$ |
| 1 | $N$ | $(16075727010816,4220700524544,-19152535552,-2744002510848)$ |
| 1 | $00$ | $(-1477289837952,188462529024,-473598027776,793984789504)$ |
| 1 | $01$ | $(-5243839406976,-6949713765888,498882076672,1167777846272)$ |
| 1 | $0N$ | $(7333274204928,-3167026046976,3638553765888,1069877190656)$ |
| 1 | $10$ | $(11630955560064,6071287319040,1737684115456,958003489792)$ |
| 1 | $11$ | $(4416921295488,395164494336,-597004097536,-353438215168)$ |
| 1 | $1N$ | $(337876876032,-4781991438336,9485512988672,5730581045248)$ |
| 1 | $N0$ | $(460276060224,-366751880448,7403515336704,5229070229504)$ |
| 1 | $N1$ | $(-3987551309760,978430151424,-5969400788992,-5156290850816)$ |
| 1 | $NN$ | $(-5835705099264,-3463213547520,-6888418213888,-1187557638144)$ |
| 2 | $\varnothing$ | $(1244862927360,1788336986112,-1216402665472,428909905920)$ |
| 2 | $0$ | $(-6070168957824,-2280114479616,933029799936,1816202870272)$ |
| 2 | $1$ | $(7778219266176,4524558841344,-1064515096576,423886218752)$ |
| 2 | $N$ | $(467686116096,-416593416192,-1896720111616,-626349315072)$ |
| 2 | $00$ | $(2087679972384,2929520552832,220320269824,102489994112)$ |
| 2 | $01$ | $(-1592232503136,-819954496128,1425382774272,735887436160)$ |
| 2 | $0N$ | $(4873379410368,2522512189440,4273893596160,3126580740352)$ |
| 2 | $10$ | $(82855228320,-1105358631552,-1660886129152,-1313836797568)$ |
| 2 | $11$ | $(1472014087968,-871556583552,-375338913280,-505930143872)$ |
| 2 | $1N$ | $(-5418470156352,-3391058525184,-2610562453504,-1253114184448)$ |
| 2 | $N0$ | $(1212435676368,346711220544,-3586088533248,-1816645906496)$ |
| 2 | $N1$ | $(2326500483792,1916639310144,2953288236800,2535813371840)$ |
| 2 | $NN$ | $(4835118772992,1182381379584,2833951164416,1140934118400)$ |
| 3 | $\varnothing$ | $(3603490558464,-17617545216,-654188531712,-811495802880)$ |
| 3 | $0$ | $(9182908715136,5578075928064,788397314048,-43794441728)$ |
| 3 | $1$ | $(-6624228832128,-5315910910464,904850593792,765831807488)$ |
| 3 | $N$ | $(-3603146519808,357065895936,6343739332608,3978193523712)$ |
| 3 | $00$ | $(-2213821536480,-1303771887744,-145712566784,-814630139776)$ |
| 3 | $01$ | $(5618793268128,3186260555136,-1639115851264,-1075947340160)$ |
| 3 | $0N$ | $(-4099485440064,-1119951756288,-2995933179904,-1424415333632)$ |
| 3 | $10$ | $(-2386657773408,-931801678464,855285746176,689955669632)$ |
| 3 | $11$ | $(606688039968,173103524736,539183364608,700948094080)$ |
| 3 | $1N$ | $(8675091096000,7043729958912,3009927267328,703678267136)$ |
| 3 | $N0$ | $(-1878094272816,148690258752,-1265381039872,-811033605056)$ |
| 3 | $N1$ | $(-595821457200,536195091264,2156257287424,-549211052992)$ |
| 3 | $NN$ | $(2985136878336,433583149056,-5410379188224,-4110192430080)$ |
| 4 | $\varnothing$ | $(-3902886179712,-172181521920,431445100544,-102971751936)$ |
| 4 | $0$ | $(947303585568,2806231608192,-321682397696,-108727802752)$ |
| 4 | $1$ | $(-2300680836576,-636923017344,-4467272192,-293896720256)$ |
| 4 | $N$ | $(3559191298752,1448763271680,-2902694324224,-2149199916288)$ |
| 4 | $00$ | $(662227030536,354339450336,-437980001280,-113993282912)$ |
| 4 | $01$ | $(-342454403544,-366852145056,-248424931584,-100835962336)$ |
| 4 | $0N$ | $(-2157520476816,-2538833348352,-39734155520,-483641952832)$ |
| 4 | $10$ | $(616147349352,-669914219424,738293447936,446258709280)$ |
| 4 | $11$ | $(1166941800264,267983940576,225252481536,-64780960864)$ |
| 4 | $1N$ | $(2721555449328,1725764804352,663754761472,1213747957696)$ |
| 4 | $N0$ | $(2570545406388,1445063093328,913582080448,295742419088)$ |
| 4 | $N1$ | $(309540368436,707831388240,-1847256703040,-817727926640)$ |
| 4 | $NN$ | $(1334856852672,-579306124800,1782142029824,719324191488)$ |
| 5 | $\varnothing$ | $(-5975059163520,-6028708406784,130227630080,-108517157376)$ |
| 5 | $0$ | $(775379570592,-1240225477248,-346216149504,-864401021056)$ |
| 5 | $1$ | $(4623260449440,3177037772160,533240445440,214825494400)$ |
| 5 | $N$ | $(3788293505472,2696356339200,-3940120554496,-1901733916416)$ |
| 5 | $00$ | $(570753603624,-412581113760,267780985600,98053557856)$ |
| 5 | $01$ | $(-856671864120,-842218692384,-417601912832,-235235575072)$ |
| 5 | $0N$ | $(2463135171888,1862976851712,638723341056,1399200762944)$ |
| 5 | $10$ | $(-398456947704,484164134112,89339341312,193057052128)$ |
| 5 | $11$ | $(-484780375704,301341603936,-147096723712,303576486752)$ |
| 5 | $1N$ | $(-1032061255248,-1176397896960,-471695355136,-241170951104)$ |
| 5 | $N0$ | $(3164726889924,1719966157584,244928631744,827297087216)$ |
| 5 | $N1$ | $(1404676295748,52383110928,-184477372480,-471716860688)$ |
| 5 | $NN$ | $(3828911623104,3924938337792,4499000118272,3429824473344)$ |
| 6 | $\varnothing$ | $(2556959140896,2226589072512,9394583040,354555386496)$ |
| 6 | $0$ | $(-1474244785656,-545813193888,-276338868736,172139114272)$ |
| 6 | $1$ | $(-997027966008,-108207539616,76855574272,313162820384)$ |
| 6 | $N$ | $(461290788912,-180386881920,1571856648960,586125100992)$ |
| 6 | $00$ | $(1291048826322,706643554680,30199763392,-112462026424)$ |
| 6 | $01$ | $(818194105626,148068986328,163959255488,60677102824)$ |
| 6 | $0N$ | $(1823619605436,938797465344,798778716800,291834652528)$ |
| 6 | $10$ | $(538919373354,212990923224,-43075313600,-75078925144)$ |
| 6 | $11$ | $(-653943171102,-480443355144,-136891679296,-89789299832)$ |
| 6 | $1N$ | $(132829765980,-63148128000,-1092548758016,-1061864957584)$ |
| 6 | $N0$ | $(-1571716211019,-812316085020,-932363981056,-745831168652)$ |
| 6 | $N1$ | $(-297430214187,181753442340,883537046848,541411819508)$ |
| 6 | $NN$ | $(-1064873836368,-1449582405504,-2037568701696,-1275719200320)$ |
| 7 | $\varnothing$ | $(-1199648658144,-1235955510144,1226950862336,973488120960)$ |
| 7 | $0$ | $(1856935407816,1059681462624,319545897216,219893462176)$ |
| 7 | $1$ | $(-323133233784,-175713619872,-789784284160,-581143210336)$ |
| 7 | $N$ | $(2852220113328,2521064751744,-54824548096,-674678112576)$ |
| 7 | $00$ | $(23219126850,105511354680,-12688845248,-66994670488)$ |
| 7 | $01$ | $(567723366858,-13138660584,328196339136,213944769544)$ |
| 7 | $0N$ | $(-1585397914020,-805901153664,652694537472,104381384368)$ |
| 7 | $10$ | $(-105717347814,53950519320,-40654025152,20899674056)$ |
| 7 | $11$ | $(-545539112046,-242507771208,-11217734848,4109161384)$ |
| 7 | $1N$ | $(157825657980,92437583232,1418092772480,212551814576)$ |
| 7 | $N0$ | $(-1550232248931,-185158345500,-786134652000,-779139837116)$ |
| 7 | $N1$ | $(407597169981,725260898724,753741543776,-19756412476)$ |
| 7 | $NN$ | $(-1225748052432,-920732315520,-1558650880768,-384743190336)$ |
| 8 | $\varnothing$ | $(2267139154848,1401325670016,-339968332288,-736207251072)$ |
| 8 | $0$ | $(795748991208,410982785760,427080609024,-18446802464)$ |
| 8 | $1$ | $(-1060103547480,-979190986272,49936200704,-66305879584)$ |
| 8 | $N$ | $(-2200428579984,-1687334911872,1101335290112,1449149083200)$ |
| 8 | $00$ | $(-454322598582,-334503424872,203100881344,133309494200)$ |
| 8 | $01$ | $(892687715442,842233094904,-20491164096,-32440092776)$ |
| 8 | $0N$ | $(400614503244,202749075072,-1676441421312,-566682852848)$ |
| 8 | $10$ | $(-400040872254,-278853607176,-340480184128,-165656689960)$ |
| 8 | $11$ | $(826437973146,358252590360,4911683264,81165810808)$ |
| 8 | $1N$ | $(1153180344684,430707196800,-175500959872,382821273104)$ |
| 8 | $N0$ | $(-238869489567,-739134609036,-123005921952,352893273868)$ |
| 8 | $N1$ | $(1011243826689,-14459012556,17926164512,141976372364)$ |
| 8 | $NN$ | $(437903268336,624213829248,-305049488128,-862882327488)$ |
| 9 | $\varnothing$ | $(8891799945984,-990884066304,7280751755264,2234064715776)$ |
| 9 | $0$ | $(8810895403200,-1085980602624,7516298059776,2155441577984)$ |
| 9 | $1$ | $(2696133458112,-4173613175040,-2256251797504,-2058085302272)$ |
| 9 | $N$ | $(14032299824256,11086684571136,-7851953299456,330156539904)$ |
| 9 | $00$ | $(2841516597168,1821726513600,-1575267813632,-1568885920256)$ |
| 9 | $01$ | $(199821786480,2736114487488,1941976667392,902522432000)$ |
| 9 | $0N$ | $(-5412703059168,-1975650093696,-5747840661504,234855443456)$ |
| 9 | $10$ | $(-1533234922128,420965554368,-1112030313728,485339356672)$ |
| 9 | $11$ | $(-1303139805264,233002951104,-1884701671168,132345993728)$ |
| 9 | $1N$ | $(8119107924768,2216869291392,-3241256237056,240034862080)$ |
| 9 | $N0$ | $(1427441902008,-2979045738528,-7709933368320,-2113644464128)$ |
| 9 | $N1$ | $(9868233543096,-389192292384,259926812672,1133694770176)$ |
| 9 | $NN$ | $(-14994901824384,-3312421212672,-616194088960,-1970523439104)$ |

For each history in the order $\mathcal W_2$, the following integer
$C_w$ bounds all nine absolute residuals after multiplication by $10^8$:

| $w$ | $C_w$ |
|---|---:|
| $\varnothing$ | 4064788 |
| $0$ | 4064788 |
| $1$ | 2125331 |
| $N$ | 2802856 |
| $00$ | 1090893 |
| $01$ | 1803664 |
| $0N$ | 3735524 |
| $10$ | 4064788 |
| $11$ | 622089 |
| $1N$ | 4064788 |
| $N0$ | 4064788 |
| $N1$ | 4064788 |
| $NN$ | 4064788 |

More explicitly, applying (143.6) to each exact quadruple in (143.10)
gives the following integer inequalities, which specify the whole
upper certificate:

$$
-C_wD_RB_0\le10^8\mathscr L(A_{i,w})
 \le10^8\mathscr U(A_{i,w})\le C_wD_RB_0
 \qquad(1\le i\le9,\ w\in\mathcal W_2).
\tag{143.11}
$$

Thus all 117 absolute residuals are at most $4064788/10^8$, and

$$
\mathcal F_f(\bar z,\bar g)
 \le\frac{4064788}{10^8}
 <\frac{4065000}{10^8}=\frac{813}{20000}.
\tag{143.12}
$$

Every number in (143.11) is specified by (143.5), (143.10) and the
$C_w$ table. The comparisons require only integer multiplication
and addition; in particular they neither round a radical nor presume
an optimum. Applying the trial upper bound in Proposition 128.1 and
subtracting $813/20000$ from $163/4000$ proves (143.8). $\square$

## 144. Fully specified decoder and nonlinear comparison constants

**Definition 144.1 (Positive constants from the same finite rows).**
Let $T$ be exactly the $34\times34$ minor in (142.7)–(142.8), and put

$$
\begin{gathered}
\Lambda=\frac{\displaystyle\sum_{j,k=1}^{34}
                         |\operatorname{cof}_{jk}(T)|}{|\det T|},
\qquad p=1+\sqrt3,\qquad B=(8/b+13p)\Lambda,\\
m_0=\frac58-b=\frac{9-4\sqrt2}{24},\qquad
\kappa=\frac{\sqrt2(2+b)B}{m_0},\\
K=\tau+\tfrac12(\sqrt{34}/8+b),\qquad R_*=pK,\\
Z_*=\frac{[1+\tfrac p2(1+b)]B+\kappa R_*}{\tau},\qquad
c=\frac1{2(\kappa+B+Z_*)},\\
C=\tfrac12\max\{2K,2b,1,2\tau\},\qquad
J=1+\frac5{2\tau},\qquad M=\sqrt2 C,\\
R=1+\frac{2JM}{c},\qquad G=\frac M c,\\
E=\tfrac12\left[b(R^2+1)
       +2G\{(\tau+b/2)R+(b/2)R^2\}\right],\\
\eta_0=\min\left\{1,\frac1{4R},\frac1{2G},\frac1{40000E}\right\},
\qquad a_- =\frac1{20000K},\qquad a_+=G.
\end{gathered}
\tag{144.1}
$$

Cofactors here mean their finite determinant sums with entries given
by (142.1), (142.6) and (142.7). Thus (144.1) consists solely of
specified finite arithmetic, absolute values, radicals and finite
maxima or minima; it contains no optimization over hypotheses.

**Theorem 144.2 (Source-only positive constants on the entire paired domain; repo-derived).**
Every quantity in (144.1) is finite and strictly positive. In particular
$\eta_0>0$. The constants $B,\kappa,c,C$ are valid decoder, retention
and comparison constants in VI (118.7), VI (116.8) and VI (118.12),
respectively, with $L_{\mathfrak s}=2$. For every original anchor and
every admissible competing hypothesis, including the whole complex
retention disk and the boundary of the completion ball,

$$
cD_0(\gamma,h;h_0)\le d_f(\gamma,h;h_0)
 \le d_a(\gamma,h;h_0)\le CD_0(\gamma,h;h_0).
\tag{144.2}
$$

*Proof.* The minor certificate gives $\det T\ne0$. At least one
cofactor is nonzero, since an invertible matrix has nonzero inverse.
Hence $\Lambda>0$ and is finite. Also $b,\tau>0$ and
$m_0>0$, since $9>4\sqrt2$. These facts prove positivity of all
successive constants in (144.1), including the finite minimum $\eta_0$.

To check the decoder bound directly, choose the representative of a
lift modulo (142.4) whose $X_{33}$ and $\operatorname{Im}Z_{33}$
coordinates vanish. Its 34 remaining coordinates form a vector $v$;
the first 34 row values form $Tv$. If the maximum absolute original
row value is $d$, Cramer's rule gives $|v_l|\le\Lambda d$ for every
$l$. The bases (142.6)–(142.7) consequently give

$$
\|X\|_{\rm HS}\le4\Lambda d,\quad
\|Y\|_{\rm HS}\le4\Lambda d,\quad
\|Z\|_{\rm HS}\le5\Lambda d.
\tag{144.3}
$$

Indeed the squared Hermitian norm has at most three squared diagonal
coordinates and twelve squared off-diagonal real coordinates; the
squared complex-matrix norm has eighteen squared real coordinates.
The gauge conditions only reduce these bounds. Set
$v_0=(1,2,0)^{\mathsf T}/\sqrt5$ and
$\Pi_{v_0}M=M-(v_0^\dagger Mv_0)I_3$.
Then $v_0\perp a_+,t$ and
$\|\Pi_{v_0}M\|_{\rm HS}\le p\|M\|_{\rm HS}$.
The kernel-invariant maps VI (118.8) are here
$(X+Y)/b$, $\Pi_{v_0}(X-Y)$ and $\Pi_{v_0}Z$.
Their three output norms sum to at most $B d$ by (144.3).
For physical paired lifts they are exactly
$H_\delta,S_\delta,\Pi_{v_0}Z$, so this proves VI (118.7).

For the retention bound use

$$
F=\begin{pmatrix}3/5&-4/5&0\\-4/5&-3/5&0\\0&0&0\end{pmatrix},
\qquad \ell_F(M)=\operatorname{Tr}(FM).
\tag{144.4}
$$

This is VI (116.6) with normalized $a_+$ and the vector $v_0$.
It has trace zero and Hilbert–Schmidt norm $\sqrt2$, annihilates $t$,
and satisfies $\ell_F(D)=5/8$. For the whole completion ball,
$q_h=5/8-b\ell_F(hh^\dagger)\ge m_0$.
The exact identity VI (116.14) and scalar invariance give

$$
q_h|\gamma-\gamma'|
 \le2\sqrt2\|\Pi_{v_0}Z\|_{\rm HS}
             +b\sqrt2\|H_\delta\|_{\rm HS}
 \le\sqrt2(2+b)B d.
\tag{144.5}
$$

Thus $\kappa$ is a valid retention constant for these same finite rows.
Substituting $B,\kappa$ in VI (118.15)–(118.18), using
$s_\theta^2=c_\theta^2=s_\theta c_\theta=1/2$, gives exactly
$R_*,Z_*,c$ in (144.1). The upper estimate VI (118.19)–(118.21)
gives $C$, because $\max_i\|r_i\|_{\rm HS}=1$ and
$\|D\|_{\rm HS}=\sqrt{34}/8$. These estimates apply to any two
points of the full closed parameter domain. Specializing one of them
to $(0,h_0)$ proves (144.2).

Finally (125.6) with $A=1/2$ gives the displayed $E$, and (126.3)
gives exactly $R,G$. The number $\eta_0$ is at most the interval
bound in (126.7) and at most $\Delta/(4E)$ for
$\Delta=1/10000$. These are explicit source constants, not an
unevaluated minimum over the completion or retention domains.
The observability intermediate in VI §118 is D'Alessandro,
[*On Quantum State Observability and Measurement*, §2, Theorem 1](https://arxiv.org/html/quant-ph/0307127v1),
which identifies indistinguishability with annihilation of an
observable linear span. The finite raw-row minor and all constants
above belong to this particular source. $\square$

## 145. A finite nonlinear type III interval for the original hypotheses

**Theorem 145.1 (Every compact minimizer is physically punctured; repo-derived).**
For the source (142.1), for every $0<\eta\le\eta_0$, retain the
anchor $h_0(\eta)=e/2+\eta f$ and exactly the nonlinear reflection-side
minima $\mu_f(\eta),\nu_f(\eta)$ of Definitions 124.1 and 126.2.
These minima are positive and attained, with

$$
\begin{gathered}
\frac{c}{2(1+2/\tau)}\eta
 \le\mu_f(\eta)\le\nu_f(\eta)\le M\eta,\\
\boxed{\quad\nu_f(\eta)-\mu_f(\eta)\ge\frac{\eta}{20000}>0.\quad}
\end{gathered}
\tag{145.1}
$$

Every compact $\mu_f$ minimizer $(\gamma,h)$ obeys

$$
\boxed{\qquad a_-\eta\le|\gamma|\le a_+\eta,\qquad}
\tag{145.2}
$$

with the strictly positive source constants in (144.1). Both extremal
retention radii of Definition 131.1 are attained and satisfy

$$
0<a_-\eta\le r_f^-(\eta)\le r_f^+(\eta)\le a_+\eta.
\tag{145.3}
$$

For the original punctured reflection side there is no alternative
at error $\varepsilon<\mu_f(\eta)$, an alternative exists at
$\varepsilon=\mu_f(\eta)$, and alternatives exist for every
$\varepsilon>\mu_f(\eta)$. Thus its exact endpoint has type III of
Theorem 132.1 throughout this interval. In particular the original
finite anchored modulus satisfies
$\omega_{\mathfrak s,h_0(\eta)}(\mu_f(\eta))\ge1/2$.

*Proof.* Since $R>1$, $\eta_0\le1/(4R)<1/4$, so the anchor is
strictly inside the original ball:
$\|h_0(\eta)\|^2=1/4+\eta^2<1$.
Theorem 126.3 applies with the explicit constants of §144 and gives
positive attained minima, the first line of (145.1), and

$$
|\mu_f(\eta)-\eta m_f|\le E\eta^2,\qquad
|\nu_f(\eta)-\eta n_f|\le E\eta^2.
\tag{145.4}
$$

The strictly positive lower bound follows there from (124.3);
compactness includes the full complex disk and full closed completion
ball on the original half-ball
$\operatorname{Re}(e^\dagger h)\le0$.
By (143.8) and $\eta\le1/(40000E)$,

$$
\nu_f-\mu_f
 \ge\eta\left(\frac1{10000}-2E\eta\right)
 \ge\frac{\eta}{20000}.
\tag{145.5}
$$

For every fixed admissible $h$, the only paired lift in changing
retention from $0$ to $\gamma$ is $(0,0,\gamma K_h)$.
Since $\|K_h\|_{\rm HS}\le K$ on the whole ball and
$\|r_i\|_{\rm HS}\le1$, the original weighted-row triangle inequality
in (127.4) is
$d_f(0,h;h_0)\le d_f(\gamma,h;h_0)+K|\gamma|$.
At every compact minimizer this implies
$K|\gamma|\ge\nu_f-\mu_f\ge\eta/20000$.
The localization (126.9), valid for every minimizer, gives
$|\gamma|\le G\eta$. This proves (145.2); compactness of the
nonempty minimizer fiber then proves (145.3).

All compact minimizers consequently have nonzero retention. The exact
endpoint criterion of Theorem 124.2 proves the assertions at and on
either side of $\mu_f$. Equivalently $r_f^->0$ and
$\nu_f>\mu_f$, which is precisely type III in Theorem 132.1.
Every reflected point has
$\|h-h_0\|\ge|\operatorname{Re}(e^\dagger(h-h_0))|\ge A=1/2$;
using a punctured minimizer in the original modulus proves its stated
lower bound at equality. This deduction uses the actual nonlinear
minima and every compact minimizer; the rational trial in (143.9)
is neither asserted to minimize nor substituted for an actual law.

For completeness, all lifted tangent witnesses used by Theorem 126.3
are admissible on this same interval, since

$$
\|-Ae+\eta z\|\le\tfrac12+\eta R\le\tfrac34,
\quad\operatorname{Re}(e^\dagger(-Ae+\eta z))\le-\tfrac14,
\quad|\eta g|\le\tfrac12
\quad(\|z\|\le R,\ |g|\le G).
\tag{145.6}
$$

VI Theorem 106.3 realizes each actual pair by one full ten-dimensional
completion with its five prescribed ready columns, shared over
emission, the single forward return and all of that hypothesis's
histories. A competing hypothesis may use a different such completion.
The anchor's particular complex direction imposes no restriction on
competitors. All raw prefix masses, both terminal labels, the factors
$a_w/2$, the sole preparation, original menus, clocks and schedules
are retained. No extra preparation, lottery, randomization, repetition,
postselection, record phase, normalized replacement state or selected
outcome enters these conclusions. $\square$

**Proposition 145.2 (The finite certificate's remaining norm boundary).**
Theorems 143.2–145.1 supply the strict gap and physical endpoint for
$d_f$ with its literal 117-row maximum. They supply no strict gap
$\delta_a$, no strict nonlinear inequality $\nu_a>\mu_a$ and no
determined endpoint type for the separate full-history norm $d_a$.

*Proof.* The lower witness (143.3) uses actual histories and therefore
also gives $n_a\ge163/4000$. The upper certificate (143.10)–(143.12)
contains exactly the histories of length at most two. It has no
inequality for another history and gives no bound $m_a\le813/20000$.
The already valid inequalities $m_f\le m_a$ and $n_f\le n_a$ do not
bound $n_a-m_a$ from below by $n_f-m_f$. Likewise (144.2) compares
norms, not their respective nonlinear optimum differences or their
endpoint types. Thus no identification of the two norms is involved.
The unresolved additional requirement is an original all-history
upper certificate paired with an appropriate lower witness, or a
separate exact nonlinear argument for the full-history minima.
The finite nonlinear conclusion is conditional on the original
return premises VI Assumption 106.2. It asserts neither an explicit
nonlinear argmin or exact optimum value nor global originality or
a resolution of an external named open problem. $\square$

## 追加锚（本行以下为增补区）

## 146. An order-three certificate for the original full-history norm

**Definition 146.1 (The reduced all-history family and its signed rows).**
For the source of Definition 142.1, write every original history uniquely
in the form

$$
w=N^{n_0}\epsilon_1N^{n_1}\cdots\epsilon_kN^{n_k},
\qquad \epsilon_j\in\{0,1\},\quad n_j\ge0,
$$

where $k$ is the number of native instrument labels. Since $N^3=I_3$,
replace each $n_j$ by its residue in $\{0,1,2\}$. Let
$\mathscr W_{\le3}$ be the resulting finite family with $0\le k\le3$.
The replacement changes the product $Q_w$ only by a scalar of modulus one,
so it preserves every original row value and its original weight
$a_w/2=2^{-k}/2$.

Use the six real completion coordinates in the ordered basis
$(\xi,\mathrm i\xi,f,\mathrm if,e,\mathrm ie)$ and the two real coordinates
of $g$. In the notation of (125.4), choose the seven actual rows, in order,
with the indicated signs:

$$
\begin{aligned}
(\rho_j,\sigma_j)_{j=1}^7={}&((9,\varnothing),+1),
 ((1,NN),-1), ((1,0),-1), ((9,0),+1),\\
 &((1,NN0N),+1), ((1,N1N),+1), ((2,NN1N),+1).
\end{aligned}
\tag{146.1}
$$

Put $c_j=\sigma_j\beta_{\rho_j}$ and let $M$ have first row all ones and
rows $2$ through $7$ equal to the signed six-coordinate vectors
$\sigma_jU_{\rho_j}$.

**Theorem 146.2 (Exact full-history lower certificate; repo-derived).**
For the full-history tangent norm of (125.5),

$$
n_a>\frac{189}{4096}.
\tag{146.2}
$$

*Proof.* Let $d_0=\det M$, and let $d_j$ replace column $j$ of $M$ by
$(1,0,0,0,0,0,0)^{\mathsf T}$, for $1\le j\le7. Direct expansion in
$\mathbb Q(\sqrt2,\sqrt3)$ gives

$$
\begin{aligned}
d_0={}&\frac{148689184238033\sqrt2+210278927993446
+169606516283115\sqrt6+239860620630880\sqrt3}
{4722366482869645213696},\\
d_1={}&\frac{-704179540270-497912696323\sqrt2+5522995798882\sqrt3
+3905391073879\sqrt6}{1180591620717411303424},\\
d_2={}&\frac{4431862778894+3134204531693\sqrt2+23397372993571\sqrt6
+33088950632464\sqrt3}{4722366482869645213696},\\
d_3={}&\frac{6657713390264\sqrt2+9415871119692+7081008641242\sqrt3
+5007043628175\sqrt6}{1180591620717411303424},\\
d_4={}&\frac{-3205241353621\sqrt6-4532858035242\sqrt3+8819173387014
+6236145086803\sqrt2}{295147905179352825856},\\
d_5={}&\frac{-5035357134791\sqrt2-7120923894510+6089708029451\sqrt6
+8612159649921\sqrt3}{295147905179352825856},\\
d_6={}&\frac{773296199455\sqrt3+546834469621\sqrt6+2887987934358
+2042152182645\sqrt2}{295147905179352825856},\\
d_7={}&\frac{762660156774+539286990438\sqrt2+434832704329\sqrt6
+614953806342\sqrt3}{36893488147419103232}.
\end{aligned}
\tag{146.3}
$$

The rational radical bounds (143.5)–(143.6), applied by integer
multiplication, give the following strict intervals after multiplication
by $10^{15}$:

$$
\begin{array}{c|rrrrrrrr}
&d_0&d_1&d_2&d_3&d_4&d_5&d_6&d_7\\ \hline
10^{15}d_j\text{ lies in}&
(265006410,265006411)&(15012803,15012804)&
(26149530,26149531)&(36727914,36727915)&
(6559653,6559654)&(52825654,52825655)&
(28646251,28646252)&(99084602,99084603)
\end{array}
$$

Thus all eight determinants are positive. Cramer's rule gives
$\lambda_j=d_j/d_0>0$, $\sum_j\lambda_j=1$, and
$\sum_j\lambda_j\sigma_jU_{\rho_j}=0$. The same exact expansion gives

$$
\sum_{j=1}^7d_j\left(c_j-\frac{189}{4096}\right)
=\frac{-20327335451999776\sqrt3-14373489159543967\sqrt6
+35385978341760498+25021737772452819\sqrt2}
{19342813113834066795298816}>0.
\tag{146.4}
$$

The last positivity is certified by (143.5)–(143.6); its value times
$10^{15}$ lies strictly in $(18423,18424)$. Hence
$\sum_j\lambda_jc_j>189/4096$. The signed cancellation identity and
Proposition 128.1 give $\mathcal F_a(z,0)\ge\sum_j\lambda_jc_j$ for every
complex $z$. Taking the infimum proves (146.2). Every row in (146.1) is an
actual original history, with its original prefix mass and native-label
weight.

**Theorem 146.3 (All-history upper certificate and strict source gap).**
Define

$$
\begin{aligned}
z_*={1\over10^8}\big(&(-20328269+36581420\mathrm i)\xi
 +(95916322-29623864\mathrm i)f\\
 &+(-1841089-2547800\mathrm i)e\big),\\
g_*={-3298492+5963260\mathrm i\over10^8}.
\end{aligned}
\tag{146.5}
$$

For every $i$ and every $w\in\mathscr W_{\le3}$, direct expansion of
(143.2) at $(z_*,g_*)$, with the radical enclosure (143.5), gives

$$
\begin{array}{c|c|c}
k(w)&\#\{w\in\mathscr W_{\le3}:k(w)=k\}&
\displaystyle\max_{i,\,k(w)=k}|\ell_{i,w}(z_*,g_*)|\\ \hline
0&3&<4485/100000\\
1&18&<4485/100000\\
2&108&<97/2500\\
3&648&<233/10000
\end{array}
\tag{146.6}
$$

The inequalities in (146.6) are finite integer comparisons after replacing
$\sqrt2,\sqrt3,\sqrt6$ by the lower and upper rational bounds in (143.5);
they include all nine prefixes and both terminal labels through the sign
identity following (125.4). Moreover, for the same exact matrices,

$$
T_*:=\frac12\left(\|X_1(z_*)\|_{\rm HS}+\|Y_1(z_*)\|_{\rm HS}
+2|g_*|\|K_-\|_{\rm HS}\right)<\frac38.
\tag{146.7}
$$

For a history with $k\ge4$, trace Cauchy–Schwarz in the original row
(116.2), $\max_i\|r_i\|_{\rm HS}=1$, and (146.7) give
$|\ell_{i,w}(z_*,g_*)|\le2^{-k}T_*<3/128<23/512$.
For $k\le3$, (146.6) and $4485/100000<23/512$ give the same bound.
Reduction modulo $N^3=I_3$ therefore covers every finite actual history, and

$$
m_a\le\mathcal F_a(z_*,g_*)<\frac{23}{512}.
\tag{146.8}
$$

Combining (146.2) and (146.8) yields the source-specific full-history
certificate

$$
\boxed{\quad\delta_a=n_a-m_a>\frac{189}{4096}-\frac{23}{512}
=\frac5{4096}>\frac3{4096}.\quad}
\tag{146.9}
$$

This is an all-history upper bound, not a finite-decoder substitution:
the tail estimate uses the original weighted rows, and the finite part
contains every reduced history with at most three native labels.

**Theorem 146.4 (Original nonlinear full-law endpoint on a positive interval).**
Set

$$
\Delta_a=\frac3{4096},\qquad
\eta_a=\min\left\{\eta_0,\frac{3}{16384E}\right\},
\tag{146.10}
$$

where $E,\eta_0$ are the explicit source constants of (144.1). Then
$\eta_a>0$, and for every $0<\eta\le\eta_a$ the original full-history
thresholds of Definition 126.2 satisfy

$$
\boxed{\qquad \nu_a(\eta)-\mu_a(\eta)
\ge\frac{3}{8192}\eta>0.\qquad}
\tag{146.11}
$$

All compact minimizers of the unchanged original $\mu_a(\eta)$ have

$$
\frac{3}{8192L}\eta\le|\gamma|
\le\frac{M-9/16384}{\underline c}\eta\le G\eta,
\tag{146.12}
$$

and both extremal retention radii of Definition 131.1 are attained and
obey the same positive lower and upper bounds. Thus the original
full-history endpoint is type III throughout this interval.

*Proof.* The gap (146.9) permits the weaker certified value
$\delta_a\ge\Delta_a$. Apply Theorem 127.1 with this $\Delta_a$.
Its interval is exactly (146.10), its threshold gap is
$\Delta_a\eta/2=3\eta/8192$, and its retention bounds are (146.12).
The attainment and type-III statements are the endpoint criterion of
Theorem 124.2 together with Definition 131.1. The construction retains
one full ten-dimensional completion per hypothesis, shared across
emission, the single forward return and every history; compared
hypotheses may use different completions. All original prefix masses,
the factors $a_w/2$, both terminal labels, clocks, schedules, sole
preparation and installed menu remain unchanged. No normalized rows,
extra preparation, randomization, postselection, record-phase gauge or
new control is introduced.

The certificate is source-specific and repo-derived. It does not give an
exact optimizer or exact optimum value, and it makes no claim of global
novelty or of resolving an external named problem. Its only literature
intermediates are the finite-source decoder and comparison results already
cited in §§106, 116, 118 and the Chebyshev signed-witness principle cited
in §128. The remaining dependence is the original return premise VI
Assumption 106.2. $\square$

## 追加锚（本行以下为增补区）
