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
