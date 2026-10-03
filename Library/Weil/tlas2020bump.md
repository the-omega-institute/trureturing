---
bibkey: tlas2020bump
authors: T. Tlas
year: 2020
title: Bump Functions With Monotone Fourier Transforms Satisfying Decay Bounds
doi: null
url: https://arxiv.org/abs/2003.12364v2
claim: The initial saddle lemma matches the prescribed bump; retaining its complex coefficient before taking real parts supplies an absolute-envelope asymptotic with a fixed phase, rather than a relative estimate through Fourier zeros.
strata_touched: []
license: citation-only
triage: anchor
---

# The original bump and its real-frequency supplier

The source is [arXiv:2003.12364v2](https://arxiv.org/pdf/2003.12364v2), initial lemma and proof on PDF pp.2–3. The original PDF and TeX were inspected. The displayed real cosine formula suppresses a constant phase; the complex saddle expression immediately before taking real parts retains the needed coefficient. The statements and applications here are paper-level, without a Lean implementation.

## Match the function and Fourier convention

Keep exactly the original test of [the research volume, §§19.3 and 30](../../docs/develop/theory/RH_RESEARCH_LANE_THEORY.md):

$$
\phi(x)=e^{-1/(1-4x^2)}\mathbf1_{\{|x|<1/2\}},
\qquad \Phi(t)=\int_{\mathbb R}\phi(x)e^{-itx}\,dx.
$$

Tlas's initial lemma concerns

$$
\phi_{A,B}(v)=
e^{-B/(1-v)^A}e^{-B/(1+v)^A}\mathbf1_{\{|v|<1\}},
\qquad
\widehat{\phi_{A,B}}(k)=\int\phi_{A,B}(v)e^{-2\pi ikv}\,dv.
$$

At $A=1$, $B=1/2$ there is an exact identity, including the support:

$$
\phi_{1,1/2}(2x)=\phi(x),
\qquad
\Phi(t)=\tfrac12\widehat{\phi_{1,1/2}}\!\left(\frac{t}{4\pi}\right).
\tag{1}
$$

Thus the source variable $\widetilde k=2\pi k$ is $t/2$, and its two exponential coefficients are $\alpha=\beta=1$. This uses the initial lemma, rather than the final theorem's different function with a monotone Fourier transform.

## Retain the saddle coefficient before taking real parts

On p.3 the contour integral is written as twice the real part of a single complex integral. For these parameters the latter has the form, for a fixed $C\ne0$,

$$
C\widetilde k^{-3/4}
\exp\!\left(-i\widetilde k+(-1+i)\sqrt{\widetilde k}\right)
+o\!\left(\widetilde k^{-3/4}e^{-\sqrt{\widetilde k}}\right).
$$

The prefactor $\widetilde k^{-1/2}$ outside the source's saddle integral combines with its $\widetilde k^{-1/4}$ saddle prefactor. Consequently (1) gives constants $a>0$, $\eta\in\mathbb R$ and a real remainder $\varepsilon(t)\to0$ such that

$$
\Phi(t)=a\,t^{-3/4}e^{-\sqrt{t/2}}
\left[\cos\!\left(t/2-\sqrt{t/2}+\eta\right)+\varepsilon(t)\right],
\qquad t\to+\infty.
\tag{2}
$$

The error in (2) is in units of the positive envelope $t^{-3/4}e^{-\sqrt{t/2}}$. No division by the cosine is made. The fixed phase is retained, and no numerical threshold or explicit bound for $\varepsilon$ is supplied by this application.

[Johnson, arXiv:1508.04376v1, §2](https://arxiv.org/pdf/1508.04376v1) analyzes the same bump, with $\Phi(t)=F(t/2)/2$, and displays the complex coefficient explicitly. It is a technical note using approximate expressions and numerical comparisons; those comparisons alone do not establish a uniform error at cosine zeros. The input used here is Tlas's complex saddle asymptotic in the proof, not an extrapolation of Johnson's finite numerical check. Saddle analysis and the original bump's decay belong to these sources, rather than to a new project criterion.

## Apply the supplier to the unchanged dilation average

Retain the volume's original nonnegative normalized weight $w$, supported on $[1,b]$, where $b=2+\sqrt5$, and its fixed verified height $H=3000175332800$. Its head is

$$
P_H(R)=2\sum_{0<\gamma\le H}m_\rho p(\gamma)
\int_1^b w(u)\Phi(uR\gamma)^2\,du,
\qquad p(z)=z^2(1+4z^2)^2.
$$

The fixed verified zeros in this head lie on the critical line. Reuse the actual critical zero $\gamma_0\in[14,15]$ and the volume's already established bound $w\ge w_0>0$ on $I=[5/4,5/2]$. These are fixed published inputs; no verified height is enlarged.

Put $r=R\gamma_0$ and $\Theta_r(u)=ur/2-\sqrt{ur/2}+\eta$. On $I$,

$$
\Theta_r'(u)=\frac r2-\frac{\sqrt r}{2\sqrt{2u}},
\qquad
\int_I\cos^2\Theta_r(u)\,du=\frac{|I|}{2}+O(r^{-1}).
$$

The latter is ordinary integration by parts in the oscillatory cosine term: $\Theta_r'$ is bounded below by a positive multiple of $r$, and $\Theta_r''=O(\sqrt r)$ on this fixed interval. Equation (2) also gives $\sup_{u\in I}|\varepsilon(ur)|\to0$, so the integral of the squared bracket in (2) is at least $|I|/8$ for all sufficiently large real $R$. No pointwise positive lower bound for $\Phi$ is asserted.

Throughout the core, $uR\gamma_0\le(75/2)R$. Its squared positive envelope therefore satisfies

$$
(uR\gamma_0)^{-3/2}e^{-\sqrt{2uR\gamma_0}}
\ge (75/2)^{-3/2}R^{-3/2}e^{-\sqrt{75R}}.
$$

Keeping just this actual nonnegative head term proves the paper-level application

$$
P_H(R)\ge cR^{-3/2}e^{-\sqrt{75R}}
\ge cR^{-3/2}e^{-10\sqrt R}
\qquad(R\ge R_0),
\tag{3}
$$

for some $c>0$ and finite $R_0$. Neither constant is numerically certified here. This applies the existing saddle supplier and a standard positive average; it is not a new saddle theorem, zero computation or RH criterion.

## Connect the average to the existing sign detector

The average retains the detection mechanism of [the volume, §§28–29](../../docs/develop/theory/RH_RESEARCH_LANE_THEORY.md), without recovering each pointwise $q(uR)$ from its average. This is a paper-level application of that existing argument, not a result attributed to Tlas. With exactly the kernel of §30,

$$
J(v)=\int_1^b\frac{w(u)}uK(v/u)\,du,
\qquad K=\phi*\phi,
\qquad
\widehat J(z)=\int_1^bw(u)\Phi(uz)^2\,du,
$$

the complete scalar is

$$
\bar q(R)=2\sum_{\gamma>0}m_\rho p(z_\rho)\widehat J(Rz_\rho).
$$

Here $J$ is real, even and smooth, has exact support $[-b,b]$, and is positive on $(-b,b)$; these properties are already supplied by §30. The factor $1/u$ belongs in $J$, and introduces no further factor in $\widehat J$. In terms of the unnormalized form, $R^3\bar q(R)=\int_1^bw(u)u^{-3}\mathcal W(uR)\,du$.

Apply the existing detector with $K$ replaced by $J$. The initial Laplace half-plane becomes $\Re s>b/2$. Its single-zero representations are

$$
I_z^J(s)=\frac1z\int_0^\infty
 e^{-s(1+t/z)}\widehat J(z+t)\,dt,
\qquad
F_z^J(s)=\int_{-b}^bJ(v)\frac{e^{-(s+izv)}}{s+izv}\,dv.
$$

They agree in $\Re(s/z)>0$, first by the same Fubini calculation for real $s>b/2$ and then by analytic continuation. Arbitrary polynomial Fourier decay on a fixed horizontal strip remains uniform after integrating over $1\le u\le b$, and pays the unchanged degree-six factor $p$ and actual zero multiplicities. The horizontal-ray cone is still $\Re s>|\Im s|/(2\gamma_*)$, where $\gamma_*=\inf_{\gamma>0}\gamma>0$.

Writing $\lambda_\rho=iz_\rho=\rho-1/2$, the cuts are now $[-b\lambda_\rho,b\lambda_\rho]$. On a compact set $\Re s\ge\delta>0$, $|\Im s|\le T$, membership $s=t\lambda_\rho$ implies $|t|\ge2\delta$ and $\gamma\le T/(2\delta)$. The cuts are therefore locally finite; the finite-low-term and convergent-horizontal-tail patching remains valid. Their complement in the positive half-plane is connected by outward radial escape to $\Re s>b/2$.

If an off-line zero exists, choose the outermost zero on one ray, as in §29. Its exposed endpoint is $b\lambda_0$. The Cauchy jump at $s=\lambda_0t$, for $t<b$ sufficiently near $b$, is

$$
\pm\frac{2\pi i}{\lambda_0}J(t)
$$

multiplied by the unchanged nonzero coefficient $2m_{\rho_0}p(z_{\rho_0})$. Positivity of $J(t)$ makes this jump nonzero despite its flat endpoint. Eventual nonnegativity of $\bar q$ would, by the already-used Landau–Widder argument, make its actual Laplace transform holomorphic throughout $\Re s>0$, contradicting that jump. Conversely RH makes every real-frequency square in $\widehat J(R\gamma)$ nonnegative. Thus the existing proof supplies the application

$$
\mathrm{RH}\quad\Longleftrightarrow\quad
\exists R_0\ge1\ \forall R\in\mathbb R,
\quad R\ge R_0\Longrightarrow\bar q(R)\ge0.
$$

This requires all sufficiently large real scales. It does not follow from one average, a bounded scale interval or sampled scales. No factorization of $\widehat J$ as the Fourier square of another compact test is needed. The application validates the signed target; it does not supply its missing sign estimate.

## What the strengthened reserve pays

For actual zeros $\rho=\beta+i\gamma$, put $z_\rho=\gamma-i(\beta-1/2)$ and keep the analytic square. Consider precisely the infinite subset

$$
\mathcal C_H(R)=
\{\rho:\gamma>H,\ |\beta-1/2|\le R^{-1/2}\},
\qquad
E_{\mathrm{near}}(R)=
2\sum_{\rho\in\mathcal C_H(R)}m_\rho p(z_\rho)
\int_1^b w(u)\Phi(uRz_\rho)^2\,du.
$$

The subset retains reflected positive-ordinate pairs and their actual multiplicities. Its dependence on $R$ does not change the pointwise-in-$R$ use of the existing common zero-count bound. Reuse the volume's complete-tail proof in §31.2: it needs only the actual critical strip, $N_+(t)\le t\log t$, and the complex Fourier estimate. Its use of $|\beta-1/2|<1/2$ in the polynomial majorant remains valid. The refined restriction gives, in the Fourier factor alone,

$$
|\Phi(uRz_\rho)|^2
\le16e^{b\sqrt R-\sqrt{R\gamma}/3}.
$$

The same nonnegative summable majorant, with cutoff $H$ and $\sqrt{RH}/3\ge28$, consequently gives

$$
|E_{\mathrm{near}}(R)|
\le6000H^7\log H\,
e^{b\sqrt R-\sqrt{RH}/3},
\qquad R\ge1.
\tag{4}
$$

The absolute square appears only in this legitimate upper majorant; the original expression defining $E_{\mathrm{near}}$ retains its analytic square. All zeros at height $H$ remain in the inclusive head. The existing tail proof, not a new criticality assumption above $H$, supplies the count and summation in (4).

Combining (3)–(4) yields

$$
\frac{|E_{\mathrm{near}}(R)|}{P_H(R)}
\le\frac{6000H^7\log H}{c}\,R^{3/2}
\exp\!\left[-\left(\frac{\sqrt H}{3}-b-10\right)\sqrt R\right]
\longrightarrow0.
\tag{5}
$$

In particular this subset can use less than half the fixed head for all sufficiently large real $R$, without a numerical threshold claim. This is a restricted application of existing bounds. The complementary actual zeros with $\gamma>H$ and $|\beta-1/2|>R^{-1/2}$ still have an uncontrolled signed contribution. Every hypothetical fixed nonzero horizontal displacement eventually belongs to that complement. Thus (5) neither excludes off-line zeros nor establishes positivity of the complete average, RH, Robin, or the FIB-to-prime intertwining.

## Keep height and transverse displacement together

The same majorant permits a larger parameter region when its scale factor $u$ is retained in both growth and decay. All sums continue to range over distinct positive-ordinate zeros with actual analytic multiplicities; the outer factor two accounts for the negative-ordinate symmetry. Put

$$
\epsilon_H=\frac{11}{\sqrt H},\qquad
a_H=\frac{1/3-\epsilon_H}{\sqrt b}>0,
\qquad \delta_\rho=\beta-\tfrac12,
$$

and, for each real $R\ge7$, define

$$
\mathcal S_H(R)=
\{\rho:\gamma>H,\ |\delta_\rho|\le a_H\sqrt{\gamma/R}\},
\qquad
E_{\mathrm{safe}}(R)=
2\sum_{\rho\in\mathcal S_H(R)}m_\rho p(z_\rho)
\int_1^bw(u)\Phi(uRz_\rho)^2\,du.
$$

Membership is fixed during the $u$ integral. The actual strip still supplies $|\delta_\rho|<1/2$ for the polynomial bound, even where the new cap exceeds $1/2$. For $\rho\in\mathcal S_H(R)$ and $1\le u\le b$, the existing complex Fourier estimate gives

$$
\begin{aligned}
|\Phi(uRz_\rho)|^2
&\le16\exp\!\left(uR|\delta_\rho|-\frac{\sqrt{uR\gamma}}3\right)\\
&\le16\exp\!\left(\sqrt{R\gamma}\left[a_Hu-\frac{\sqrt u}3\right]\right)
\le16e^{-\epsilon_H\sqrt{R\gamma}}.
\end{aligned}
$$

Here $a_Hu\le(1/3-\epsilon_H)\sqrt u$ and $u\ge1$. Apply the same nonnegative full-count/Stieltjes calculation of §31.2 with $\alpha=\epsilon_H\sqrt R$ and $X=\alpha\sqrt H=11\sqrt R\ge28$. Its count factor remains $4H^7\log H\,e^{-X}$, so $2\cdot45\cdot16\cdot4\le6000$ gives

$$
|E_{\mathrm{safe}}(R)|\le6000H^7\log H\,e^{-11\sqrt R},
\qquad R\ge7.
\tag{6}
$$

Combining with (3), in its eventual real-scale range,

$$
\frac{|E_{\mathrm{safe}}(R)|}{P_H(R)}
\le\frac{6000H^7\log H}{c}\,R^{3/2}e^{-\sqrt R}
\longrightarrow0.
\tag{7}
$$

This reuses the existing Fourier and counting bounds; no stronger complex saddle estimate is assumed. The admissible region includes the earlier cap because $a_H\sqrt H>1$, hence $\mathcal C_H(R)\subseteq\mathcal S_H(R)$. This inclusion does not assert that the two actual zero subsets differ. The broader cap trades the sharper bound in (4) for a bound that still decays faster than the fixed-head floor.

The complementary signed sum has a stricter joint height condition. Define

$$
\kappa_H=\frac1{4a_H^2}
=\frac{b}{4(1/3-11/\sqrt H)^2}<10.
$$

For the last inequality, $H>3300^2$ gives $\epsilon_H<1/300$, while $b<17/4$; thus $\kappa_H<10625/1089<10$. Every complementary term satisfies strictly

$$
H<\gamma<\frac{R\delta_\rho^2}{a_H^2}<\kappa_HR<10R.
\tag{8}
$$

Consequently its independently specified expression is the finite sum

$$
E_{\mathrm{rem}}(R)=
2\sum_{\substack{H<\gamma<\kappa_HR\\
|\delta_\rho|>a_H\sqrt{\gamma/R}}}
m_\rho p(z_\rho)\int_1^bw(u)\Phi(uRz_\rho)^2\,du,
\qquad
\bar q(R)=P_H(R)+E_{\mathrm{safe}}(R)+E_{\mathrm{rem}}(R).
\tag{9}
$$

Both subsets retain reflected pairs, actual multiplicities and analytic squares; the common positive majorant gives absolute convergence. Equality in the transverse cap belongs to $\mathcal S_H(R)$, and height $H$ remains in the head. The remaining height restriction improves the earlier $250000R$ cutoff without changing the fixed verified height. The height cutoff is finite for each $R$ and grows linearly with $R$; no fixed height cutoff for the remainder is established.

The outstanding estimate is still a signed comparison for this same $E_{\mathrm{rem}}$. Any hypothetical fixed off-line zero eventually leaves $\mathcal S_H(R)$, so (6)–(9) do not exclude one. They control a larger parameter region and specify the residual more tightly; they do not establish complete eventual nonnegativity or RH/Robin. The golden value of $b$ fixes the existing dilation band and supplies no additional FIB-to-prime transport.

## Identify the complex transform with an existing function family

The integral definition of the extended confluent hypergeometric function in [Mondal, arXiv:1611.08423v1, equation (1.3), PDF p.1](https://arxiv.org/pdf/1611.08423v1) gives a direct source coordinate for the unchanged bump. Write that family as

$$
\mathcal F_\sigma(B;C;\zeta)=
\frac1{\mathrm B(B,C-B)}
\int_0^1v^{B-1}(1-v)^{C-B-1}
\exp\!\left(\zeta v-\frac\sigma{v(1-v)}\right)\,dv,
\qquad \Re C>\Re B>0,\quad \sigma>0.
$$

Here $\mathrm B$ is the classical beta function. Substituting $x=v-1/2$ gives $1-4x^2=4v(1-v)$ and $\mathrm B(1,1)=1$, hence, for every complex $s$,

$$
\Phi(s)=e^{is/2}\mathcal F_{1/4}(1;2;-is),
\qquad
M=\mathcal F_{1/4}(1;2;0).
\tag{10}
$$

The finite integral is entire in its last parameter; the fixed endpoint damping is $1/4$. The original defining paper cited by Mondal is Chaudhry–Qadir–Srivastava–Paris, *Extended hypergeometric and confluent hypergeometric functions*, Applied Mathematics and Computation 159 (2004), 589–602. The defining integral used here was inspected in Mondal; no complex asymptotic is attributed to the uninspected full text of the 2004 paper.

The same substitution also retains the outer bump. Put $d=b-1$ and $u=1+dv$. The original normalized weight satisfies

$$
w(1+dv)d\,dv=
\frac1M e^{-1/[4v(1-v)]}\,dv.
$$

Thus the exact analytic average, including both endpoint phases, is

$$
A_R(z)=\frac1M\int_0^1
e^{-1/[4v(1-v)]}e^{i(1+dv)Rz}
\mathcal F_{1/4}(1;2;-i(1+dv)Rz)^2\,dv.
\tag{11}
$$

Equations (10)–(11) identify published terminology and parameters; they supply no sign estimate. In particular, Mondal's Theorem 2.5, PDF pp.6–7, gives real-argument monotonicity and log-convexity statements. They do not establish a lower bound for the real part of (11) at the complex arguments of the residual.

## Reuse the Bessel expansion through its exact integral

[Paris, *The asymptotic expansion of Krätzel's integral and an integral related to an extension of the Whittaker function*, arXiv:2112.02928v1, §6, PDF pp.9–11](https://arxiv.org/pdf/2112.02928v1), supplies a closer special-function interface. Its equation (6.1) is, writing the second endpoint exponent as $c$ and the damping parameter as $h$ to distinguish them from this note's dilation bound and polynomial,

$$
I_{\nu,h}(a,c;\zeta)=\sqrt{\frac{2h}{\pi}}
\int_0^1v^{a-1/2}(1-v)^{c-1/2}e^{\zeta v}
K_\nu\!\left(\frac{h}{v(1-v)}\right)\,dv,
\qquad \nu\ge-1/2,\quad h>0.
$$

Here $K_\nu$ is the modified Bessel function. The exact half-integer identity [DLMF 10.39.2](https://dlmf.nist.gov/10.39.E2) is

$$
K_{1/2}(y)=\sqrt{\frac{\pi}{2y}}e^{-y},\qquad y>0.
$$

It cancels the integral's prefactor and half powers, giving the unchanged family exactly:

$$
\mathcal F_{1/4}(1;2;\zeta)=I_{1/2,1/4}(0,0;\zeta),
\qquad \Phi(s)=e^{is/2}I_{1/2,1/4}(0,0;-is).
$$

This uses (6.1), rather than the displayed definition of $J$ immediately before (6.8). The latter literally has $\exp(+h/[v(1-v)])$ with $h>0$ in both the inspected PDF and original TeX. At the target endpoint exponents its ordinary improper integral diverges. Changing that sign silently would give a different definition; the half-integer specialization of $I$ avoids relying on it.

In the coefficients preceding (6.6), $a_0(1/2)=1$ and $a_k(1/2)=0$ for $k\ge1$. Thus (6.6) specializes to

$$
I_{1/2,1/4}(0,0;-x)
\sim e^{-1/4}x^{-1/2}
\sum_{r=0}^\infty
\frac{(-1)^r c_r(0)}{r!\,2^r x^{r/2}}
K_{1+r}(\sqrt x),
\qquad |x|\to\infty,\quad |\arg x|<\pi/2,
$$

with principal roots and the coefficients defined by

$$
e^{-1/[4(1-v)]}
=e^{-1/4}\sum_{r=0}^\infty\frac{(-1)^r c_r(0)}{r!}v^r,
\qquad |v|<1.
$$

This is an existing one-endpoint asymptotic expansion, not an exact convergent representation or a new saddle construction. The source records a local $O(e^{-x})$ error when extending an intermediate upper limit, but gives no constant uniform as the argument approaches the sector boundary and no remainder transported through (11). Its Kummer relation (6.2) supplies the opposite-sector representation; it does not alone justify adding both endpoint expansions with one controlled remainder near the Fourier direction. The actual signed aggregate estimate remains unprovided by this interface.

## Preserve the source hypotheses at the complex interface

Inspected asymptotic sources provide complementary tools for a possible remainder estimate:

| Source and exact location | Conditions needed by an application to (11) |
| --- | --- |
| [Nemes, *An extension of Laplace's method*, arXiv:1802.03962v2](https://arxiv.org/pdf/1802.03962v2), Conditions 1.1 and Theorem 1.1, PDF p.3; remainders (29)–(30), p.8 | Parameter-independent analytic data and path, convergent endpoint power expansions with the source's $\mu>\nu\ge0$ and $\Re\lambda>0$, uniform convergence, and a uniform positive phase gap away from the initial endpoint on a fixed closed sector of width less than $\pi$. The source also requires its tail-growth condition $r(t)=O(|p(t)-p(a)|)$. The original essential endpoint singularities and a transformed parameter-dependent amplitude require an additional application proof. |
| [Bennett–Howls–Nemes–Olde Daalhuis, *Globally exact asymptotics for integrals with arbitrary order saddles*, arXiv:1710.10073v2](https://arxiv.org/pdf/1710.10073v2), assumptions and sector (7), PDF pp.4–6; exact remainder (9), (12), pp.6–7; bound (42), p.18 | Admissible convergent steepest-descent contours, a finite nonempty adjacent-saddle set, and the corresponding contour deformation. The bound retains angular factors and adjacent-contour integrals; uniform constants for this moving nested integral must be justified. |
| [Temme, *Uniform asymptotic expansions of a class of integrals in terms of modified Bessel functions, with application to confluent hypergeometric functions*, SIAM J. Math. Anal. 21 (1990), 241–261, DOI 10.1137/0521013, original paper at CWI](https://ir.cwi.nl/pub/2392/2392D.pdf), (1.1), p.241; (2.5)–(2.13), pp.243–244; Theorem 3.2 with (3.12)–(3.13), pp.246–247 | Large positive-real $z$ in the half-line model $\int_0^\infty t^{\lambda-1}e^{-zt-a/t}f(t)\,dt$, with nonnegative real uniformity parameters. The two Bessel blocks of §2 use the saddles $\pm\sqrt{a/z}$ of this model, not the two endpoints of (11). The exact integral remainder requires bounds on the recursively constructed amplitude over the whole positive half-line. Theorem 3.2 also imposes an analytic-domain radius condition and a uniform polynomial growth condition. Its positive-real large-variable theorem does not provide moving near-Fourier uniformity. |

For the original inner integral, the local $v=0$ match to Temme's phase is $\lambda=1$, $a=1/4$, $z=x=is$, with amplitude $f(v)=e^{-1/[4(1-v)]}$. This amplitude has an essential singularity at the other endpoint $v=1$ and does not supply the required whole-half-line amplitude. An endpoint split would need its own cutoff or contour and remainder argument. The exact local phase match therefore does not establish the theorem's application, and its two Bessel blocks cannot be identified with a simultaneous two-endpoint estimate for the original finite interval.

None of these inspected statements directly supplies a uniform remainder for (11) or a signed estimate for the actual multiplicity-weighted residual. A local saddle and Gaussian coefficient alone do not discharge contour deformation, connecting faces, parameter-dependent amplitude bounds, or the full rescaled tails.

For a residual representative with positive displacement, write $s=T-i\alpha$, $T=R\gamma$ and $\alpha=R\delta_\rho$. Equations (8)–(9) give the strict domain

$$
HR<T<\kappa_HR^2,
\qquad a_H\sqrt T<\alpha<R/2.
\tag{12}
$$

When $\alpha/\sqrt T$ stays bounded and $T\to\infty$, $\arg(is)\to\pi/2$. Uniformity only on $|\arg(is)|\le\pi/2-\epsilon$ for a fixed $\epsilon>0$ does not cover this part of (12). A two-endpoint expansion also needs an additive remainder that remains meaningful when the endpoint terms cancel. Subsequently integrating the modulus of an inner remainder can lose the exponentially small cancellation of the outer integral; its analytic transport or a direct outer-integral remainder remains a separate obligation.

The required consumer is still the actual signed sum in (9). With

$$
B_H(R)=6000H^7\log H\,e^{-11\sqrt R},
$$

a sufficient comparison is

$$
E_{\mathrm{rem}}(R)\ge-P_H(R)+B_H(R)
$$

for all sufficiently large real $R$. A relative version $E_{\mathrm{rem}}\ge-(1-\varepsilon(R))P_H$ pays the known safe-error bound when $\varepsilon(R)P_H(R)\ge B_H(R)$; an unspecified $o(1)$ reserve does not ensure this. This is a sufficient use of the absolute-error certificate, not a necessary condition for the unknown complete scalar. Pointwise complex asymptotics alone do not bound the summed error relative to $P_H$. The source mapping and these transfer obligations are paper-level applications, with the signed comparison and RH/Robin unresolved.
