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
