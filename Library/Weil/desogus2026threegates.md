---
bibkey: desogus2026threegates
authors: Marco Desogus
year: 2026
title: "The Three Gates: A Rooted-Operator Approach to Weil Positivity"
doi: null
url: https://arxiv.org/abs/2609.20367v3
claim: The preprint claims all-scale odd-channel Weil positivity via a common-cut Schur induction; this note records its actual-operator proof interfaces without adopting its claimed RH proof as a verified input.
strata_touched: []
license: citation-only
triage: anchor
---

# Common-cut Schur induction: an unadopted all-scale claim

The source claims RH through all-scale positivity of the actual localized Weil operator on the real odd logarithmic channel. The claims below are version-specific: the current arXiv v3 is internally labelled V4; the older two-arm audit applies to arXiv v2. The full proof and supplementary certificates are not independently verified project premises, and no actual-arithmetic counterexample to either main claim is established here.

## Current arXiv v3 interface: one exact source debit

The current primary is [arXiv:2609.20367v3](https://arxiv.org/abs/2609.20367v3), revised **6 October 2026** and internally labelled **V4**, 69 pages. Its [supplement](https://doi.org/10.5281/zenodo.23198201) is a different versioned deposit from the v2 archive. The paper still claims RH; the conclusion and the certificates are not independently verified project premises.

Audit statement 6.28 explicitly excludes the special multiplication-minus-rank-one folded Hessian from the active proof. Lemma 8.5 instead uses the exact reduced common-source metric and forcing, after one common-complement short, on the full-operator harmonic vector $F=H_kf$. Its source row and single debit are

$$
\mathsf C_k^{\rm src}x_k=\lambda_k(c_k),\qquad
D_k^{\rm src}=\langle\lambda_k(c_k),(\mathsf C_k^{\rm src})^{-1}\lambda_k(c_k)\rangle.
$$

The square completion in MASTER-P3b is the standard exact Schur identity; (200) is its covariance under a unitary change of source coordinates. The source invokes the positive old block for the source metric's positivity, and treats the endpoint fold solely as unitary transport. Thus the v2 two-arm formulas and their auxiliary physical-pivot condition are not active inputs to this version. The v2 scalar example below is not a counterexample to the v3 construction. No second debit should be imposed just because that older parametrization had two arms.

### The reference term must be part of the actual reduced form

Lemma 8.1, (190)–(193), identifies the inherited row at its exact minimizer with the negative metric energy

$$
\mathcal I_{k,m}^{\rm act}
=-\mathscr S_{k,m}^{\rm ex}[r_m c_m^{\rm inh}].
$$

Corollary 8.2 then asserts an aligned positive reference contribution on the same reduced row and uses

$$
\mathscr S_{k,m}^{\rm ex}[r_m^0c_m^{\rm inh}]
+\mathcal I_{k,m}^{\rm act}
=|c_m^{\rm inh}|^2\Delta\mathscr S_{k,m}^{\rm ex}
\ge(1-\theta_{k,m}^2)\Pi_m^{(0)}|X_m|^2,
\qquad X_m=\varepsilon_{k,m}\sqrt{C_m}\,c_m^{\rm inh}.
$$

The equality is quadratic homogeneity once the reference term is present. The quantitative input not supplied by that equality is its provenance and allocation inside the actual full reduced Weil form. In (190) the frozen-coordinate remainder $\mathcal Q_{k,m}^{\rm rest}$ is independent of the varied inherited coordinate. Stationarity supplies the negative response contribution, not an extra positive reference energy. On the harmonic graph the inherited coordinate depends on the prescribed target, so this does not refute the possibility of a valid reference contribution. Its identification requires the actual remainder and target/source transport, with no reuse of the direct target diagonal $\mathfrak B_k\|c_k\|^2$, the same source metric, or a reserve already charged elsewhere.

Theorem 8.6 consumes that reference–actual splice, Lemma 8.3's homogeneous parent estimate, the literal-slot true-ground leakage correction in Corollary 6.57/Certificate 6.58, and the complete one-debit source ledger. Theorem 6.53 states a joint operator lower form, stronger than testing pure directions separately; its statement can be cited as a source claim. Its active obligation is a lower bound on the *whole same harmonic vector*, including every source-row component and every mixed term. Separate bounds for pure target-ground and pure target-transverse data do not by themselves supply that combined lower bound. No additional ground/transverse covariance of the full source metric is inferred from branch ground-line invariance.

The complete archimedean/source correspondence remains necessary: Proposition 5.3 and the one-cell source metric used in Theorem 6.53/Lemma 6.61 must carry the full potential, regular kernel, pole and common-complement domain through to that same reduced vector. The normalization benchmarks below are reused, not recomputed. The v3 generic Schur and unitary identities do not establish this actual-family comparison.

The restricted odd Weil criterion and endpoint closure remain separate consumers; odd-only testing is not dismissed. The bounded primary check supplies no signed Robin main estimate, new positivity theorem, numerical certificate or RH proof. It also establishes no actual-arithmetic counterexample to v3. Its reusable source conclusion is that v2's retired double-arm reduction must not be used to reject v3, while the positive reference contribution and full-form comparison still require verification before Theorem 8.6 can be adopted.

## A full-pole bound for the literal physical collar

Use the physical form defined by (9)–(15) and (61)–(63) of arXiv v3. This calculation concerns its literal old/new compression, not the whole arithmetic target cell and not a free-complement source short. The source's identification of that form with the global Weil form, and its subsequent common-cut transport, retain their separate verification obligations.

For every integer $k\ge7$, set

$$
a=\frac12\log k,\qquad b=\frac12\log(k+1),\qquad
h=b-a=\frac{w_k}{2},\qquad w_k=\log(1+1/k).
$$

Let $\mathcal K_k$ be the odd functions supported in $(-b,-a)\cup(a,b)$, initially on the smooth compactly supported core. Denote by $D_k^A$ the compression of the complete source-defined operator $A_{b,-}$ to this collar; thus this is the new diagonal in the full physical old/new block matrix. Write

$$
\mathfrak B_k=\frac12+\log(1/w_k),\qquad
\tau_k=\|s^{\rm ph}\mathbf1_{(-b,-a)\cup(a,b)}\|_2^2
=\sinh b-\sinh a-h.
$$

The pole quantity is the source's exact restriction identity (114), not a profile replacement.

### No prime-power term survives inside this new block

A same-side collar overlap would require a displacement smaller than $h<\log2$. A cross-side overlap would require

$$
2a<\log n<2b,\quad\text{or equivalently}\quad k<n<k+1.
$$

Neither can hold for an integer prime power $n\ge2$. Boundary contact at $n=k$ has zero measure. Consequently every prime-power translation in the complete new/new compression vanishes, including prime powers at the arithmetic endpoint. The old/new coupling remains present in the full operator.

### Retain the reflected Gamma contribution and the true pole

Identify an odd collar vector isometrically with $u\in L^2(a,b)$ by taking $u(y)/\sqrt2$ on the positive interval and $-u(-y)/\sqrt2$ on the negative interval. Put $g(v)=\sqrt h\,u(a+hv)$ for $0<v<1$. Reuse the [single-interval archimedean compression benchmark](#full-form-transport-benchmarks-and-the-v2-correspondence-input). Combining its two reflected copies gives the complete diagonal identity

$$
\begin{aligned}
\langle u,D_k^Au\rangle
={}&\mathfrak b[g]-[\log(2\pi h)+\gamma]\|u\|_2^2
-\iint_{(a,b)^2}\rho(|y-z|)u(y)\overline{u(z)}\,dy\,dz\\
&+\iint_{(a,b)^2}\kappa(y+z)u(y)\overline{u(z)}\,dy\,dz
-4\left|\int_a^b\sinh(y/2)u(y)\,dy\right|^2,
\end{aligned}
\tag{C1}
$$

where $\rho(r)=e^{-r/2}/(1-e^{-2r})-1/(2r)$ and

$$
\kappa(r)=\frac1{2r}+\rho(r)
=\frac{e^{-r/2}}{1-e^{-2r}}
=\sum_{j\ge0}e^{-(2j+1/2)r}.
$$

Thus the reflected term is positive as an operator, not merely pointwise:

$$
\iint\kappa(y+z)u(y)\overline{u(z)}\,dy\,dz
=\sum_{j\ge0}\left|\int_a^b e^{-(2j+1/2)y}u(y)\,dy\right|^2\ge0.
\tag{C2}
$$

The sum converges because $a\ge\frac12\log7>0$. The reflected singular and regular kernels must be combined before using this sign.

For $0\le r\le h<1/2$, the continuous extension of the regular kernel obeys

$$
0\le\rho(r)\le\frac14.
\tag{C3}
$$

For the upper bound, equivalently $(2+r)\sinh r\ge2r e^{r/2}$, the odd power coefficients after the first are $2[1-(2j+1)/4^j]/(2j+1)!$ and the even ones are $[1-1/4^j]/(2j+1)!$, all nonnegative. For the lower bound, $\sinh r/r\le\cosh r\le e^{r^2/2}\le1+r^2\le1+r/2\le e^{r/2}$ for $r\le1/2$. Schur's kernel bound therefore gives an operator norm at most $h/4=w_k/8$ on this interval.

The already supplied one-cell form has $\mathfrak b[g]\ge(\log2)\|g\|_2^2$. Its stronger spectral constant may be retained: the [existing small-window source](frankliebseiringer2006hardy.md#reuse-the-stronger-small-window-spectral-floor) defines $\mu_1>0$ and gives $\mathfrak b[g]\ge(\log2+\mu_1)\|g\|_2^2$ after the affine unitary. No local spectral theorem is reproved here. Finally Cauchy–Schwarz bounds the full negative pole by $2\tau_k\|u\|_2^2$. Hence (C1) yields the all-$k$ literal-collar lower bound

$$
\boxed{
D_k^A\succeq
[\mathfrak B_k-C_k+\mu_1]I,
\qquad
C_k=\frac12+\log(\pi/2)+\gamma+\frac{w_k}{8}+2\tau_k.
}
\tag{C4}
$$

Dropping only the known positive $\mu_1$ gives the weaker explicit coefficient. This bound applies on the displayed smooth core and its Friedrichs form closure; it is not an assertion that an unproved transported source domain coincides with that closure.

There is a uniform elementary allowance:

$$
\begin{aligned}
2\tau_k
&=\sqrt{k+1}-\sqrt k+\frac1{\sqrt k}-\frac1{\sqrt{k+1}}-w_k\\
&<\frac1{2\sqrt k}+\frac1{2k^{3/2}}
\le\frac4{7\sqrt7}<\frac{20}{91},\qquad
\frac{w_k}{8}<\frac1{56}.
\end{aligned}
$$

Using the standard constant bounds $\gamma<3/5$, $\log(\pi/2)<23/50$ and $\sqrt7>13/5$, one obtains

$$
C_k<\frac{39}{25}+\frac1{56}+\frac{20}{91}
=\frac95-\frac{43}{18200}<\frac95.
\tag{C5}
$$

Consequently $D_k^A\succeq(\mathfrak B_k-9/5)I$ in this realization. The Gamma reflection sign, vanished prime overlaps and true negative pole all refer to the same physical vector.

### The constant target diagonal is not the whole physical compression

The existing small-window domain argument permits the constant profile in the closed form. Let $u_k=h^{-1/2}$ on $(a,b)$ and take its odd pair as above. Then $\mathfrak b[1]=1$, the self-regular term is $O(h)$, the reflected term is $O(hk^{-1/2})$, and the pole is $O(k^{-1/2})$. Since $h=w_k/2$, (C1) gives

$$
\langle u_k,D_k^Au_k\rangle-\mathfrak B_k
\longrightarrow\frac12-\log\pi-\gamma<0.
\tag{C6}
$$

Therefore the scalar $\mathfrak B_k I$ is not equal to, or a lower bound for, the complete literal physical new diagonal. This does not refute a decomposition in which $\mathfrak B_k$ is one named primal term accompanied by further diagonal contributions. Any such decomposition must retain those contributions and the actual old/new transport before consuming MASTER-P3c. Nor is (C6) a negative test for the full Weil form: the actual diagonal grows like $\log k$.

The new interface is the complete prime-free odd collar comparison (C1)–(C5), with (C6) specifying its normalization. The one-cell floor, basic compression benchmark, Schur kernel estimate and exact pole restriction are reused. The global signed obligation remains the old/source inverse debit on the same harmonic vector; no positive aligned reference contribution is supplied by this diagonal bound, and no Robin or RH conclusion follows alone. The source's finite MASTER margin must not be transported through (C5) without a paid common-source identification and a compatible all-scale tail.

## A pole-free odd null family tests the raw old/source metric

The following calculation concerns the complete compact-test Weil form and its actual pole-free odd core. It tests a proposed identification of a raw old-block variational short with a uniformly positive one-cell source metric. It does not identify the source's allocated common-cut component with that raw short, and does not assert that the source's full induction is refuted.

Reuse the theta transform, all-order weighted derivative tails, compact weighted-two-jet bridge and multiplicity-weighted zero summability already recorded in [the localization note](frankliebseiringer2006hardy.md#the-exact-auxiliary-line-does-not-replace-the-discarded-residual). The published xi null-vector mechanism and the existing [critical derivative family](lagarias2004li.md#the-full-derivative-family-and-the-remaining-estimate) are not new results here. The additional interface is their quantitative comparison with a moving *actual prime-power collar source slot*, retaining the odd sector and annihilating the true pole.

### An odd test family that also annihilates the pole

Let $\Phi$ be the original positive even theta kernel, with

$$
\widehat\Phi(z)=\xi(1/2+iz),\qquad
\widehat f(z)=\int_{\mathbb R}f(y)e^{-izy}\,dy.
$$

Define the real odd rapidly decaying function

$$
g(y)=\Phi'''(y)-\frac14\Phi'(y).
$$

Tilted integration by parts, justified by the retained all-order theta tails, gives

$$
\int_{\mathbb R}g(y)e^{zy}\,dy
=-z(z^2-1/4)\xi(1/2+z).
\tag{O1}
$$

In particular this transform vanishes at every actual centered zero, with no assumption on its real part, and at both pole arguments $z=\pm1/2$. Thus

$$
\int_{\mathbb R}g(y)\sinh(y/2)\,dy=0.
\tag{O2}
$$

The function $g$ is nonzero: its real Fourier transform is $(it)((it)^2-1/4)\xi(1/2+it)$, which is nonzero for sufficiently small nonzero $t$ because $\xi(1/2)>0$. It follows by oddness and continuity that there is a positive point at which $g$ is nonzero. Fix a dyadic rational $M>1$ such that

$$
y_0=\frac12\log M>0,\qquad g(y_0)\ne0.
$$

Such an $M$ exists because dyadic rationals are dense in $(1,\infty)$ and the nonzero set is open. This choice requires no prime-distribution estimate.

### Use a real fresh prime-power branch at arbitrarily large endpoints

Write $M=p/2^d$ with positive integers $p,d$, allowing $d=0$. For sufficiently large integers $j$, put

$$
n_j=2^j,\qquad k_j=M n_j^2+1,\qquad
a_j=\frac12\log k_j,\quad b_j=\frac12\log(k_j+1),\quad h_j=b_j-a_j.
$$

For $j\ge d$, $k_j$ is an integer, $M n_j$ is an integer, and $n_j\nmid k_j$. Thus $n_j$ is an active fresh prime power in the source's arithmetic routing, with $\Lambda(n_j)=\log2$. Its actual translated positive physical collar source slot is

$$
J_j=(a_j-\log n_j,\ b_j-\log n_j)
\Subset(-a_j,a_j).
\tag{O3}
$$

Both endpoints tend to $y_0$, and $k_jh_j\to1/2$. Its reflected partner is $-J_j$, disjoint from $J_j$ for sufficiently large $j$.

These are literal prime-translation source intervals. They are also contained in the source's full arithmetic slot: at endpoint $Y=k_j+1$, the exact Mellin coordinate is $t=e^{y+b_j}$, so

$$
\left[\frac{k_j}{n_j},\frac{k_j+1}{n_j}\right)
\quad\longleftrightarrow\quad
[a_j-h_j-\log n_j,\ b_j-\log n_j).
\tag{O4}
$$

The parent index is $m_j=\lfloor k_j/n_j\rfloor=M n_j$ and the non-divisorial residue is exactly $1$. The Mellin substitution preserves $dy=dt/t$, so a source-slot unitary preserves the norm used below. No abstract interval is substituted for this branch.

### The complete old-core energy is smaller than every power of the slot width

Fix a real even $\chi\in C_c^\infty(-1,1)$, equal to one on $[-1/2,1/2]$, and set

$$
u_j(y)=\chi(y/a_j)g(y).
$$

This is an actual real odd compact smooth test in the old physical support $(-a_j,a_j)$, and agrees with $g$ on $J_j\cup(-J_j)$ for all sufficiently large $j$. The reused weighted derivative tails, with the cutoff starting at $|y|=a_j/2$, give

$$
\epsilon_j:=\int e^{|y|/2}
\bigl(|u_j-g|+|(u_j-g)''|\bigr)dy
=O_R(k_j^{-R})\qquad\text{for every }R>0.
\tag{O5}
$$

Indeed $e^{2|y|}\ge e^{a_j}=\sqrt{k_j}$ on the error support; any polynomial factor from the fixed derivatives and the cutoff is absorbed by the original $e^{-c\sqrt{k_j}}$ tail. The constants may depend on $R$, $M$, $g$ and the fixed cutoff, but not on $j$.

Use the complete compact Weil explicit formula with

$$
z_\rho=\Im\rho-i(\Re\rho-1/2),\qquad
Q(u_j)=\sum_\rho m_\rho\widehat u_j(z_\rho)
\overline{\widehat u_j(\overline{z_\rho})}.
$$

Both limiting factors vanish by (O1), including the reflected zero $1-\overline\rho$. The weighted-two-jet estimate gives

$$
|\widehat{u_j-g}(t+iw)|\le\frac{2\epsilon_j}{1+t^2},
\qquad |w|\le1/2.
$$

Consequently the already supplied finite sum $S_4=\sum_\rho m_\rho(1+(\Im\rho)^2)^{-2}$ yields $|Q(u_j)|\le4S_4\epsilon_j^2$. The paired factors have not been replaced by modulus squares off the critical line.

Write the true polar-free old form, on this same compact core, as

$$
C_{a_j}[u_j]=Q(u_j)+2\left|\int u_j(y)\sinh(y/2)dy\right|^2.
$$

Equation (O2) and $|\sinh(y/2)|\le e^{|y|/2}/2$ bound the added term by $\epsilon_j^2/2$. Therefore

$$
|Q(u_j)|+|C_{a_j}[u_j]|
=O_R(k_j^{-R})\qquad\text{for every }R>0.
\tag{O6}
$$

Only compact tests are evaluated by the arithmetic form. No new form on noncompact functions, RH assumption or sign of $Q(u_j)$ is asserted. If the source-defined $A_{a,-}$ and $C_a$ are identified with these complete Weil forms on their common core, the same estimate applies to those operators; that identification retains its independent obligation.

In contrast, their actual slot data have polynomially sized mass:

$$
\ell_j:=\|\mathbf1_{J_j\cup(-J_j)}u_j\|_2^2,
\qquad k_j\ell_j\longrightarrow |g(y_0)|^2>0.
\tag{O7}
$$

Thus neither the complete odd old form nor its true polar-free core admits, for any fixed $c>0$, the bound

$$
q_{a_j}[v]\ge c\|\mathbf1_{J_j\cup(-J_j)}v\|_2^2
\quad\text{for every old compact odd test }v
\tag{O8}
$$

at all sufficiently large $j$. Taking $v=u_j$ gives the failure directly, independently of whether $q_{a_j}$ is positive.

### A raw common-source short must retain these nearly null directions

Whenever the actual old form $q_{a_j}$ has a positive closed realization and the variational short under consideration, let $S_j=-S_j\subset(-a_j,a_j)$ be either this reflected slot pair or a reflection-symmetric union of actual old source slots containing it. Work on $\mathcal H_j=L^2_{\mathrm{odd}}(S_j,dy)$, with the inherited $L^2$ norm, and define

$$
q_j^{\mathrm{short}}[r]
=\inf\{q_{a_j}[v]:v\in D(q_{a_j}),\ v\text{ odd},\ \mathbf1_{S_j}v=r\}.
$$

Assume the valid closed short on this data space when invoking its associated operator or inverse. Reflection symmetry makes the support restriction an orthogonal projection within the odd old space. Put $r_j=\mathbf1_{S_j}u_j\in\mathcal H_j$. By this definition and (O6)–(O7),

$$
0\le\operatorname{Short}_{S_j}q_{a_j}[r_j]
\le q_{a_j}[u_j],\qquad
\frac{\operatorname{Short}_{S_j}q_{a_j}[r_j]}{\|r_j\|_2^2}
=O_R(k_j^{-R})\quad\text{for every }R>0.
\tag{O9}
$$

This holds on any cofinal subsequence satisfying the stated positivity/shorting conditions, for the full odd form or the pole-free core. If the associated exact short operator on $\mathcal H_j$ is additionally strictly positive with a bounded inverse, the usual positive-operator Cauchy--Schwarz inequality makes that inverse norm grow faster than every fixed power of $k_j$ along the subsequence. It supplies no lower bound for the actual debit $B_{A,k}^*A_k^{-1}B_{A,k}$, since that forcing need not lie in the normalized $r_j$ direction.

The one-cell source model and its CMC/ground lower bounds remain valid in their declared realization. Equations (O8)–(O9) exclude identifying them with a uniformly coercive lower bound for this *whole raw actual old/source short* by source-slot unitaries alone. A valid full-form allocation may instead separate an archimedean component, retain compensating arithmetic/pole/target terms, or estimate the actual forcing after a justified treatment of the critical family. Such an allocation must be proved on the same object; the known one-cell floor cannot be imported as a raw old inverse bound. This is a specific realization boundary, not a refutation of the source's allocated-component claim or of its full induction.

The all-scale signed Robin estimate remains unproved. The application supplies a quantitative test for the missing raw metric correspondence and explains why an actual directional inverse estimate, including the nearly null family, is still required. Classical nullity, theta tails, zero summability and variational shorting are reused; the moving prime-power slot comparison (O3)–(O9) is the additional paper-level interface, without a new Lean certification or mathematical-priority claim.

## Complete collar response versus one actual prime branch

Retain the actual odd family, integer endpoints and compact cutoffs from (O1)–(O9). This calculation gives the full old-to-new response of that family, uniformly against every $L^2$ odd collar probe. It complements the raw source-metric boundary; it does not estimate the old inverse debit on arbitrary forcing.

Reuse the [complete mixed Weil pairing and compact-domain bridge](lagarias2004li.md#mixed-nullity-needs-a-domain-bridge), the [general two-pole and prime formula](frankliebseiringer2006hardy.md#ordinary-windows-require-both-poles), and the classical multiplicity-weighted inverse-square zero mass recorded in [the resolvent supplier](broadbent2026mertens.md#an-upper-budget-in-the-actual-logarithmic-gamma-energy). No mixed-nullity or zero-summability theorem is reproved. The even theta-weighted commutator bounds in [the exterior account](lenz2010compactness.md) are not assigned to the physical odd metric without a map.

Write

$$
E_j=(-b_j,-a_j)\cup(a_j,b_j),\qquad
\alpha_j=\sqrt{2h_j}\,e^{b_j/2},\qquad
S_2=\sum_\rho\frac{m_\rho}{1+(\Im\rho)^2}<\infty,
\qquad m_j=\int u_j(y)\sinh(y/2)dy.
$$

All zeros in $S_2$ are actual nontrivial zeros, with both ordinate signs and every multiplicity. Put $B_Q$ for the full compact Weil pairing, linear in the first argument. For a compact smooth odd $v$ supported in $E_j$, the disjoint supports eliminate multiplication terms. The same general explicit formula gives the physical response $Y_j^Q$ by

$$
\begin{aligned}
Y_j^Q(y)={}&-\int_{-a_j}^{a_j}\kappa(|y-z|)u_j(z)\,dz
-2\sinh(y/2)m_j\\
&-\sum_{2\le n\le k_j}\frac{\Lambda(n)}{\sqrt n}
\bigl(u_j(y+\log n)+u_j(y-\log n)\bigr),\qquad y\in E_j,\\
B_Q(u_j,v)={}&\langle Y_j^Q,v\rangle_{L^2(E_j)},
\qquad \kappa(t)=\frac{e^{-t/2}}{1-e^{-2t}}.
\end{aligned}
\tag{O10}
$$

The theta cutoff has compact support strictly inside the old interval, so this Gamma cross integral is nonsingular. Every prime-power translation that can reach this collar is retained; translations with $n\ge k_j+1$ have no old/new overlap. The true negative odd pole has its coefficient $2$. Formula (O10) refers to the actual compact Weil form. Identifying the source-defined $B_{A,k_j}^*u_j$ with it still requires the source's complete common-core identification.

### A bound uniform over all collar coefficients

For $|w|\le1/2$, Cauchy--Schwarz on the actual collar gives

$$
|\widehat v(t+iw)|\le e^{b_j/2}\|v\|_1
\le\alpha_j\|v\|_2.
$$

The complete paired spectral formula is

$$
B_Q(u_j,v)=\sum_\rho m_\rho\widehat u_j(z_\rho)
\overline{\widehat v(\overline{z_\rho})},
\qquad z_\rho=\Im\rho-i(\Re\rho-1/2).
$$

Equation (O1) makes the limiting old factor zero at every $z_\rho$; (O5) bounds its actual error by $2\epsilon_j/(1+(\Im\rho)^2)$. The probe bound therefore pays the complete sum by $2S_2\alpha_j\epsilon_j\|v\|_2$. No bound on the probe's derivatives is required. Density of the smooth odd collar core and Riesz representation give

$$
\boxed{\|Y_j^Q\|_2\le2S_2\alpha_j\epsilon_j.}
\tag{O11}
$$

For the true pole-free core, its response is $Y_j^C=Y_j^Q+2m_j\sinh(y/2)|_{E_j}$. Using $|m_j|\le\epsilon_j/2$ from (O2) and $\|\sinh(y/2)\|_{L^2(E_j)}\le\alpha_j/2$ gives

$$
\boxed{\|Y_j^C\|_2\le(2S_2+1/2)\alpha_j\epsilon_j.}
$$

Since $\alpha_j\asymp k_j^{-1/4}$ and $\epsilon_j=O_R(k_j^{-R})$ for every $R>0$, both complete response norms are smaller than every fixed power of $k_j^{-1}$. This is a uniform $L^2$ collar estimate on the stated old family, not merely convergence for one fixed smooth probe. It uses the same actual zero real parts and paired factors; no critical-line or simple-zero assumption is made.

### The selected prime-power response alone is polynomially sized

Keep the literal contribution of $n_j=2^j$ in (O10):

$$
P_j(y)=-\frac{\log2}{\sqrt{n_j}}
\bigl(u_j(y+\log n_j)+u_j(y-\log n_j)\bigr).
$$

On the positive collar only $u_j(y-\log n_j)$ is present, and on the negative collar only its odd reflected partner is present. The source slots are exactly $J_j$ and $-J_j$ from (O3); the two translations preserve Lebesgue measure. Therefore

$$
\|P_j\|_2^2=\frac{(\log2)^2}{n_j}\ell_j,
\qquad
k_j^{3/2}\|P_j\|_2^2
\longrightarrow (\log2)^2\sqrt M\,|g(y_0)|^2>0.
\tag{O12}
$$

The selected response is thus of order $k_j^{-3/4}$ in norm. It is not a hypothetical edge or a prime sample: $n_j$ is the fresh branch with parent $Mn_j$ and residue one, at the same integer endpoint used in (O3)–(O9).

Let $R_j^Q$ consist of the Gamma and true pole terms in (O10), together with all the displayed prime-power terms except $n_j$. This is an independently specified sum of the actual remaining terms. Equations (O10)–(O12) give

$$
Y_j^Q=P_j+R_j^Q,\qquad
\frac{\|P_j+R_j^Q\|_2}{\|P_j\|_2}\longrightarrow0.
\tag{O13}
$$

Thus the remaining actual response cancels the polynomially sized selected prime response in relative $L^2$ norm on these collars. The same statement holds for the pole-free core with its actual pole-removal term included in $R_j^C$. Independent absolute estimates for these components would miss this joint relation. The cancellation is quantitative and on one actual source; it does not follow from independently achievable component bounds or from replacing a signed response by its norm.

### The inverse budget remains a separate estimate

Equations (O9) and (O11) show that a nearly null raw source metric and a small complete collar response can coexist, even though a single real prime branch remains polynomially large. They do not show that $B_{A,k}^*A_k^{-1}B_{A,k}$ is small. In particular, an upper bound on the coupling numerator and an upper bound on the old energy do not bound their quotient; a matching directed estimate and control of all other old directions remain required. No whole-form positivity, Robin main upper bound or RH conclusion is inferred.

The additional interface is the complete physical collar norm (O11) and its same-source comparison with the isolated actual prime branch (O12)–(O13). Classical mixed nullity, support Cauchy--Schwarz, Riesz representation, zero summability and the accepted moving-slot construction are reused. This is a paper-level application, without Lean certification or a mathematical-priority claim.

## A natural-tail cutoff pays one actual old direction

The small response in (O11) cannot be divided by the old-energy upper bound in (O6). The following chooses a different cutoff of the same odd null function and proves a matching lower denominator. It pays only the resulting one-dimensional old direction; the full inverse supremum remains separate.

Reuse the original theta series and derivative bounds in [the derivative-family account](lagarias2004li.md#the-full-derivative-family-and-the-remaining-estimate), the [compact weighted-jet/domain bridge and complete two-pole formula](frankliebseiringer2006hardy.md#the-exact-auxiliary-line-does-not-replace-the-discarded-residual), and the Gamma scaling calculation underlying [the physical compression benchmark](#full-form-transport-benchmarks-and-the-v2-correspondence-input). The even theta-weighted exterior and commutator estimates in [Lenz's application](lenz2010compactness.md) have a different metric and are not used as odd physical estimates.

Retain $g$, the fixed $M$, and the actual endpoints $k_j,a_j,b_j,h_j,E_j$ from (O1)–(O3) and (O10). Put

$$
R_j=a_j/2=\tfrac14\log k_j,\qquad
\delta_j=e^{-2R_j}=k_j^{-1/2}.
$$

Fix a real smooth function $0\le\eta\le1$, zero on $(-\infty,0]$ and one on $[1,\infty)$. Define a new compact odd old test and its actual error tail by

$$
\widetilde u_j(y)=\bigl(1-\eta((|y|-R_j)/\delta_j)\bigr)g(y),\qquad
e_j(y)=g(y)-\widetilde u_j(y).
\tag{T1}
$$

The multiplier is constant near zero, so the use of $|y|$ does not impair smoothness. The support of $\widetilde u_j$ lies in $[-R_j-\delta_j,R_j+\delta_j]\Subset(-a_j,a_j)$ for large $j$. It still agrees with $g$ on the actual reflected source slots. This is a change of the chosen test family, not a change of any arithmetic operator, prime branch or earlier cutoff statement.

### The actual tail has one natural width

Suppress $j$ temporarily and write $R=R_j$, $\delta=\delta_j$. Directly differentiating the reused theta series gives

$$
g(R)=-32\pi^5e^{21R/2}e^{-\pi e^{2R}}(1+O(e^{-2R})).
$$

Thus $A_R=-g(R)>0$ for large $R$. Let

$$
H_R(s)=-e_j(R+\delta s)/A_R,\qquad
H(s)=\eta(s)e^{-2\pi s},\qquad
c_\eta=\int_0^\infty H(s)^2ds>0,
$$

with both profiles zero for $s\le0$. The same first theta term and its derivatives, with the remaining normally convergent series exponentially smaller, show

$$
H_R\longrightarrow H\quad\text{in }L^1\cap H^2,
\qquad
|H_R^{(m)}(s)|\le C_m e^{-c s}\quad(s\ge0,\ 0\le m\le2),
\tag{T2}
$$

for fixed $c>0$ and constants independent of large $R$. Indeed
$e^{2R}(e^{2\delta s}-1)\ge2s$ and $\delta e^{2R}=1$; the polynomial factors from each fixed derivative are absorbed by this exponential. On bounded $s$ the leading term tends to $e^{-2\pi s}$, giving the stated dominated convergence. Consequently the actual odd error mass is

$$
M_R:=\|e_j\|_2^2=2A_R^2\delta(c_\eta+o(1)).
\tag{T3}
$$

These theta consequences are intermediate applications, not independent new theta identities.

### A complete-form bridge for this noncompact error

Only $\widetilde u_j$ is an old compact arithmetic test. To calculate its energy, approximate the fixed-$j$ error $e_j$ by real even compact cutoffs times $e_j$. The reused all-order theta tails pay the weighted two-jet error and both pole integrals. They also supply the Gamma small-shift bound by the first derivative and an integrable large-shift majorant.

For the complete prime sum, the same two-tail estimate used in the derivative-family domain passage applies:

$$
e^{2|y|}+e^{2|y-\log n|}\ge2n.
$$

Products of fixed theta derivatives therefore have integrated majorant $C_j n^{d_j}e^{-c_j n}$, including every prime power and independent of the outer approximation cutoff. This proves absolute convergence and dominated passage for the prime correlations. The full paired zero sum passes by the weighted-jet bridge and multiplicity-weighted inverse-fourth zero mass.

Write $Q^{\rm tail}(e_j)$ for this particular limit of the complete arithmetic expressions. This defines neither a new closed operator nor positivity on an arbitrary noncompact domain. At every actual zero, (O1) gives $\widehat e_j(z_\rho)=-\widehat{\widetilde u_j}(z_\rho)$, and likewise for the reflected factor. Thus, with actual zero real parts, both signs and multiplicities unchanged,

$$
Q(\widetilde u_j)=Q^{\rm tail}(e_j),\qquad
B_Q(\widetilde u_j,v)=-B_Q^{\rm tail}(e_j,v)
\tag{T4}
$$

for every compact smooth odd collar probe $v$. The same domain passage supplies the mixed equality. This reuses full mixed nullity rather than replacing the off-line pair by a modulus square.

On this tail the complete expression is

$$
\begin{aligned}
Q^{\rm tail}(e_j)={}&c_\Gamma\|e_j\|_2^2
+\int_0^\infty\kappa(t)\|e_j-\tau_t e_j\|_2^2dt\\
&-2\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
\Re\langle e_j,\tau_{\log n}e_j\rangle
-2\left|\int e_j(y)\sinh(y/2)dy\right|^2,
\end{aligned}
\tag{T5}
$$

where $c_\Gamma=\Re\operatorname{digamma}(1/4)-\log\pi$ and $\kappa$ is exactly (O10). The unbounded prime sum is paid by the domain bridge; it is not truncated at the compact old endpoint.

### The lower denominator retains Gamma, every prime and the true pole

For one positive-tail copy $f_R(y)=-A_R H_R((y-R)/\delta)$, the reused Gamma dilation calculation has the explicit form

$$
\int_0^\infty\kappa(t)\|f_R-\tau_t f_R\|_2^2dt
=A_R^2\delta\int_0^\infty\delta\kappa(\delta s)
\|H_R-\tau_sH_R\|_2^2ds
=\bigl(\log(1/\delta)+O(1)\bigr)\|f_R\|_2^2.
$$

For completeness, the profile bounds in (T2) pay the uniform remainder: below $s=1$ use the derivative bound; above it write the squared increment as $2\|H_R\|_2^2-2\Re\langle H_R,\tau_sH_R\rangle$, with exponentially decaying correlation. The scalar integral obeys $2\int_\delta^\infty\kappa(t)dt=\log(1/\delta)+O(1)$. This is the existing kernel scaling mechanism, consumed here with a noncompact but controlled profile.

The reflected tail cross term is at separation at least $2R$, so its absolute value is at most $C A_R^2\delta^2e^{-R}=O(e^{-3R}M_R)$. Combining the two tails and the actual $c_\Gamma$ gives the Gamma part $(2R+O(1))M_R$.

The same-side prime correlations satisfy $C A_R^2\delta e^{-c t/\delta}$. Their sum over $t=\log n\ge\log2$, using only $\Lambda(n)\le\log n$, is exponentially small in $1/\delta$ relative to $M_R$. Opposite tails only correlate for $t\ge2R$; putting $v=(t-2R)/\delta$ bounds the correlation by $C A_R^2\delta(1+v)e^{-c v}$. Absorb the polynomial into a smaller exponential. For $T=e^{2R}=1/\delta$, elementary integral comparison then gives

$$
\sum_{n\ge\lceil T\rceil}\frac{\log n}{\sqrt n}
e^{-c\log(n/T)/\delta}\le C R e^{-R}.
$$

Hence the absolute value of the full prime correction is at most $C R e^{-R}M_R$. No prime-distribution hypothesis or finite prime sample is used. The true odd pole is also controlled on this same error:

$$
\left|\int e_j(y)\sinh(y/2)dy\right|
\le C A_R\delta e^{R/2},\qquad
2\left|\int e_j\sinh(y/2)\right|^2\le C e^{-R}M_R.
$$

Equations (T3)–(T5) therefore give the matching complete lower energy

$$
\boxed{Q(\widetilde u_j)=(2R_j+O(1))M_{R_j}>0\quad(j\text{ large}).}
\tag{T6}
$$

The actual pole-free old energy has the same asymptotic, since it adds precisely the displayed pole square. This establishes positivity only for this specified compact family.

### The complete physical collar row at the same scale

Let $\widetilde Y_j^Q$ be the literal response (O10) with $u_j$ replaced by $\widetilde u_j$. Use (T4) to estimate it from the tail. The whole-line Gamma row of $e_j$ has its local multiplier and symmetric difference integral retained. On $y\in(a_j,b_j)=(2R_j,2R_j+h_j)$ its local small-shift part is negligible by the original theta tails, while the remote part is bounded by

$$
C A_R\delta e^{-R/2}.
$$

One can split at $t=R/2$: below it, $y\pm t\ge3R/2$ and the symmetric small-shift difference is paid by the second derivative; above it, (T2) and $\kappa(t)\le C e^{-t/2}$ bound the near-$R$ tail by $A_R\delta e^{-(y-R)/2}$ and its reflected partner by $A_R\delta e^{-(y+R)/2}$. The remaining theta tail is smaller than these budgets.

The full prime row is estimated without deleting the translations beyond the old compact threshold. For $T_-=e^{y-R}$ and $T_+=e^{y+R}$, the two source regions of $e_j(y-\log n)$ give

$$
\begin{aligned}
\sum_{2\le n\le T_-}\frac{\Lambda(n)}{\sqrt n}
|e_j(y-\log n)|&\le C A_R\log T_-\bigl(T_-^{-1/2}+\delta T_-^{1/2}\bigr),\\
\sum_{n\ge T_+}\frac{\Lambda(n)}{\sqrt n}
|e_j(y-\log n)|&\le C A_R\log T_+\bigl(T_+^{-1/2}+\delta T_+^{1/2}\bigr).
\end{aligned}
$$

These follow by summing the bounds $(n/T_-)^{c/\delta}$ and $(n/T_+)^{-c/\delta}$ from (T2), respectively, and using $\Lambda(n)\le\log n$. Endpoint terms are retained in the integral comparison, including when $\delta T_-<1$. Since $T_-\asymp e^R$, $T_+\asymp e^{3R}$ and $\delta=e^{-2R}$, their total is $C A_R R e^{-R/2}$. The other orientation $e_j(y+\log n)$ is smaller than every exponential in $R$ relative to $A_R$ by the same bound. Odd reflection supplies the negative collar, with no omitted orientation.

Finally the true pole row is bounded by
$2|\int e_j\sinh(y/2)|\sinh(y/2)\le C A_R e^{-R/2}$ on the positive collar. Thus (T4), with all local, Gamma, prime and pole terms retained, gives

$$
\boxed{\|\widetilde Y_j^Q\|_2^2
\le C h_j A_{R_j}^2R_j^2e^{-R_j}.}
\tag{T7}
$$

This is a full physical $L^2(E_j)$ row bound, uniform in every collar coefficient. The true pole-free core response satisfies the same bound, since its actual pole-removal term has the just-displayed size. Its identification with source-defined operators still requires the complete common-core map.

### A correctly directed rank-one debit, with the other directions unpaid

Since $h_j\asymp e^{-4R_j}$, (T3), (T6) and (T7) now supply a lower denominator and upper numerator on the same actual test:

$$
\boxed{
\frac{|B_Q(\widetilde u_j,v)|^2}{Q(\widetilde u_j)}
\le C R_j e^{-3R_j}\|v\|_2^2
\le C(\log k_j)k_j^{-3/4}\|v\|_2^2.
}
\tag{T8}
$$

It holds for every odd $L^2$ collar $v$, by the response representation and density; the denominator is positive for large $j$ by (T6), without an all-support positivity assumption. The same statement holds with the true pole-free form in both numerator and denominator. Constants may depend on the fixed smooth transition and theta kernel, but not on $j$ or $v$.

Equation (T8) pays the variational debit restricted to the line $\mathbb C\widetilde u_j$. It is not the supremum over the full old space, does not remove cross terms with its old complement, and does not bound the entire operator $B_{A,k}^*A_k^{-1}B_{A,k}$. Applying it to that source's restricted line remains conditional on the source's complete form and norm identification. The original signed Robin main estimate and RH remain open.

The additional interface is the matched complete physical old-energy/collar-response quotient (T6)–(T8) at the natural theta-tail width. Theta nullity and tails, Gamma dilation, the full explicit formula and standard comparison/domain arguments are reused as inputs. The calculation is paper-level, without Lean certification or a mathematical-priority claim.

## Joint control of a fixed derivative space at actual collars

Fix an integer $d\ge1$. A separate bound for each of $d+1$ old lines does not control their joint variational debit: their actual energy Gram can have much smaller directions. The following controls every complex combination, including coefficients depending on the endpoint, using the same natural-tail cutoff and physical form as (T1)–(T8).

Reuse the [full theta derivative family and its compact-domain bridge](lagarias2004li.md#the-full-derivative-family-and-the-remaining-estimate), [Romik's original series and natural tail scale](../Analytic/romik2021orthogonal.md#reusable-theta-tail-and-its-local-scale), and the complete Gamma, prime and two-pole bounds in (T4)–(T7). The common negative-edge Gram in the [even critical-space account](lagarias2004li.md) has a different measure, parity and form; its invertibility is not an inverse bound for the present odd physical energy. Classical polynomial interpolation and finite-dimensional Gram stability are used inside the joint estimate, not presented as new supplier theorems.

Let $D=d/dy$ and define

$$
g_m=D^{2m+1}(D^2-1/4)\Phi,\qquad 0\le m\le d.
$$

The existing theta transform and tilted integration by parts give

$$
\int g_m(y)e^{zy}dy
=-z^{2m+1}(z^2-1/4)\xi(1/2+z).
$$

Every $g_m$ is odd, vanishes at all actual zeros in this transform, and annihilates both pole arguments. Retain the actual $k_j,a_j,b_j,h_j,E_j$, $R_j=\log(k_j)/4$, $\delta_j=e^{-2R_j}$ and the one fixed smooth transition $\eta$ from (T1). Write

$$
\chi_j(y)=1-\eta((|y|-R_j)/\delta_j),\qquad
U_{j,d}=\operatorname{span}_{\mathbb C}\{\chi_jg_0,\ldots,\chi_jg_d\}.
\tag{T9}
$$

All these tests have the same compact old support. The coefficients in $U_{j,d}$ are unrestricted at each $j$; no fixed-vector limit is substituted for a uniform estimate.

### Resolve coalescing tails before taking an inverse

Suppress $j$ and put $R=R_j$, $\delta=e^{-2R}$, $T=e^{2R}=1/\delta$. In the original theta series the $n=1$ term is

$$
\Phi_1(y)=e^{y/2}P(X)e^{-\pi X},\qquad
X=e^{2y},\quad P(X)=4\pi^2X^2-6\pi X.
$$

Differentiation acts on its polynomial by

$$
\mathcal D=\tfrac12+2X\tfrac d{dX}-2\pi X.
$$

Thus the first-term polynomial for $g_m$ is

$$
p_m=(\mathcal D^{2m+3}-\tfrac14\mathcal D^{2m+1})P,
\qquad
\nu_m=\deg p_m=2m+5,\qquad
a_m=4\pi^2(-2\pi)^{2m+3}
$$

with leading coefficient $a_m$. Introduce the scaled jet matrix

$$
\mathsf J(T)_{s,m}
=\frac{T^s p_m^{(s)}(T)}{s!\,a_mT^{\nu_m}},\qquad 0\le s,m\le d.
\tag{T10}
$$

Since every lower polynomial coefficient is fixed, $\mathsf J(T)_{s,m}=\binom{\nu_m}{s}+O_d(T^{-1})$. The limiting matrix is invertible: the standard polynomial Vandermonde determinant is

$$
\det\left[\binom{\nu_m}{s}\right]_{s,m=0}^d
=\frac{\prod_{m<n}(\nu_n-\nu_m)}{\prod_{s=0}^d s!}
=2^{d(d+1)/2}\ne0.
$$

For large $R$, define a real change of basis by

$$
\beta_{mr}(T)=\frac{T^{r-\nu_m}}{a_m}
[\mathsf J(T)^{-1}]_{mr},\qquad
G_{r,R}=\sum_{m=0}^d\beta_{mr}(T)g_m,
\qquad 0\le r\le d.
$$

Its first-term polynomial $q_{r,T}=\sum_m\beta_{mr}p_m$ has exact jets

$$
\frac{q_{r,T}^{(s)}(T)}{s!}=\mathbf1_{\{s=r\}}\quad(0\le s\le d),
\qquad
|\beta_{mr}(T)|\le C_dT^{r-\nu_m}.
\tag{T11}
$$

The higher jets obey $q_{r,T}^{(s)}(T)/s!=O_d(T^{r-s})$ for $d<s\le2d+5$. Consequently its exact Taylor polynomial is

$$
q_{r,T}(X)=(X-T)^r
+\sum_{s=d+1}^{2d+5}O_d(T^{r-s})(X-T)^s.
$$

This change of basis is invertible and depends on the same endpoint as the tests. It explicitly retains combinations that cancel the common leading tail; it does not assume the raw derivative Gram is uniformly conditioned.

### A stable common profile Gram

Put $B_R=e^{R/2}e^{-\pi T}$ and define the positive-tail error profiles

$$
F_{r,R}(s)=\eta(s)G_{r,R}(R+\delta s)/B_R,
\qquad
F_r(s)=\eta(s)(2s)^re^{-2\pi s},
$$

zero for $s\le0$. The first theta term is exactly

$$
\eta(s)e^{\delta s/2}
q_{r,T}(Te^{2\delta s})
e^{-\pi T(e^{2\delta s}-1)}.
$$

Here $Te^{2\delta s}-T\to2s$ on bounded $s$. Equations (T10)–(T11) give $q_{r,T}(Te^{2\delta s})\to(2s)^r$. For a uniform majorant use
$T(e^{2\delta s}-1)\ge2s$ and $T(e^{2\delta s}-1)\le2s e^{2\delta s}$. The finite polynomial degree, the higher-jet bounds and two scaled derivatives are absorbed by the exponential. For the remaining theta terms $n\ge2$, the coefficients in (T11) and the normally convergent differentiated series give a bound
$C_d T^d e^{-3\pi T}e^{-cs}$, also through two scaled derivatives. Thus

$$
F_{r,R}\longrightarrow F_r\quad\text{in }L^1\cap H^2,
\qquad |F_{r,R}^{(l)}(s)|\le C_d e^{-cs}\quad(0\le l\le2),
\tag{T12}
$$

uniformly in large $R$, with $c>0$ fixed. These are applications of the original series and the new finite jet coordinates; no differentiated asymptotic remainder is used.

The limiting Gram is

$$
\mathsf K_d(r,t)=\int_0^\infty
\eta(s)^2(2s)^{r+t}e^{-4\pi s}ds.
$$

It is positive definite: a nonzero polynomial cannot vanish almost everywhere on $s\ge1$, where $\eta=1$. Strong convergence in (T12) makes the finite Gram converge in operator norm. Hence there are constants $0<c_d<C_d$ and a sufficiently large $R_d$ such that for every $\mathbf a\in\mathbb C^{d+1}$ and $R\ge R_d$,

$$
c_d|\mathbf a|^2\le
\left\|\sum_{r=0}^d a_rF_{r,R}\right\|_2^2
\le C_d|\mathbf a|^2.
$$

Writing $F_{\mathbf a,R}=\sum_r a_rF_{r,R}$, the pointwise bounds, first two derivative norms and $L^1$ norm are also at most $C_d|\mathbf a|$. In particular they are controlled by $C_d\|F_{\mathbf a,R}\|_2$. This is uniform over coefficients depending on $R$; separate convergence of fixed derivative vectors would not provide it.

Let

$$
g_{\mathbf a,R}=\sum_r a_rG_{r,R},\qquad
u_{\mathbf a,R}=\chi_jg_{\mathbf a,R},\qquad
e_{\mathbf a,R}=g_{\mathbf a,R}-u_{\mathbf a,R}.
$$

Odd reflection gives the exact mass and its two-sided coefficient comparison

$$
M_{\mathbf a,R}:=\|e_{\mathbf a,R}\|_2^2
=2B_R^2\delta\|F_{\mathbf a,R}\|_2^2
\asymp_d B_R^2\delta|\mathbf a|^2.
\tag{T13}
$$

### Joint complete energy and response bounds

For fixed $j,d,\mathbf a$, the compact outer-cutoff passage in (T4)–(T5) applies to this finite linear combination of theta derivatives. Each transform and both pole moments vanish for the uncut combination. Therefore its compact old energy equals the complete tail energy, and its mixed collar pairing is the negative tail pairing. The full paired zero multiset, every prime power and true pole are unchanged.

All estimates in (T6)–(T7) depend on a scaled profile only through its norm, the first two derivative budgets and an exponential envelope. Equations (T12)–(T13) provide those budgets uniformly in $\mathbf a$, relative to its actual tail mass. In the energy calculation the Gamma remainder is $C_dM_{\mathbf a,R}$; the reflected Gamma term is $C_de^{-3R}M_{\mathbf a,R}$; same-side prime correlations are exponentially small in $1/\delta$; the full opposite-tail prime correction is $C_dR e^{-R}M_{\mathbf a,R}$; and the actual negative pole is $C_de^{-R}M_{\mathbf a,R}$. The discrete endpoint term in the prime sum is retained. Thus, uniformly for every coefficient vector,

$$
\boxed{
|Q(u_{\mathbf a,R})-2R M_{\mathbf a,R}|
\le C_d M_{\mathbf a,R}.
}
\tag{T14}
$$

The same estimate holds for the true pole-free core. It pays all cross terms in the complete old Gram, and makes it positive definite for sufficiently large $j$.

For the collar row use the same two source thresholds $e^{y-R}$ and $e^{y+R}$ as (T7), with both translation orientations and their infinite tail. Replace the profile amplitude there by $B_R|\mathbf a|$, justified by (T12); the singular Gamma neighborhood and local multiplier are paid by the uniform second-derivative tail. The true pole moment is at most $C_dB_R|\mathbf a|\delta e^{R/2}$. With $Y_j^Q(u)$ denoting the full physical $L^2(E_j)$ response,

$$
\boxed{
\|Y_j^Q(u_{\mathbf a,R})\|_2^2
\le C_d h_jB_R^2|\mathbf a|^2R^2e^{-R}
\le C_d h_jR^2e^{-R}\delta^{-1}M_{\mathbf a,R}.
}
\tag{T15}
$$

This is uniform over all old coefficients and all odd collar coefficients. The core response has the same bound after its actual pole-removal term. Neither weighted even commutators nor an independently optimized component budget is substituted for this physical row.

### The actual restricted inverse is paid jointly

Equations (T13)–(T15), $h_j\asymp e^{-4R_j}$ and $\delta_j=e^{-2R_j}$ give, for each fixed $d\ge1$ and all sufficiently large $j$,

$$
\boxed{
\sup_{0\ne u\in U_{j,d}}
\frac{|B_Q(u,v)|^2}{Q(u)}
\le C_d R_j e^{-3R_j}\|v\|_2^2
\le C_d(\log k_j)k_j^{-3/4}\|v\|_2^2.
}
\tag{T16}
$$

It holds for every odd $L^2$ collar $v$ by the complete response representation. In any basis $u_r$ of this actual compact old space, put
$\mathsf G_{rt}=B_Q(u_t,u_r)$ and $b_r(v)=\overline{B_Q(u_r,v)}$. Then $\mathsf G\succ0$ and the standard finite-dimensional variational identity identifies the left side with $b(v)^*\mathsf G^{-1}b(v)$. Consequently (T16) is a bound for the complete restricted inverse, including its smallest-energy combinations, rather than the sum of $d+1$ rank-one bounds. It also holds with the true pole-free form in both Gram and forcing.

The quantifiers are $\forall d\ \exists C_d,j_d\ \forall j\ge j_d$: no degree-uniform constant, growing-degree rate or certified numerical starting endpoint is supplied. The actual full old inverse can have additional directions outside $U_{j,d}$, and its interaction with their complement remains unpaid. Source-operator application still requires the full common-core and physical norm identification. The original selected-integer signed Robin estimate and RH remain unproved.

The added interface is the coefficient-uniform complete physical Gram/forcing bound (T13)–(T16), made possible by the endpoint-dependent tail-jet construction (T10)–(T12). The individual cutoff estimate, theta nullity and tails, kernel scaling and classical interpolation/Gram identities are reused. This is a paper-level joint estimate, without Lean certification or a mathematical-priority claim.

## Quantified degree growth in the physical inverse budget

The fixed-$d$ statement (T16) does not control a prescribed degree growing with the endpoint. A qualitative choice of an unspecified slow sequence would not pay this parameter gap. Here the original polynomial construction is used to bound its constants and thresholds together, on the same actual collars and in the same physical odd metric.

Retain the fixed smooth transition $\eta$, the actual endpoints and all objects from (T9)–(T16). The [original theta series](../Analytic/romik2021orthogonal.md), derivative nullity and compact-domain passage from [the derivative-family account](lagarias2004li.md#the-full-derivative-family-and-the-remaining-estimate), Gamma scaling and complete prime/pole estimates remain suppliers. Classical interpolation, adjugate bounds and elementary factorial estimates below are intermediate tools; no separate new polynomial theorem is asserted.

### One budget for the degree-sensitive construction

Put $N=d+1$, $D=2d+5$ and retain $T=e^{2R}$, $\delta=T^{-1}$. There is a constant $C_0\ge1$, depending on the fixed transition and normalization but not on $d$ or $R$, such that with

$$
K_d=\exp(C_0N^2),\qquad H_d=K_d^{10},
\tag{T17}
$$

the following construction estimates hold whenever $R\ge H_d$. The exponential budget is derived as follows, rather than substituted for the unspecified constants in (T16).

For the coefficient $\ell^1$ norm of a polynomial of degree at most $D$, the original operator satisfies

$$
\|\mathcal D p\|_{\rm coeff,1}
\le(1/2+2D+2\pi)\|p\|_{\rm coeff,1}.
$$

At every stage constructing $p_m$, its degree is at most $D$. Applying this inequality at most $2d+3$ times gives
$\max_m\|p_m/a_m\|_{\rm coeff,1}\le\exp(O(N\log(N+1)))$, with a constant independent of $d$. The entries of $V=[\binom{\nu_m}{s}]$ are at most $2^D$ and its determinant is at least one by (T10). The adjugate formula therefore gives

$$
\|V^{-1}\|_2\le N\,d!\,(2^D)^d\le\exp(O(N^2)).
$$

The lower polynomial coefficients similarly pay
$\|\mathsf J(T)-V\|_2\le\exp(O(N\log(N+1)))/T$.
The ordinary inverse perturbation estimate, at the stated $R\ge H_d$, bounds $\mathsf J(T)^{-1}$ by $\exp(O(N^2))$. The coefficients $\beta_{mr}$ and higher Taylor coefficients in (T11) consequently have the same budget, after the displayed powers $T^{r-\nu_m}$ and $T^{r-s}$ are factored out. All the constants implicit in these bounds are independent of the degree. Enlarging one $C_0$ absorbs their finite products.

The first-term profile error can also be quantified. For $s\ge0$,

$$
0\le T(e^{2s/T}-1)-2s\le\frac{2s^2}{T}e^{2s/T}.
$$

Use this in the exact Taylor formula following (T11). For the exponential factor, $|e^{-a}-e^{-b}|\le(a-b)e^{-b}$ when $a\ge b\ge0$; its first two derivatives use the same $T^{-1}$ remainder and finite polynomial factors. The higher jets have $T^{r-s}\le T^{-1}$ for $r\le d<s$. Thus, through two scaled derivatives, the errors are bounded by $T^{-1}\exp(O(N^2))$ times a polynomial of degree at most $D+6$ and a fixed decreasing exponential. The bound
$\sup_{s\ge0}(1+s)^{D+6}e^{-c s}\le\exp(O(N\log(N+1)))$
and the corresponding integrals pay that polynomial.

For every remaining theta term, its polynomial coefficients contain only powers $n^{O(N)}$ and the same degree-$D$ recurrence. After the jet change its profile contribution is bounded by
$\exp(O(N^2))T^d e^{-3\pi T}e^{-cs}$ through two scaled derivatives. The elementary Gaussian moment bound
$\sum_{n\ge2}n^{O(N)}e^{-c(n^2-4)}\le\exp(O(N\log(N+1)))$
pays the series uniformly in degree. For $T\ge N^2$, $T^d e^{-3\pi T}\le e^{-2\pi T}$, so this also lies in the $T^{-1}$ error budget. These estimates differentiate the original series and exact polynomial expressions, not an asymptotic remainder.

After increasing $C_0$ once, for every $0\le r\le d$ and $0\le l\le2$ the construction therefore gives, with a fixed $c>0$,

$$
\begin{gathered}
|F_{r,R}^{(l)}(s)|\le K_de^{-cs}\quad(s\ge0),\\
\|F_{r,R}-F_r\|_{L^1}+\|F_{r,R}-F_r\|_{H^2}
\le K_d/T.
\end{gathered}
\tag{T18}
$$

The threshold $R\ge H_d$ pays every inverse-perturbation and exponential-absorption condition above. No unspecified $R_d$ from the fixed-degree argument is retained as an extra hypothesis.

### A quantitative lower Gram on the same profiles

Let $p(x)=\sum_{r=0}^d a_rx^r$. Partition $[1,2]$ into $N$ cells and, in the first third of each cell, choose $s_m$ with

$$
|p(2s_m)|\le\sqrt{3N}\,\|p(2\cdot)\|_{L^2(1,2)}.
$$

Such a point exists by the integral bound on that subinterval, also for complex $p$. The nodes $x_m=2s_m$ lie in $[2,4]$ and have pairwise separation at least $4|m-n|/(3N)$. In the Lagrange basis, the coefficient $\ell^1$ norm of each numerator is at most $5^d$, while the denominator is at least

$$
\left(\frac4{3N}\right)^d m!(d-m)!.
$$

Using $\binom dm\le2^d$, $d!\ge(d/e)^d$ and $N/d\le2$ gives a coefficient norm at most $(15e)^d$ for each Lagrange polynomial. Consequently

$$
|\mathbf a|\le N\sqrt{3N}(15e)^d
\|p(2\cdot)\|_{L^2(1,2)}.
$$

Since $\eta=1$ on this interval, the actual limiting profile Gram obeys the degree-explicit bound

$$
\boxed{\lambda_{\min}(\mathsf K_d)
\ge\frac{e^{-8\pi}}{3N^3(15e)^{2d}}\ge K_d^{-1}.}
\tag{T19}
$$

Here $C_0$ has been chosen large enough to include the last inequality. The finite profile Gram has error at most $K_d^4/T$ by (T18), Cauchy--Schwarz and $N\le K_d$. For $R\ge K_d^{10}$ this is less than $(2K_d)^{-1}$. Thus, uniformly over every complex coefficient vector,

$$
\|F_{\mathbf a,R}\|_2^2\ge(2K_d)^{-1}|\mathbf a|^2.
$$

The exponential envelope, first two derivative norms and $L^1$ norm of the combination are at most $K_d^2|\mathbf a|$, after absorbing their fixed constants into $C_0$. Relative to the actual combination norm they are at most $K_d^3\|F_{\mathbf a,R}\|_2$. This explicitly pays endpoint-dependent cancellation directions before taking any inverse.

### The complete physical remainder fits the same budget

For each parameter pair $d,R$ and coefficient vector, use the fixed-parameter compact outer-cutoff passage from (T4)–(T5). It applies to the finite derivative combination at that endpoint, irrespective of how $d$ or its coefficients are selected at other endpoints. Every actual zero, paired off-line factor and multiplicity is retained; there is no interchange of an infinite-degree limit with the explicit formula.

Insert the just-proved relative profile budgets into the same Gamma and full prime/pole estimates used in (T14)–(T15). The Gamma scaling remainder and singular small-shift derivative budget are at most a fixed constant times $K_d^6M_{\mathbf a,R}$. Its reflected cross term has the additional $e^{-3R}$ factor. The same-side prime correlations have the additional exponential in $-1/\delta$, the complete opposite-tail prime correction has $R e^{-R}$, and the actual pole square has $e^{-R}$. The prime sums still include their discrete endpoint terms; only $\Lambda(n)\le\log n$ is used. These scalar integrals and sums have constants independent of the degree because the profile exponential rate $c$ is fixed.

For the collar row, both threshold sums at $e^{y-R}$ and $e^{y+R}$, the other translation orientation, the Gamma local and remote pieces and the true pole use the same relative envelope and two-jet budgets. Squaring its bound costs at most $K_d^6$ times the common scalar constant. Choosing $C_0$ to contain those fixed scalar constants makes $H_d=K_d^{10}$ an upper budget for both complete estimates:

$$
\boxed{
\begin{aligned}
|Q(u_{\mathbf a,R})-2R M_{\mathbf a,R}|
&\le H_dM_{\mathbf a,R},\\
\|Y_j^Q(u_{\mathbf a,R})\|_2^2
&\le H_dh_jR^2e^{-R}\delta^{-1}M_{\mathbf a,R}.
\end{aligned}
}
\tag{T20}
$$

Both inequalities hold for all $d\ge1$, every complex coefficient vector and each actual endpoint with $R_j\ge H_d$. The true pole-free form satisfies the same estimates. In particular
$Q(u)\ge R_jM_{\mathbf a,R}>0$ for $u\ne0$ in that subspace. The error budget is compared to the main term before division; it is not an upper denominator used as a lower one.

### A paid increasing number of old directions

Put $C=10C_0$ and, for sufficiently large actual endpoints, choose

$$
d_j+1=\left\lfloor\sqrt{\frac{\log R_j}{4C}}\right\rfloor.
\tag{T21}
$$

Then $d_j\ge1$ eventually, $d_j\to\infty$ and
$H_{d_j}=\exp(C(d_j+1)^2)\le R_j^{1/4}\le R_j$.
All thresholds and both estimates in (T20) are therefore paid by this same choice. Since
$h_j=\tfrac12\log(1+e^{-4R_j})\le\tfrac12e^{-4R_j}$, the complete restricted variational debit obeys

$$
\boxed{
\sup_{0\ne u\in U_{j,d_j}}
\frac{|B_Q(u,v)|^2}{Q(u)}
\le\tfrac12 R_j^{5/4}e^{-3R_j}\|v\|_2^2
=O\bigl((\log k_j)^{5/4}k_j^{-3/4}\bigr)\|v\|_2^2.
}
\tag{T22}
$$

This holds for every odd $L^2$ collar $v$, with the same core version. The actual space dimension is $d_j+1\asymp\sqrt{\log\log k_j}$, and all its endpoint-dependent complex combinations are covered. The constants in the chosen schedule and its numerical starting endpoint are not certified numbers. The quantitative degree rate and vanishing debit follow from the paid exponential construction budget, not from a qualitative diagonalization of (T16).

An increasing derivative space does not by itself identify or estimate the complete old complement, nor prove approximation in the original energy norm. The full old-space inverse and the source's common-core/norm map remain separate obligations. The original selected-integer signed Robin main estimate, its coefficients and strict core are unchanged; RH remains unproved.

The added interface is the simultaneous degree/threshold control (T17)–(T20) consumed by the growing-space physical inverse bound (T21)–(T22). The fixed-degree estimate, theta representations and nullity, interpolation and Gamma/prime/pole mechanisms are reused. This is paper-level work without Lean certification or a mathematical-priority claim.

## Move the theta cutoff toward the actual old endpoint

The growing spaces in (T21) still use a cutoff at half of the actual old radius. Increasing their degree does not include the outer half of that radius. The following pays a different physical collar row when the theta cutoff and the arithmetic endpoint are independent. It keeps the same integers and collars, and permits a cutoff whose ratio to the old radius tends to one. This is a spatial extension of the specified derivative family, not a density or full-old-space assertion.

Retain the actual $k_j$, $a_j=\tfrac12\log k_j$, $h_j=\tfrac12\log(1+e^{-2a_j})$ and reflected collar $E_j$ from (O10). Suppress $j$ and write $a=a_j$, $h=h_j$. Choose

$$
\frac a2\le r\le a-1,\qquad g=a-r,\qquad
\delta=e^{-2r},\qquad B_r=e^{r/2}e^{-\pi e^{2r}},
\qquad r\ge H_d.
\tag{T23}
$$

Here $g$ is the physical gap, and is unrelated to the previously named null function $g_0$. Use the same transition $\eta$, derivative family $g_m$, and jet basis at the new cutoff $r$. Define

$$
\chi_r(y)=1-\eta((|y|-r)/\delta),\qquad
U_{j,d}^{(r)}=\operatorname{span}_{\mathbb C}\{\chi_rg_m:0\le m\le d\}.
$$

Its tests are compact inside the same old interval $(-a,a)$ since $r+\delta<a$. Coefficients remain unrestricted and may depend on both parameters.

### Reuse the tail coordinates and complete energy

The construction in (T17)–(T19) depends on the theta cutoff alone; neither the arithmetic endpoint nor the collar occurs in its polynomial, profile or Gram calculation. Apply it at $r$. For a coefficient vector $\mathbf c$ in that jet basis, write $g_{\mathbf c,r}$ for its uncut null function, $u=\chi_rg_{\mathbf c,r}$ and $e=g_{\mathbf c,r}-u$. With $F=F_{\mathbf c,r}$ and $P=\|F\|_2$, the reused budgets give

$$
M:=\|e\|_2^2=2B_r^2\delta P^2,\qquad
|F^{(\ell)}(s)|\le K_d^3P e^{-cs}\quad(0\le\ell\le2),
\qquad \|F\|_1\le K_d^3P,
\tag{T24}
$$

for a fixed $c>0$ independent of $d,r,a$. The lower Gram ensures $P>0$ for nonzero coefficients. The fixed-parameter compact outer-cutoff passage and mixed nullity remain (T4): all actual zero real parts, both signs, heights and multiplicities are unchanged.

The complete tail-energy proof in (T20) also contains no collar parameter. Its Gamma scale is $\log(1/\delta)=2r$, the two tails are separated by $2r$, and its full opposite-tail prime threshold is $e^{2r}$. Thus the existing proof directly supplies

$$
|Q(u)-2rM|\le H_dM,\qquad Q(u)\ge rM>0
\quad(u\ne0).
\tag{T25}
$$

The true pole-free core satisfies the same bounds. Choose the admissible $C_0$ in (T17) large enough once to absorb the additional fixed scalar constants below; $K_d=e^{C_0(d+1)^2}$ and $H_d=K_d^{10}$ still pay all earlier construction conditions. No new unquantified degree-dependent threshold is introduced.

### Pay the new physical row, including its discrete endpoints

On the positive collar $a<y<a+h$, put $T_-=e^{y-r}$ and $T_+=e^{y+r}$. The same complete prime-row comparison used in (T7), now at these two distinct thresholds, gives

$$
\begin{aligned}
\sum_{2\le n\le T_-}\frac{\Lambda(n)}{\sqrt n}|e(y-\log n)|
&\le C B_rK_d^3P\log T_-
 (T_-^{-1/2}+\delta T_-^{1/2}),\\
\sum_{n\ge T_+}\frac{\Lambda(n)}{\sqrt n}|e(y-\log n)|
&\le C B_rK_d^3P\log T_+
 (T_+^{-1/2}+\delta T_+^{1/2}).
\end{aligned}
\tag{T26}
$$

Indeed, (T24) bounds the two tails by $(n/T_-)^{c/\delta}$ and $(n/T_+)^{-c/\delta}$ respectively. Elementary increasing/decreasing integral comparison and $\Lambda(n)\le\log n$ supply the displayed estimates, including their first discrete endpoint terms. There is no contribution from $T_-<n<T_+$ because that argument lies in $(-r,r)$, where $e=0$. The noncompact tail sum is not stopped at $k_j$.

The other orientation $e(y+\log n)$ is bounded by
$B_rK_d^3P e^{-cg/\delta}n^{-c/\delta}$; its entire weighted sum is smaller than $CB_rK_d^3P e^{-g/2}$ for the paid small $\delta$. Since $h\le1$, $r\ge a/2$ and $g\ge1$, the logarithms in (T26) are at most $Ca$. Moreover

$$
T_-^{-1/2}\asymp e^{-g/2},\qquad
\delta T_+^{1/2}\asymp e^{(a-3r)/2},
$$

while $\delta T_-^{1/2}$ and $T_+^{-1/2}$ are bounded by these two budgets. The complete prime row is therefore at most
$CB_rK_d^3Pa(e^{-g/2}+e^{(a-3r)/2})$.

The complete Gamma row retains its local multiplier and symmetric difference integral. Split its shifts at $g/2$. For the smaller shifts, $y\pm t\ge r+g/2$ and (T24) gives

$$
|e''(y\pm t)|\le B_rK_d^3P\delta^{-2}e^{-cg/(2\delta)}.
$$

The fixed scalar integral $\int_0^\infty t^2\kappa(t)dt<\infty$ pays the local singularity. Uniformly for $g\ge1$ and the paid small $\delta$,
$\delta^{-2}e^{-cg/(2\delta)}\le C\delta e^{-g/2}$. The local multiplier has a smaller bound. For shifts at least $g/2$, use $\kappa(t)\le Ce^{-t/2}$ and the two tail envelopes. Changing to their scaled coordinates bounds the near-$r$ tail by $CB_rK_d^3P\delta e^{-(y-r)/2}$ and the reflected tail by $CB_rK_d^3P\delta e^{-(y+r)/2}$. The remaining untranslated and far positive-tail terms are smaller. This gives a full Gamma-row bound $CB_rK_d^3P\delta e^{-g/2}$; no nonsingular separated-kernel formula is substituted for the local part.

Finally, the actual odd pole satisfies

$$
\left|\int e(x)\sinh(x/2)dx\right|
\le CB_rK_d^3P\delta e^{r/2}.
$$

Multiplication by the true collar factor $2\sinh(y/2)$ therefore bounds its row by $CB_rK_d^3P e^{(a-3r)/2}$. Odd reflection supplies the negative collar. These estimates include every prime power and both translation orientations, and the actual pole coefficient. The fixed-parameter mixed identity identifies the compact test's physical row with the negative tail row. Squaring the complete row, integrating over both collars and absorbing only fixed constants in the same $H_d$ yields

$$
\boxed{\|Y_j^Q(u)\|_{L^2(E_j)}^2
\le H_dh a^2\delta^{-1}M
\bigl(e^{-(a-r)}+e^{a-3r}\bigr).}
\tag{T27}
$$

The true pole-free core has the same estimate after its actual pole-removal term. This bound is uniform over every old coefficient vector at the specified $d,r,a$; the profile-to-mass comparison pays cancellations before the square is taken.

### A vanishing debit with a cutoff approaching the old radius

Divide (T27) by the independently proved lower energy (T25), and use the exact width inequality $h\le\tfrac12e^{-2a}$. For every odd physical $L^2$ collar $v$,

$$
\boxed{
\sup_{0\ne u\in U_{j,d}^{(r)}}
\frac{|B_Q(u,v)|^2}{Q(u)}
\le\frac{H_da^2}{2r}
\bigl(e^{-3(a-r)}+e^{-(a+r)}\bigr)\|v\|_2^2.
}
\tag{T28}
$$

This is the complete restricted inverse, not a sum over individual derivative lines. The same core version holds. At the earlier midpoint it has the same exponential order as (T22); changing the cutoff changes both threshold contributions, so the midpoint collar estimate cannot simply be reused with $r$ substituted for $a/2$.

At sufficiently large actual endpoints choose

$$
r_j=a_j-\log a_j,\qquad
d_j+1=\left\lfloor\sqrt{\frac{\log r_j}{4C}}\right\rfloor,
\qquad C=10C_0.
\tag{T29}
$$

Then $a_j/2\le r_j\le a_j-1$, $H_{d_j}\le r_j^{1/4}\le r_j$, and all conditions are paid. Equation (T28) becomes

$$
\boxed{
\sup_{0\ne u\in U_{j,d_j}^{(r_j)}}
\frac{|B_Q(u,v)|^2}{Q(u)}
\le C_1a_j^{-7/4}\|v\|_2^2
=O\bigl((\log k_j)^{-7/4}\bigr)\|v\|_2^2.
}
\tag{T30}
$$

Here $C_1$ is fixed, and the schedule's constant and numerical start are not certified numbers. Indeed, $a_j^2/r_j\le2a_j$, $e^{-3(a_j-r_j)}=a_j^{-3}$ and the other exponential is smaller. The actual dimension remains $d_j+1\asymp\sqrt{\log\log k_j}$. The new tests agree with their uncut null functions on $[-r_j,r_j]$ and have support inside $[-r_j-\delta_j,r_j+\delta_j]\Subset(-a_j,a_j)$, with $r_j/a_j\to1$.

The weaker decay in (T30) pays a different, larger spatial reach than the midpoint family. It does not establish that this finite derivative family approximates arbitrary old tests, even in the newly reached interior. The full complementary directions, their cross terms and the energy-norm approximation cost remain unestimated; they cannot be described as only a logarithmic boundary layer. The source common-core/physical-norm map and original selected-integer signed Robin estimate also remain unproved, and no RH conclusion follows.

The additional interface is the independent-cutoff, same-collar response estimate (T26)–(T28), consumed by the spatial schedule (T29)–(T30). Tail coordinates, degree thresholds, complete energy, mixed nullity and elementary prime comparisons are reused suppliers. This is paper-level work without Lean certification or a mathematical-priority claim.

## Pay the actual cross Gram of both cutoff families

The midpoint and near-endpoint estimates cannot be added on their joint span without a lower bound for its whole Gram. They are different cutoff families, even though their uncut functions belong to the same null derivative family. The following estimates their actual mixed energy and then combines the already paid forcing bounds.

Retain the same actual $k_j,a_j,h_j,E_j$, complete physical odd form $Q$ and true pole-free core. Suppress $j$ and take, for sufficiently large actual $a=a_j$,

$$
r_0=a/2,\qquad r_1=a-\log a,\qquad
\Delta=r_1-r_0,\qquad \Sigma=r_1+r_0,\qquad
\delta_i=e^{-2r_i}.
$$

Use both accepted degree schedules, without replacing either family by a single line:

$$
d_i+1=\left\lfloor\sqrt{\frac{\log r_i}{4C}}\right\rfloor,
\qquad H_{d_i}\le r_i^{1/4},\qquad C=10C_0.
\tag{T31}
$$

The corresponding actual spaces are $U_i=U_{j,d_i}^{(r_i)}$. For $u_i\in U_i$, write its uncut null function as $g_i$, its error as $e_i=g_i-u_i$, and its profile as $F_i$. This $g_i$ is a finite derivative combination, not a new source function. Reuse (T24)–(T25): with $P_i=\|F_i\|_2$, $B_i=e^{r_i/2}e^{-\pi e^{2r_i}}$ and $M_i=\|e_i\|_2^2$,

$$
M_i=2B_i^2\delta_iP_i^2,\qquad
Q(u_i)\ge r_iM_i,\qquad
|F_i^{(\ell)}(s)|\le K_{d_i}^3P_i e^{-cs}
\quad(0\le\ell\le2).
$$

Put $W=K_{d_0}^3K_{d_1}^3$. The existing degree budget gives
$W\le(r_0r_1)^{3/40}\le a^{3/20}$. All constants below are independent of the degree, endpoint and complex coefficient vectors. At each fixed parameter pair the mixed nullity and compact outer-cutoff bridge give the exact equality
$B_Q(u_0,u_1)=B_Q^{\rm tail}(e_0,e_1)$, with the actual zero pairing, heights and multiplicities unchanged. The same core equality retains its true pole correction.

### Unequal-width correlations retain both prime-shift centers

Write the positive tails as
$f_i(y)=B_iF_i((y-r_i)/\delta_i)$, extended by zero below $r_i$; oddness gives $e_i(y)=f_i(y)-f_i(-y)$. Eventually $\delta_1\le\delta_0/2$. The profile envelopes then bound the complete two-orientation correlation by

$$
\begin{aligned}
&|\langle e_0,\tau_t e_1\rangle|
+|\langle e_1,\tau_t e_0\rangle|\\
&\quad\le C B_0B_1WP_0P_1\delta_1
\left(e^{-c|t-\Delta|/\delta_0}
+\mathbf1_{\{t\ge\Sigma\}}e^{-c(t-\Sigma)/\delta_0}\right),
\qquad t\ge0.
\end{aligned}
\tag{T32}
$$

For like-sign tails the two possible centers are $\Delta$ and $-\Delta$. Integrating the narrower profile gives the factor $\delta_1$; the term centered at $-\Delta$ is bounded by the displayed one. For opposite signs the convolution is zero below $\Sigma$. Above it, putting $w=t-\Sigma$ gives the explicit envelope integral

$$
\int_0^w e^{-cx/\delta_0}e^{-c(w-x)/\delta_1}dx
\le\frac{2\delta_1}{c}e^{-cw/\delta_0}.
$$

Thus (T32) covers all reflected pairs and both translations for complex profiles, without a phase or sign assumption.

The elementary threshold comparison in (T26), applied on both sides of $e^b$, supplies for $b\ge1$ and the paid small $\delta_0$

$$
\sum_{n\ge2}\frac{\log n}{\sqrt n}
e^{-c|\log n-b|/\delta_0}
\le C(1+b)(e^{-b/2}+\delta_0e^{b/2}).
$$

The first term retains the discrete endpoint, including when the local expected count is below one. Apply this at $b=\Delta$ and $b=\Sigma$, use $\Lambda(n)\le\log n$, and normalize by the actual masses. The complete prime part of the mixed energy satisfies

$$
\boxed{
\frac{|B_{\rm prime}(e_0,e_1)|}{\sqrt{M_0M_1}}
\le CWa\left(
e^{-3\Delta/2}+\delta_0e^{-\Delta/2}
+e^{-\Delta-\Sigma/2}+e^{-\Sigma/2}\right).
}
\tag{T33}
$$

This notation denotes the prime part of the full polarized tail expression; if one mass is zero the equivalent multiplicative inequality is used. No prime power, endpoint or translation orientation is omitted. In particular the discrete shift near $e^\Delta$, rather than the direct tail overlap, supplies the first term in (T33).

### The singular Gamma part and true pole also fit

The direct overlap is exponentially small in $\Delta/\delta_0$, but this alone does not bound the Gamma energy. For its symmetric increment pairing split the shifts at $\Delta/2$. Below that point, expressing both increments as integrals of their first derivatives gives

$$
|\langle e_0-\tau_te_0,e_1-\tau_te_1\rangle|
\le C B_0B_1WP_0P_1\delta_0^{-1}
t^2 e^{-c\Delta/(2\delta_0)}.
$$

Indeed, wherever a translated $e_1'$ is nonzero, the argument of the corresponding $e_0'$ has absolute value at least $r_0+\Delta/2$. Its supremum is at most
$B_0K_{d_0}^3P_0\delta_0^{-1}e^{-c\Delta/(2\delta_0)}$, while the full $L^1$ norm of $e_1'$ is at most $CB_1K_{d_1}^3P_1$. The finite scalar integral $\int t^2\kappa(t)dt$ therefore pays the small-shift singularity. No divergent total jump rate is separated out.

For shifts at least $\Delta/2$, use (T32) and $\kappa(t)\le Ce^{-t/2}$. Its translated terms integrate to at most
$CB_0B_1WP_0P_1\delta_0\delta_1(e^{-\Delta/2}+e^{-\Sigma/2})$. The untranslated overlap and actual $c_\Gamma$ multiplier fit the small-overlap budget. Consequently the complete Gamma pairing obeys

$$
\begin{aligned}
\frac{|B_\Gamma(e_0,e_1)|}{\sqrt{M_0M_1}}
\le CW\bigl[&e^{3r_0+r_1}e^{-c\Delta/(2\delta_0)}\\
&+\sqrt{\delta_0\delta_1}
(e^{-\Delta/2}+e^{-\Sigma/2})\bigr].
\end{aligned}
\tag{T34}
$$

The actual pole moments, from the same error profiles, satisfy
$|\int e_i(y)\sinh(y/2)dy|\le CB_iK_{d_i}^3P_i\delta_i e^{r_i/2}$.
Their polarized term, with true coefficient $2$, is therefore at most
$CW e^{-\Sigma/2}\sqrt{M_0M_1}$. The pole-free core removes precisely this actual term and has the same mixed upper budget.

### A coefficient-uniform mixed Gram lower bound

For the actual choices in (T31), $\Delta=a/2-\log a$ and $\Sigma=3a/2-\log a$. The first term in (T34) is at most $e^{-a}$ once $a$ exceeds a fixed threshold independent of the degree: use $\Delta\ge a/4$, $\delta_0=e^{-a}$ and exponential domination. All other Gamma and pole terms, and every term in (T33), can be compared explicitly with
$a^{3/2}e^{-3a/4}$ after division by $\sqrt{r_0r_1}\ge a/2$. For example the discrete difference-shift term is
$e^{-3\Delta/2}=a^{3/2}e^{-3a/4}$, whereas the opposite-shift integral term is
$e^{-\Sigma/2}=a^{1/2}e^{-3a/4}$.

Together with $W\le a^{3/20}$, this gives a fixed $C_*>0$ such that, for all sufficiently large actual endpoints and every coefficient pair,

$$
\boxed{
|B_Q(u_0,u_1)|
\le\varepsilon_a\sqrt{r_0M_0\,r_1M_1},\qquad
\varepsilon_a=C_*a^2e^{-3a/4}\longrightarrow0.
}
\tag{T35}
$$

The same estimate holds for the true pole-free core. The remaining starting threshold is fixed by scalar constants and $c$, independently of the degrees; no unspecified $d$-dependent threshold is imported. Its numerical value and $C_*$ are not certified numbers.

Choose a sufficiently large endpoint with $\varepsilon_a<1/2$. Write $Q_i=Q(u_i)$. The existing lower energies imply
$\sqrt{r_0M_0r_1M_1}\le\sqrt{Q_0Q_1}$. Therefore the actual full joint Gram satisfies

$$
\boxed{
Q(u_0+u_1)\ge(1-\varepsilon_a)(Q_0+Q_1)
\ge\tfrac12(r_0M_0+r_1M_1).
}
\tag{T36}
$$

This proves positivity on the whole joint space without assuming positivity on an arbitrary old complement. It also makes the two spaces a direct sum: a zero $u_0+u_1$ forces both actual masses, and hence both coefficient vectors, to vanish. Its dimension is $(d_0+1)+(d_1+1)\asymp\sqrt{\log\log k_j}$. The separate spaces alone would not establish (T36).

### The complete joint inverse is now paid

Let $D_0(a)$ and $D_1(a)$ be the already proved uniform upper allowances in (T22) and (T30) for these two actual spaces; thus
$D_0(a)=O(a^{5/4}e^{-3a/2})$ and $D_1(a)=O(a^{-7/4})$.
For the same physical odd collar $v$ and any $u_i\in U_i$, those bounds give
$|B_Q(u_i,v)|\le\sqrt{D_i(a)}\|v\|_2\sqrt{Q_i}$.
Ordinary two-coordinate Cauchy--Schwarz, now consumed with the actual joint denominator (T36), gives

$$
\boxed{
\sup_{0\ne u\in U_0\oplus U_1}
\frac{|B_Q(u,v)|^2}{Q(u)}
\le\frac{D_0(a)+D_1(a)}{1-\varepsilon_a}\|v\|_2^2
=O(a^{-7/4})\|v\|_2^2.
}
\tag{T37}
$$

The same statement holds with the true pole-free form in both Gram and forcing. The existing finite variational identity identifies this quotient with the whole joint Gram inverse, including coefficients depending on the endpoint and near-cancelling directions across the two cutoffs. The sum in (T37) is justified by the new cross-Gram estimate; it is not obtained by assuming independent optimizers or adding rank-one inverses.

The added interface is the complete unequal-cutoff mixed estimate (T32)–(T35), consumed by joint positivity and inverse control in (T36)–(T37). Tail coordinates, degree and single-space energy/forcing budgets, mixed nullity/domain passage, Gamma kernel estimates, prime threshold comparisons and finite Gram algebra are reused suppliers. The full old complement and its interaction with this joint family, energy-norm approximation cost, source common-core/physical-norm map and original selected-integer signed Robin estimate remain unpaid. This paper-level joint estimate has no Lean certification, full-old-space or RH conclusion, or mathematical-priority claim.

## Pay the complete physical collar forcing on an infinite exterior

The preceding theta spaces leave arbitrary old directions unestimated. Here the old-to-new pairing is bounded on the **whole physical odd $L^2$ space**, and the existing Fourier-exterior floor supplies a denominator on an infinite old subspace. The retained low-frequency Schur block remains separate.

Reuse the complete compact-test row (O10), the classical disjoint-source/squared-weight mechanism in arXiv v3 under “Ambient cross-$n$ structure” and “Fixed-target gauge and simultaneous source shorting”, especially the corollary “Source-resolved transverse Feshbach bound” (`source-resolved-transverse`), the [weighted Schur criterion](../Fourier/teschl2009mathematical.md#schur-criterion-for-the-local-frequency-kernel), classical Chebyshev bounds, and the [existing infinite-exterior allowance (16)](../Fourier/montgomery1978largesieve.md#a-growth-regime-and-its-limitations). The source's positive normalized pre-short metric is not identified with the full physical old metric. The additional interface below is the complete adjacent physical row, including its shared-boundary Gamma singularity, consumed by that independently supplied exterior denominator. No generic Carleman, prime-weight or Fourier-leakage theorem is reproved.

For an integer $k\ge7$ set

$$
a=\tfrac12\log k,\quad b=\tfrac12\log(k+1),\quad
h=b-a\le\frac1{2k},\quad \ell=2a=\log k,
$$

and put $\mathcal H_a=L^2_{\rm odd}(-a,a)$ and
$\mathcal K_k=L^2_{\rm odd}((-b,-a)\cup(a,b))$ with the physical Lebesgue norms. Write $R_k:\mathcal H_a\to\mathcal K_k$ for the cross row in (O10), initially on compact smooth old tests, and $b_k(v)=R_k^*v$ for its old forcing. Thus $B_Q(u,v)=\langle R_ku,v\rangle$; no positivity of the whole old form is assumed. For a collar vector outside the form domain, this pairing denotes the bounded cross-row extension established below.

### Retain the reflected integer source slots

On the positive collar the prime row is
$-\sum_{2\le n\le k}\Lambda(n)n^{-1/2}u(y-\log n)$; the other translation is zero there. Its source slots are

$$
J_n=(a-\log n,b-\log n)\subset(-a,a),\qquad 2\le n\le k.
$$

Distinct $J_n$ are disjoint: consecutive logarithmic gaps exceed $2h$. The reflected slots also remain disjoint from them. Indeed $J_n\cap(-J_m)$ could have positive length only if
$2a<\log(nm)<2b$, or $k<nm<k+1$, which no integer product satisfies. Products $nm=k$ or $k+1$ give only touching endpoints. This verifies the needed reflection interface in the actual thin collar; it does not replace the source metric by a normalized one-cell form.

The two reflected copies and physical odd normalization therefore give, for every complex odd collar vector,

$$
\boxed{
\|R_{k,p}^*v\|_2^2=S_k\|v\|_2^2,
\qquad S_k=\sum_{2\le n\le k}\frac{\Lambda(n)^2}{n}.
}
\tag{T38}
$$

This is the disjoint-source squared-weight mechanism with its physical reflection map checked, not a new principle. The endpoint $n=k$ is retained: its old/new slot has positive length. In contrast, the old self-form has only $n<k$.

Fix a classical Chebyshev constant $B\ge1$ such that
$\Psi(t)=\sum_{n\le t}\Lambda(n)\le Bt$ for $t\ge1$. Directly reuse partial summation and $\Lambda(n)\le\log k$ to obtain

$$
S_k\le B\ell(1+\ell),\qquad
W(k):=\sum_{2\le n<k}\frac{\Lambda(n)}{\sqrt n}\le2B\sqrt k.
\tag{T39}
$$

### Pay the Gamma singularity at the common boundary

Use the isometry $u\mapsto\sqrt2\,u|_{(0,a)}$ and its collar counterpart. The negative odd Gamma row on $(0,a)\times(a,b)$ has absolute kernel

$$
\kappa(y-x)-\kappa(y+x),\qquad
\kappa(t)=\frac{e^{-t/2}}{1-e^{-2t}}.
$$

Both reflected terms have been kept. The kernel $\kappa$ is decreasing, so this difference is nonnegative and bounded above by $\kappa(y-x)$. Put $C_\kappa=(1-e^{-2})^{-1}$. For $0<t\le1$, concavity gives $1-e^{-2t}\ge t(1-e^{-2})$; for $t\ge1$ use $te^{-t/2}\le2/e<1$. Hence $\kappa(t)\le C_\kappa/t$ for all $t>0$.

After $s=y-a$ and $r=a-x$, the dominating kernel is $C_\kappa/(s+r)$ on $(0,h)\times(0,a)$. The classical Carleman bound, equivalently the cited weighted Schur criterion with weight $r^{-1/2}$ and its standard scalar integral, gives

$$
\boxed{\|R_{k,\Gamma}\|=\|R_{k,\Gamma}^*\|
\le\pi C_\kappa.}
\tag{T40}
$$

The bound is independent of $k,h$. The row is not treated as a separated smooth kernel or claimed to have norm $O(\sqrt h)$: its $1/(2(y-x))$ singularity reaches the shared endpoint. Compact-core density gives the bounded $L^2$ cross extension used here, without splitting off a divergent diagonal jump rate.

### Keep the true pole in the same row

Let $s_a=\sinh(y/2)|_{(-a,a)}$ and $t_k=\sinh(y/2)|_{(-b,-a)\cup(a,b)}$. The actual pole row is $-2t_ks_a^*$, and its exact norm is

$$
\begin{aligned}
\|R_{k,\mathrm{pole}}\|
&=2\sqrt{(\sinh a-a)(\sinh b-\sinh a-h)}\\
&\le e^{h/2}\le e^{1/8}.
\end{aligned}
\tag{T41}
$$

For the inequality use $\sinh a-a\le e^a/2$,
$\sinh b-\sinh a-h=\int_a^b(\cosh t-1)dt\le he^b$ and $2he^{2a}\le1$. This retains the true coefficient $2$ and both physical norms. Multiplication terms have no old/new cross part. Combining (T38)–(T41) gives the complete all-old forcing allowance

$$
\boxed{
\|b_k(v)\|_2\le K(k)\|v\|_2,
\qquad
K(k)=\pi C_\kappa+e^{1/8}+\sqrt{B\ell(1+\ell)}
=O(1+\ell).
}
\tag{T42}
$$

The true pole-free core has the same bound with the $e^{1/8}$ term omitted. These statements cover every complex odd $L^2$ collar vector and every old direction, without a theta-family, derivative or positivity restriction. They are $L^2$ forcing bounds, not yet inverse-energy bounds.

### Consume the existing floor on the whole infinite Fourier exterior

Use the same Fourier/Plancherel identification and actual Weil-form domain bridge as in the cited exterior account. Let $P_{>M}$ be the projection in $\mathcal H_a$ onto the Fourier modes $|m|>M$ on the length-$\ell$ old interval. Oddness is preserved. On the closed-form restriction to this infinite exterior, the already supplied lower allowance is

$$
\begin{aligned}
d(k,M)={}&(1-\eta)\left[\log\frac{M}{4\ell}
-\frac{2\ell}{\pi M}\right]+\eta h_0
-2W(k)-4\sinh(\ell/2),\\
\eta={}&\frac4{3\pi^2},\qquad
h_0=-\gamma-\frac\pi2-3\log2-\log\pi.
\end{aligned}
$$

Its conditions include $\pi M/(2\ell)\ge15/4$. Neither the floor nor the restriction's positivity requires RH or positivity of the full old form. The underlying analytic/Fourier/domain identification remains a paper-level bridge; it is not certified merely by citing the existing Lean leakage statement.

Choose

$$
\beta=\frac{4B+4}{1-\eta},\qquad
M=\left\lceil e^{\beta\sqrt k}\right\rceil.
$$

Reuse (T39) and $4\sinh(\ell/2)\le2\sqrt k$. Then

$$
\begin{aligned}
d(k,M)&\ge2\sqrt k
-(1-\eta)\left[\log(4\ell)+\frac{2\ell}{\pi M}\right]
+\eta h_0\\
&\ge\sqrt k>0
\qquad\text{for all sufficiently large integers }k.
\end{aligned}
\tag{T43}
$$

The last step needs only the displayed scalar frequency condition and
$(1-\eta)[\log(4\ell)+2\ell/(\pi M)]-\eta h_0\le\sqrt k$.
No numerical starting endpoint is certified.

Let $A_{k,>M}$ be the operator of this restricted closed form. The standard positive-form variational identity, now with an independently paid denominator, consumes the **same complete forcing** in (T42):

$$
\boxed{
\begin{aligned}
&\sup_{\substack{0\ne u\in D(Q)\\P_{>M}u=u}}
\frac{|B_Q(u,v)|^2}{Q(u)}
=\langle P_{>M}b_k(v),A_{k,>M}^{-1}P_{>M}b_k(v)\rangle\\
&\qquad\le\frac{K(k)^2}{d(k,M)}\|v\|_2^2
\le\frac{K(k)^2}{\sqrt k}\|v\|_2^2
=O\!\left(\frac{(\log k)^2}{\sqrt k}\right)\|v\|_2^2.
\end{aligned}
}
\tag{T44}
$$

The full true pole-free form and its own forcing obey the same estimate, since removing the negative pole only increases the exterior energy and removes its row term. Each quotient uses its corresponding complete form and row. This covers every coefficient combination in the entire infinite exterior; it is not a sum of finite or rank-one inverse budgets.

The added interface is (T38)–(T42) for the complete physical adjacent forcing, consumed by the reused exterior floor in (T43)–(T44). The disjoint-slot principle, classical Carleman/Schur and prime-weight estimates, Fourier leakage, scalar digamma bound and positive-form inverse algebra are reused. The retained space has dimension of order $\exp(\beta\sqrt k)$: this conservative cutoff is not an efficient certification scheme. Its full retained Schur sign and coupling, and a paid relative-energy identification of the joint theta space (T31) with that retained Fourier space, remain unproved. The theta and exterior debit estimates cannot simply be added as a bound on the whole old inverse.

Applying this physical estimate to the preprint's allocated source debit still requires its common-core, norm and full-form transport identification. The original selected-integer signed Robin estimate, its original coefficients, actual zero real parts, both signs, all heights and multiplicities, elementary correction and strict core are unchanged and unproved. This paper-level interface is neither a Lean result nor an RH proof, and carries no mathematical-priority claim.

## Join the theta directions to the entire infinite exterior

The theta debit (T37) and infinite-exterior debit (T44) cannot be added without paying their actual mixed energy. A state-projection approximation is not needed for this particular joint estimate: mixed nullity expresses its forcing through the small original theta error. The following pays that error's complete old response, including its endpoint trace, and consumes it on the whole exterior.

Reuse (T24), (T31)–(T37), the complete tail expression (T5), the [mixed-nullity/domain bridge](lagarias2004li.md#the-full-derivative-family-and-the-remaining-estimate), (T42)–(T44), and the classical $H^1$ Fourier integration-by-parts, trace and Parseval estimates. The weighted even approximation and spectral-projector statements in [the weighted exterior account](lenz2010compactness.md#weighted-fourier-finite-family-interface) have a different physical norm and are not transported here. The additional interface is the complete physical old error response and its mixed bound with the infinite exterior; no generic Fourier approximation or Schur theorem is new.

Keep the same integer $k$, $a=\tfrac12\log k$, $\ell=2a$, both cutoffs $r_i$ and degree schedules from (T31), and the same exterior cutoff
$M=\lceil e^{\beta\sqrt k}\rceil$ from (T43). Put
$U=U_0\oplus U_1$ and $E=P_{>M}\mathcal H_a$. Every $u=u_0+u_1\in U$ retains its actual null functions $g_i$, errors $e_i=g_i-u_i$, profiles and masses from (T24); all complex coefficients may depend on the endpoint. The constants below are independent of these coefficients and degrees. Assume the already stated Fourier/Plancherel and closed physical form-domain bridge when using $E$ and its positive restricted operator $A_E$; it does not imply positivity of the complete old form.

### The actual errors have a paid two-derivative norm

Write $K_i=K_{d_i}$, $\delta_i=e^{-2r_i}$ and $M_i=\|e_i\|_2^2$. From the same two profiles in (T24), for $0\le j\le2$,

$$
\|e_i^{(j)}\|_2\le C K_i^3\delta_i^{-j}\sqrt{M_i},\qquad
|e_i^{(j)}(y)|\le C B_iK_i^3P_i\delta_i^{-j}
e^{-c(|y|-r_i)/\delta_i}\quad(|y|\ge r_i).
\tag{T45}
$$

The errors and their derivatives vanish inside $(-r_i,r_i)$, with no boundary distribution. This is direct parameter reuse, not a new theta estimate. The paid schedule gives $K_i^3\le a^{3/40}$ and $\delta_i^{-1}\le k$.

### The full tail response is bounded in physical old $H^1$

For the fixed actual tail define its arithmetic response on the whole old interval by

$$
\begin{aligned}
Z_i(y)={}&c_\Gamma e_i(y)
+\int_0^\infty\kappa(t)
 [2e_i(y)-e_i(y+t)-e_i(y-t)]dt\\
&-\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
 [e_i(y+\log n)+e_i(y-\log n)]
-2\sinh(y/2)m_i,\\
m_i={}&\int_{\mathbb R} e_i(y)\sinh(y/2)dy,
\qquad -a<y<a.
\end{aligned}
\tag{T46}
$$

Here $c_\Gamma$ and $\kappa$ are exactly (T5). The sum is global: the error is noncompact, so even $n=k$ and all $n>k$ remain present. This row is distinct from the disjoint-support collar row (O10), which has no multiplication term.

The Gamma integral is a convergent $H^1$ Bochner integral. Reuse the translation estimate
$\|e_i-\tau_t e_i\|_{H^1}\le t\|e_i'\|_{H^1}$ and
$\int_0^\infty t\kappa(t)dt<\infty$ to bound it by $C\|e_i\|_{H^2}$. This keeps the local singularity in its increment; no divergent diagonal rate is isolated.

For $2\le n\le k$, restrict translated functions only after taking their full $H^1(\mathbb R)$ norm. The reused Chebyshev allowance $\sum_{n\le k}\Lambda(n)/\sqrt n\le2B\sqrt k$ pays this complete finite part by
$C\sqrt k K_i^3\delta_i^{-1}\sqrt{M_i}$, with both orientations.

For $n>k$ and $|y|\le a$, one has
$|y\pm\log n|-r_i\ge(a-r_i)+\log(n/k)$.
The exact profile envelope in (T45), through the first derivative, therefore bounds the remaining $H^1$ norm by

$$
C\sqrt\ell\,B_iK_i^3P_i\delta_i^{-1}
e^{-c(a-r_i)/\delta_i}
\sum_{n>k}\frac{\log n}{\sqrt n}(n/k)^{-c/\delta_i}.
$$

Once $c/\delta_i\ge2$, the complete discrete sum is at most
$C\sqrt k(1+\ell)$ by integral comparison, including its endpoint term. Divide by $\sqrt{M_i}=\sqrt2 B_iP_i\sqrt{\delta_i}$; this costs at most
$C\sqrt\ell K_i^3\delta_i^{-3/2}\sqrt k(1+\ell)$, independently of the degree. The exponentially smaller factor may be discarded in this conservative upper bound; the prime tail itself is not discarded.

The same envelope gives the true polar moment
$|m_i|\le C B_iK_i^3P_i\delta_i e^{r_i/2}$, while
$\|\sinh(y/2)\|_{H^1(-a,a)}\le Ce^{a/2}$.
Its coefficient-$2$ row is consequently at most
$C K_i^3 e^{(a-r_i)/2}\sqrt{M_i}$. Since $a/2\le r_i<a$, every preceding budget is bounded by a fixed multiple of $k^3\sqrt{M_i}$ at sufficiently large endpoints. Thus the full same tail satisfies

$$
\boxed{\|Z_i\|_{H^1(-a,a)}\le C k^3\sqrt{M_i}.}
\tag{T47}
$$

This is uniform for the complete actual coefficient combination, not only for the basis vectors. It uses no old positivity and no weight change. The pole-free response omits only the displayed true pole and obeys the same bound.

### Mixed nullity exposes a small high-frequency forcing

The existing fixed-parameter outer-cutoff passage applies to every compact smooth old probe, not only a disjoint collar probe: the uncut $g_i$ has zero transform at every actual zero, and its true polar moments vanish. The complete prime/Gamma/pole expression passes by the same original theta-tail and weighted-jet majorants. Hence

$$
B_Q(u,f)=-\langle Z_0+Z_1,f\rangle
\quad(f\in C_c^\infty(-a,a),\ f\text{ odd}).
$$

On the closed physical form realization this also holds for every admitted odd old form vector $f$. Indeed the compact smooth $u$ has its actual operator row in $L^2$; core density and (T47) identify that row with $-Z$, where $Z=Z_0+Z_1$. This is an operator-row extension under the existing form bridge, not an assumption that a zero quadratic value implies mixed nullity.

For this actual $H^1$ row the ordinary Fourier integration-by-parts estimate retains its endpoint jump:

$$
\begin{aligned}
\|P_{>M}Z\|_2^2
&\le C\left[
\frac{\ell|Z(a)-Z(-a)|^2}{M}
+\frac{\ell^2\|Z'\|_2^2}{M^2}\right]\\
&\le\frac{C(1+\ell^2)}{M}\|Z\|_{H^1(-a,a)}^2
\le\frac{Ck^6(1+\ell^2)}{M}(M_0+M_1).
\end{aligned}
\tag{T48}
$$

Traces are not assumed to vanish or match. In the coefficient formula their contribution is
$(-1)^m[Z(a)-Z(-a)]/(i(2\pi m/\ell)\sqrt\ell)$ up to the irrelevant overall sign; the derivative part uses Parseval. This is a normalized application of the classical trace/Fourier estimate, rather than a new Fourier theorem.

At sufficiently large endpoints (T36) gives
$Q(u)\ge a(M_0+M_1)/4$, and (T43) gives
$Q(f)\ge\sqrt k\|f\|_2^2$ on the whole $E$.
Consume these independent denominators in the exact mixed identity. Increasing a fixed $C_*>0$ if needed, put
$\zeta_k=C_*k^4/\sqrt M\to0$. Then for every coefficient combination and every exterior form vector,

$$
\boxed{
|B_Q(u,f)|\le\zeta_k\sqrt{Q(u)Q(f)},\qquad
Q(u+f)\ge(1-\zeta_k)[Q(u)+Q(f)].
}
\tag{T49}
$$

The scalar threshold is independent of the degree; no numerical starting endpoint is certified. The proof has used positivity only on $U$ and $E$, separately supplied by (T36) and (T43). In particular $U\cap E=\{0\}$, so this is a genuine joint positive space with all its near-cancelling coefficient combinations controlled. The true pole-free form has its corresponding row identity and the same estimate.

### Pay the full joint inverse and its retained theta short

Let $D_U(k)=[D_0(a)+D_1(a)]/(1-\varepsilon_a)=O(a^{-7/4})$ from (T37), and $D_E(k)=K(k)^2/d(k,M)=O((\log k)^2/\sqrt k)$ from (T44). The two estimates concern the same collar vector $v$. Now (T49), followed by ordinary two-coordinate Cauchy–Schwarz, gives

$$
\boxed{
\sup_{\substack{0\ne x\in U+E\\x\in D(Q)}}
\frac{|B_Q(x,v)|^2}{Q(x)}
\le\frac{D_U(k)+D_E(k)}{1-\zeta_k}\|v\|_2^2
=O((\log k)^{-7/4})\|v\|_2^2.
}
\tag{T50}
$$

This covers the entire infinite exterior plus both original theta spaces, not a finite collection of exterior modes. Their inverse budgets can be combined because the actual mixed term has now been paid. The standard positive-form variational identity supplies the complete restricted inverse interpretation.

There is also an exact finite retained consumer. The projection
$u\mapsto l=P_{\le M}u$ is injective on $U$ because $U\cap E=0$. Finite odd Fourier polynomials belong to $H^1_0(-a,a)$ and hence the admitted physical form domain, so $l$ and $u-l$ are legitimate form vectors.
For its image define the **actual exterior short**, using the same closed form,
$Q_{\rm short}(l)=\inf_{f\in E\cap D(Q)}Q(l+f)$.
Since $l+E=u+E$, completing the already positive exterior square gives

$$
\boxed{
\begin{aligned}
Q_{\rm short}(P_{\le M}u)
&=Q(u)-\langle P_{>M}Z,A_E^{-1}P_{>M}Z\rangle,\\
(1-\zeta_k^2)Q(u)
&\le Q_{\rm short}(P_{\le M}u)\le Q(u).
\end{aligned}
}
\tag{T51}
$$

Thus the exact high-frequency elimination retains a positive theta image of dimension $(d_0+1)+(d_1+1)$ inside the retained Fourier space. This pays its shorted metric without assuming raw Fourier projection is a small relative-energy perturbation. It does not establish the sign or conditioning of the rest of that finite space.

The added interface is the coefficient-uniform complete old error row (T46)–(T48), consumed by the actual theta/exterior mixed estimate (T49), whole joint inverse (T50) and exterior-shorted retained theta metric (T51). Tail profiles, nullity/domain passage, Fourier trace algebra, positive block inversion and the two prior restricted budgets are reused. The full retained complement and its mixed interaction with this positive theta image remain unpaid; they cannot be inferred from the image dimension or from an independently positive diagonal.

The original selected-integer signed Robin estimate, all its original coefficients, actual zero real parts, both signs, heights and multiplicities, elementary correction and strict core remain unchanged and unproved. Source common-core/norm/full-form transport is still required before consuming this physical result as the preprint's allocated source metric. This is a paper-level mixed interface, without Lean certification, a numerical endpoint certificate, an all-old inverse or RH conclusion, or a mathematical-priority claim.

## v2: the claimed induction step

The following induction and fold formulas are those of [arXiv:2609.20367v2](https://arxiv.org/abs/2609.20367v2), revised **20 September 2026**, 69 pages. At the arithmetic endpoint $a_k=(\log k)/2$, the source retains the pole term in $A_k=C_k-2|s_k\rangle\langle s_k|$. Lemma 6.27, under the old endpoint's positivity and inverse hypotheses, forms the actual harmonic extension

$$
H_k f=\binom{-A_k^{-1}B_{A,k}f}{f},\qquad
B_{A,k}=B_k-2s_kt_k^*,\qquad T_k=H_k^*A_{k+1}H_k.
$$

Theorem 8.5, printed pp.58–59, claims for every integer $k\ge7$, assuming $A_{k,-}>0$, a lower bound on this same extension by a strictly positive ground-coordinate coefficient plus a nonnegative transverse remainder, strictly positive when the transverse component is nonzero. This is the claimed estimate yielding $T_k>0$. The old-block positivity is an induction hypothesis, not an assumption of all-scale positivity. Theorem 1.2's restricted odd Weil criterion and the endpoint-to-all-support closure are separate consumers of the induction.

The load-bearing comparisons to inspect before any reuse are:

- Theorem 6.53 and Theorem 6.55: simultaneous ground/transverse budgets on the same common complement and the required transverse reserve.
- Lemma 8.1: placement of the full actual Schur response, with its positive saving and negative reference charge attached to the same contribution.
- Lemma 8.2: the homogeneous mixed and aligned-forcing estimate for all complex coefficients, not only a normalized scalar case.
- Lemma 8.4: the common-cut, transported form and endpoint-fold identities for the same harmonic vector, including the pole term, actual forcing and physical-pivot positivity.
- Certificate 6.62 and Certificate 8.3: the base at $Y=7$ and the all-$k$ ground margin, whose stated finite interval verification is paired with an analytic tail.

These are propositions that the source claims to prove. They are not merely extra conjectural hypotheses declared by its author; they also have not become independently verified project premises by being listed here. Checking scalar certificates alone would leave the actual-operator and function-space correspondence obligations untouched.

## v2: debit multiplicity and physical-pivot inputs

The displayed local formulas require a specific reconciliation before they can supply an all-scale estimate. In Lemma 8.4, equations (207)–(212) give two endpoint arms with the same positive target block $P$ and coupling $b$. Completing both squares deducts

$$
2D=2\|P^{-1/2}bx\|^2.
$$

Equation (212) explicitly calls $D=|\widehat h_0|^2/\Pi^{\rm phys}$ the **one-arm** debit. In contrast, (205) and MASTER-P3b use the once-deducted remainder $Q-D=E(1-u)$. At these displayed coefficients, that remainder alone does not bound the two-arm remainder. A reuse must identify the additional payment, or an explicit normalization or allocation that reconciles the same $Q$, $D$ and direct target diagonal. An overall change of units must transport all three together.

A scalar check isolates this issue without claiming to realize an arithmetic endpoint. In the one-defect model of Lemma 6.28, take both pieces to have measure one, $a_-=a_+=1$, $\beta=1/4$, $x_-=1/3$, $x_+=1$. Then the left pivot is $3/4>0$, $\gamma^c=1/3$, $g_-=0$, $h=\Pi^{\rm phys}=2/3>0$, and

$$
Q=D=\frac23,\qquad Q-D=0,\qquad Q-2D=-\frac23.
$$

Equivalently, the two displayed positive arm blocks $P=2/3$ and couplings $b=2/3$, minimized at $t_+=t_-=-1$, give $-2/3$ after subtracting the separately retained target diagonal. These are exact rational values. The example shows that the once-deducted estimate is insufficient for those local displayed formulas; it is **not** a counterexample to the actual Weil operator, nor does it show that all the other reserves in the complete argument fail.

The sign needed for the physical pivot is a separate input. With the notation of (124)–(135), positive $|R|,J$ and $1-\beta I>0$ give

$$
\Pi^{\rm phys}
=\frac{|R|}{J}\frac{1-\beta(I+J)}{1-\beta I}.
$$

Thus the old left-block condition alone does not supply the numerator's positivity. The algebra in Lemma 6.28 is valid under its stated positive-pivot condition; the relation $g=A^{\rm pre}x$ transports the forcing but does not establish that sign. The actual compression/shorting map must identify this pivot as one whose positivity follows from the permitted induction inputs. The review has not completed that identification. This is an unclosed proof input, not a claim that an old-block induction hypothesis is inherently circular.

## v2: a same-vector payment interface

The original square completion (209)–(212) retains two nonnegative arm squares. Write their sum as

$$
\mathcal S_k[F]=\sum_{\pm}
\|P_k^{1/2}t_\pm+P_k^{-1/2}b_kx_k\|^2.
$$

At the displayed coefficients, its exact accounting is

$$
\Phi_k=\mathfrak B_k|\gamma_k(f)|^2+\mathcal S_k[F]+Q_k-2D_k.
$$

Lemma 6.61 states the one-debit identity on the identified normalized vector $F_k^\#=H_kf_k^\natural$. Lemma 8.4 asserts the same identity on its general harmonic vector. Write $\mathcal C_k[F]=Q_k[F]-D_k[F]$. The displayed fold remainder is $\mathcal S_k[F]+\mathcal C_k[F]-D_k[F]$. Granting the source identification on the same $F$, it writes $\mathcal C_k=E_k(1-u_k)$ when $E_k>0$. The interface below uses $Q_k-D_k$ directly, so it remains meaningful at $E_k=0$ without dividing by $E_k$. This is a conditional accounting of the displayed form, not a verified transport identity for the actual Weil operator.

There is further coefficient slack in the source's parent-loss estimate. With $w_k=\log(1+1/k)$, put

$$
\mathcal L_k=\frac{439}{250}\sum_m\chi_m+\frac52W_k,
\qquad
\delta_k=-\log(kw_k)+\frac{439}{250}
\left(\frac{\sum_mV_{k,m}}{\log2}-\sum_m\chi_m\right).
$$

The coefficients in (203), (204) and MASTER-P3c give

$$
\mathfrak B_k-\mathcal L_k=\mathfrak g_k^{\rm M+}+\delta_k.
$$

The source bounds $0<kw_k<1$ and $\chi_m\le V_{k,m}/\log2$ make $\delta_k$ nonnegative. Nonnegative unused terms also arise from the two Young inequalities in Lemma 8.2 and from any excess of the exact inherited pivot over its certified floor. None of these sign statements supplies a comparison with the remaining $D_k$.

Throughout the proposed interface, $k$ is an integer at least seven, $A_{k,-}\succ0$, $f\in\mathcal K_k$, and $F=H_kf$ is the exact full-operator harmonic extension with the pole retained. Retain the order in Lemma 8.4: complete full-form transport, fixed-target gauge, simultaneous common-complement source short, then root-adapted endpoint fold. The one-defect and forcing identifications of Lemma 6.28, its positive multiplication coefficients, $1-\beta_kI_k>0$, $J_k>0$, $\Pi_k^{\rm phys}>0$, and the arm block $P_k\succ0$ must all hold in those coordinates. These correspondence and positive-pivot inputs remain unverified here; none is inferred from positivity of the future block.

A proposed unused remainder $\mathcal U_k$ is admissible only after establishing the common lower-form estimate

$$
\langle F,A_{k+1,-}F\rangle\ge
(\mathfrak g_k^{\rm M+}+\delta_k)|\gamma_k(f)|^2
+\mathcal R_k^\perp[f]+\mathcal S_k[F]+\mathcal U_k[F]
+Q_k[F]-2D_k[F].
$$

This lower bound is itself an unverified actual-family obligation. Conditional on it, a sufficient payment preserving the advertised ground coefficient and transverse reserve is

$$
D_k[F]\le\mathcal C_k[F]+\delta_k|\gamma_k(f)|^2
+\mathcal S_k[F]+\mathcal U_k[F]
\qquad\text{for every }f\in\mathcal K_k.
$$

Here $\mathcal U_k$ may contain only explicitly identified, proved nonnegative Young-residual or pivot-excess terms retained in that lower bound. Each must be disjoint from the expenditures already made in MASTER-P2 and the $3/5+2/5$ parent allocation, and from $\mathcal S_k$, the coefficient slack $\delta_k|\gamma_k(f)|^2$, and the transverse reserve $\mathcal R_k^\perp$ supplied by Theorems 6.53 and 6.55. It is not defined as the unknown difference. Taking $\mathcal U_k=0$ introduces no additional reserve; a nonzero choice needs the displayed lower-form proof. This interface is sufficient for the stated allocation scheme; positivity could also follow from a different allocation that spends part of the claimed ground margin. It is not asserted to be necessary for RH or for operator positivity.

The source reserves have distinct existing uses:

| Source input | Existing allocation | Additional obligation before using it for $D_k$ |
|---|---|---|
| Lemma 8.1, MASTER-P2 | Comparator saving and its negative reference charge are one inherited-response contribution. | Retain both terms; the saving is not an independent positive summand. |
| Lemma 8.2 | The certified inherited surplus is split $3/5+2/5$ to pay mixed and aligned forcing. | Identify the unused remainder and compare it with $D_k$ on the actual harmonic response. |
| Theorems 6.53 and 6.55 | The transverse budget supplies the reserved transverse term. | Prove any proposed reallocation while preserving the claimed transverse conclusion. |
| Lemma 8.4, (213) | One target diagonal splits into ground and transverse parts. | Keep the split and both expenditures in the same coordinates. |

The source does not identify an extra factor-of-two normalization in (209)–(213): the symmetric coupling is explicitly $\sqrt2\,b_k$, and the diagonal is retained once. No same-vector payment satisfying the interface above has been verified here. Harmonic restrictions could make the arm squares or parent remainders large enough; their quantitative consequence remains unverified. This narrows the reuse obligation without producing an actual-arithmetic counterexample or deciding the source's claimed RH conclusion. The coefficient calculation and conditional scalar accounting do not constitute new mathematical estimates.

The [v2 supplementary archive](https://doi.org/10.5281/zenodo.22864087), file `The_Three_Gates_Supplementary_V2.zip`, contains a Gate-II audit of full-comb scalarization. That audit explicitly limits its verdict to that particular risk and says it does not independently reprove every theorem. Its reported PASS therefore does not verify this second-arm payment. The archive describes its `master/` programs as finite scalar sweeps and its `Y7_end_to_end/` calculation as a conservative base-endpoint replication; those stated scopes do not supply the missing all-step, same-vector lower bound. These computations have not been rerun here.

## Full-form transport benchmarks and the v2 correspondence input

Proposition 5.3 must be read as an obligation about the whole form, including its diagonal. For a change of variables $x=\phi(u)$ with $J=\phi'>0$ and $g(u)=\sqrt{J(u)}f(\phi(u))$, substitution in the singular difference expression produces

$$
K(\phi(u),\phi(v))
\left|\sqrt{J(v)}g(u)-\sqrt{J(u)}g(v)\right|^2.
$$

Using only the transported off-diagonal kernel $\sqrt{J(u)J(v)}K(\phi(u),\phi(v))$ in an ordinary $|g(u)-g(v)|^2$ form leaves a multiplication term to account for, together with the transported endpoint potential. The exponential kernel identities in Lemma 5.1 do not by themselves perform this diagonal comparison. Before applying the later one-cell lower form, its full transported potential must be identified or bounded in the same coordinates. The bounded review has not completed the identification of the source's $c_A$ with all the later collar and fixed-target forms. No failure of the entire RH claim follows merely from this outstanding correspondence.

The source formulas give a specific normalization benchmark for this interface. Denote the archimedean form in (61), with the pole and prime terms excluded, by $\mathfrak a_{\mathrm{arch},a}$. For $a>0$, use the affine unitary

$$
(Tf)(t)=\sqrt2\,f(2t-1),\qquad 0<t<1.
$$

On the smooth compactly supported core, substitution in (12)–(15), (50) and (62) gives

$$
\mathfrak a_{\mathrm{arch},a}[T^{-1}g]
=\mathfrak b[g]+\bigl(c_0(a)-\log2\bigr)\|g\|_2^2
-\langle g,K_{\gamma,2a}^{(0,1)}g\rangle,
\qquad c_0(a)-\log2=-\log(4\pi a)-\gamma,
$$

where $K_{\gamma,2a}^{(0,1)}$ has kernel $2a\rho(2a|t-s|)$. The singular difference energy retains its coefficient, while

$$
V(2t-1)=-\log2-\frac12\log\bigl(t(1-t)\bigr).
$$

The original odd domain becomes $g(1-t)=-g(t)$. Extension of this core calculation requires the actual transported closed-form domain and common form-core contract. This affine map is not identified with the exponential $U_A$ or the paper's complete collar gauge. The benchmark states which scalar and regular-kernel terms occur before that identification; it neither supplies a new lower bound nor contradicts Proposition 5.3. Reusing the later $\mathfrak b$ estimates still requires the complete realization and allocation of these terms in the same direct/source forms. The displayed calculation is paper-level source bookkeeping, without a Lean validation of the integral or domain transport.

There is also a benchmark in the actual parent-cell coordinate of §6.9. Transport the same archimedean formula by $R_a$ from (8), before odd restriction. Its physical gamma kernel is $\rho(|y-z|)$, and its multiplication coefficient is

$$
c_0(a)+V(y/a)=-\log(2\pi)-\gamma-\frac12\log(a^2-y^2).
$$

Write $\mathfrak h_J$ for the singular quarter difference form on an interval $J$. Let $I=(\ell,r)\subset(-a,a)$, $w=r-\ell$, $f\in C_c^\infty(I)$, and let $E_If$ be its zero extension. The exterior strips give

$$
\mathfrak h_{(-a,a)}[E_If]-\mathfrak h_I[f]
=\frac12\int_I\log\frac{a^2-y^2}{(y-\ell)(r-y)}|f(y)|^2\,dy.
$$

The physical endpoint potential is $-\tfrac12\log(a^2-y^2)$; it cancels the numerator in this strip contribution. With $g(u)=\sqrt w\,f(\ell+wu)$, the resulting compression is

$$
\mathfrak a_{\mathrm{arch},a}^{\mathrm{ph}}[E_If]
=\mathfrak b[g]-\bigl[\log(2\pi w)+\gamma\bigr]\|g\|_2^2
-\langle g,K_{\gamma,w}^{(0,1)}g\rangle,
\qquad K_{\gamma,w}^{(0,1)}(u,v)=w\rho(w|u-v|).
$$

For a Mellin parent $C_m=[m,m+1)$ within $[1,e^{2a}]$, use $t=e^{y+a}$. Its physical interval is $I_m=(\log m-a,\log(m+1)-a)$, with $w=w_m$. The coordinate $u=\log(t/m)/w_m$ is the one used in (103)–(104). This calculation is a compression, whereas Theorem 6.53 takes an infimum over a free common complement. For the same form, prescribed data and admissible complement, zero extension is only one competitor and gives an upper comparison for that infimum. The physical compression has not been identified with the theorem's short of $\mathfrak b$. A nonsymmetric single-parent test also needs its reflected component and all cross terms to become an odd test. The pole and prime terms are excluded from these archimedean benchmarks; no counterexample to the actual odd Weil form is asserted.

The remaining realization must specify its full potential, starting interval, preceding map from the odd physical space, and relation between $A$, $a$ and $w_m$. The displayed proof of Proposition 5.3 does not identify these data. Lemma 6.16 preserves the target ground line and its orthogonal splitting; that alone is not a transformed-potential identity. Lemma 6.51 and Theorem 6.53 calculate on the already-specified $\mathfrak b$, and Lemma 8.4 invokes Proposition 5.3 again. These source dependencies locate the missing correspondence without proving that no such correspondence can exist.

The [existing small-support spectral supplier](suzuki2026screw.md) and [localization account](frankliebseiringer2006hardy.md) already cover the corresponding basic boundary energy and its small-window use. They should be reused; neither supplies this paper's all-scale collar correspondence. The supplementary scalarization audit limits its PASS to the stated scalarization risk and does not independently establish the complete diagonal identification.

## Relation to the FIB research gap

The retained-old-block, mixed-coupling and Schur-induction architecture is standard and is explicitly attempted at all scales in this source. Naming the support schedule after Fibonacci therefore supplies no architectural novelty. The project's [exact block reduction](../../D5/S3/Weil/ZetaLinear/ExactStickyReduction.lean) and [golden positivity induction](../../D5/S3/Weil/TestFunctions/GoldenPositivityInduction.lean) remain reusable under their own assumptions; this review did not rebuild them.

For an actual finite positive old block $H$, the additional estimate is $B^*H^{-1}B\preceq D$ for the matching new block and coupling; a semidefinite old block also needs the appropriate range condition. This source's claimed budget bridges are relevant candidates for detailed comparison with that obligation. They are not adopted as a supplier that has already closed it. The local scalar audit does not settle the full comparison. No external certificates, prime or zero samples, or Lean declarations were produced for this review.
