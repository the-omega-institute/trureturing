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
