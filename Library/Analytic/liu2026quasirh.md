---
bibkey: liu2026quasirh
authors: Baiying Liu
year: 2026
title: Slightly improved zero-free half-planes for the quasi-Riemann hypothesis
doi: null
url: https://arxiv.org/abs/2610.12234v2
claim: The main theorem improves the uniform zero-free boundary for finite-order Hecke L-functions over Q(sqrt(-3)) and for Dirichlet L-functions from 7/8 to (18 xi_new + 7)/(18 xi_new + 9) = 0.874957019420098946..., where xi_new is the specified cubic root; principal poles are allowed and the boundary is excluded.
strata_touched: []
license: citation-only
triage: anchor
---

# Slightly improved zero-free half-planes for the quasi-Riemann hypothesis

The source is [arXiv:2610.12234v2](https://arxiv.org/pdf/2610.12234v2), submitted 8 October 2026 and revised 12 October 2026. It is a preprint; the paper reports Lean formalizations of its extensions, but this repository has not independently built that external Lean code. This card records the analytic statement and its interface to the existing OpenAI 7/8 source, without treating the result as a proof of the Riemann hypothesis.

## The new boundary

Let $F=\mathbb Q(\sqrt{-3})$ and let $\beta_*$ be the supremum of the real parts of nontrivial zeros of all primitive finite-order Hecke $L$-functions over $F$, together with $1/2$. The main theorem (Theorem 27.1 in v2) states

$$
\beta_*\le B_{\mathrm{new}}
=\frac{18\xi_{\mathrm{new}}+7}{18\xi_{\mathrm{new}}+9}
=0.874957019420098946\ldots,
$$

where $\xi_{\mathrm{new}}\in(0.38858,0.38859)$ is the unique root there of

$$
1188\xi^3-2160\xi^2+171\xi+190=0.
$$

The same boundary holds for every Dirichlet $L$-function, including $\zeta$, with the principal pole at $s=1$ allowed and the boundary line excluded. The paper also gives the conservative rational value

$$
B_r=\frac{34999}{40000}=0.874975
$$

before the algebraic optimization.

## Relation to the existing route

The result varies the two length parameters and the admissible moment range in the existing cubic-theta zero-detection argument. The rational step uses

$$
b_r=\frac18,\qquad \ell_r=\frac16+\frac1{10000},
$$

and gives $B_r=34999/40000$. The intermediate algebraic step uses

$$
B_{\mathrm{alg}}=\frac{1507-2\sqrt{921}}{1653}.
$$

The final step extends the unweighted fourth-moment range to $13/18\le\kappa\le1$, iterates the resulting bound, and reaches

$$
\begin{aligned}
 b_{\mathrm{new}}&=0.123405685419541002\ldots,\\
 \ell_{\mathrm{new}}&=0.166838588986270882\ldots,\\
 \kappa_{\mathrm{new}}&=2B_{\mathrm{new}}-1=0.749914038840197892\ldots.
\end{aligned}
$$

It is therefore an optimization and iteration of the already recorded OpenAI 7/8 source, rather than an independent RH criterion. The existing [OpenAI source card](openai2026quasirh.md) remains the local source for the original parameter contract; its fixed $7/8$ estimates cannot be replaced by the new boundary until the changed lengths, moment ranges, contour bounds, and Lean statements are transported together.

## Robin and FIB boundary

This improves the zero-free input used by the project's sextic packet, but it does not locate zeros on $\Re s=1/2$, give a square-root Möbius bound, or estimate the complete signed Robin residual. In particular, the new number $B_{\mathrm{new}}$ cannot be inserted into an existing $7/8$-based FIB estimate without rechecking every parameter-dependent inequality. The Robin/RH bridge remains open.

## Comparison with the 0.8748087 tracker ledger

Zhongpai Gao's preprint [*Finite-depth affine source returns for Dirichlet L-functions*](https://github.com/Gaozhongpai/QuasiRiemannTracker/blob/5085baa8fd0814c60f3ae523c6d1ce697bf12752/submissions/gao-five-step-affine-20261020/paper/paper.pdf), Theorem 1, states all-moduli Dirichlet nonvanishing at

$$
\theta=\frac{8748087}{10^7}=0.8748087:
\qquad
\Re z>\theta,\quad\neg(\chi=1\text{ and }z=1)
\quad\Longrightarrow\quad L(\chi,z)\ne0
$$

for every modulus $n\ge1$ and every Dirichlet character $\chi$ modulo $n$. The principal pole is excluded, and the boundary line is not included. The submission is `gao-five-step-affine-20261020` in [GTimG/QuasiRiemannTracker](https://github.com/GTimG/QuasiRiemannTracker); its [Lean entry point](https://github.com/GTimG/QuasiRiemannTracker/blob/b3c157e2e1278b7690eda65499bf9974dc59950c/submissions/gao-five-step-affine-20261020/src/Candidate/Main.lean) exports `Candidate.bound`. Its literature status is preprint plus tracker Lean source; this repository has not built that Lean and does not claim independent Lean certification of this boundary.

**Consumed moment and comparison.** Proposition 1, equation (M), bounds the literal initial root energy by

$$
E_\eta(\Phi,p)\le
C\,\mathcal D(\Phi)\,\mathcal S_S(p)^2
(1+|t|+T)^D Z^{1+\varepsilon},
\qquad \kappa_0=\frac{4499}{6000}.
$$

Here $\mathcal D$ and $\mathcal S_S$ denote the paper's radial and finite profile controls. The hypothesis is $51/100\le\beta\le7/8$ for the source's global zero supremum. Its window is $81/200\le m_i\le264/625$, $17/500\le s\le0.04038098$, and $m_1+m_2+\lambda s\le B$, with $s$ the selected prime width. The prime-slot mesh precedes the ambient cardinality and actual weighted source; the finite seminorm set, degree and constant precede $Z$ and the moving profiles. The original prime pools, annular coefficients, fixed mask, inherited $Q$, seed one, both reflection orientations, and shifts bounded by $T$ belong to this contract. The same estimate supplies the actual detector and conjugated numerator. Thus the required input is a whole-root estimate with its source and uniformity data, not an estimate for an independently chosen coefficient vector.

The relevant detector counts are Gao's equation (11): for inverse length $r$, plain length $m$, amplitude $p$, and outer detector density $\delta$, their exponents are

$$
1-\delta\bigl(p+(1-p)r\bigr),\qquad
1-2\delta m-2\delta p\frac{B-2m}{\lambda},\qquad
1-\delta+(5/6-\delta)(r+m-1).
$$

The affine count applies only within (M)'s actual width window; capped-width, plain-top and inherited branches cover the other ranges. The inverse exponent remains $5/6$. In these ledger formulas $B$ is Gao's affine source parameter, distinct from the zero-free boundary argument of $z_P(m;B)$ below; $B$ and $\lambda$ are the exact rationals defined by the submission's [consumer parameters](https://github.com/GTimG/QuasiRiemannTracker/blob/b3c157e2e1278b7690eda65499bf9974dc59950c/submissions/gao-five-step-affine-20261020/src/Candidate/Research/RecursiveAffine/ConsumerParameters.lean).

The final comparison is Gao's equation (12), with

$$
\begin{aligned}
\kappa_*&=2\theta-1=\frac{3748087}{5000000},&
\ell&=\frac{11}{3}-4\theta=\frac{1255739}{7500000},\\
h&=0.79716116522,& y&=h-2\ell,\\
C_O(d)&=\frac{\min(d,2y-d)}{6\kappa_*},&
C_N(d)&=\frac{2y-(2-B)d}{\lambda}.
\end{aligned}
$$

For the selected count exponent $R$ and applicable capacity $C$, that comparison requires

$$
\frac{1+\delta}{2}+\frac{13h}{75}-\frac y2-\frac\ell2
+\ell\delta p+d\left(\frac14-\frac{17}{50}\right)
-\frac{\delta pC}{2}+\frac{3dR}{4}
\le\theta-\frac1{50000000}.
$$

The paper's endpoint certificates cover $0\le\delta\le3/4$, $0\le p\le1/2$, the old-capacity ends and affine-capacity junction and top, including positive denominators and source admissions. The same-source feedback, weighted numerator and continuation obligations are part of the implication to nonvanishing. An input substitution must preserve these obligations and the strict reserve.

**Plain capacity: the coefficient is already consumed.** The [OpenAI card's capacity interface](openai2026quasirh.md#对已知无零输入的容量接口) gives

$$
z_P(m;B)=\frac{1-2m}{6(2B-1)},\qquad 0\le m\le1/2.
$$

At $B=\theta$ its coefficient is exactly $1/(6\kappa_*)$, the coefficient already used in $C_O$; the coefficient ratio is $1$. For $m<1/2$, its gain over the $7/8$ capacity is

$$
\frac{z_P(m;\theta)}{z_P(m;7/8)}
=\frac{3/4}{\kappa_*}
=\frac{3750000}{3748087}.
$$

At $m=1/2$ both capacities vanish, so their quotient is not defined. This price change is already consumed by the record, and the inverse slope is $5/6$ on both sides. The local interface also requires the complete stated Hecke-family zero-free supply; Dirichlet nonvanishing alone does not discharge that hypothesis. Neither the coefficient identity nor a larger formal capacity supplies a new certified ledger input.

**Complete coefficient energy: a different object and an insufficient exponent.** [Section 459](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#459-缓冲零点分箱下的完整原卷积联合估计), equations (459.1)–(459.3), bounds the unslotted original Möbius/plain row energy $Q(b)=\|Ab\|_2^2$, with $U\asymp K$ and $D=N=\sqrt K$, by

$$
Q(b)\ll_\varepsilon\mathcal C^2
K^{(49-10\sqrt6)/12+\varepsilon}.
$$

Its common profile/height contract is fixed, or permits the specified subpower polylog costs; it does not certify the broader original growing-height allowance. Its operator, coefficients and quantifiers are those of (458.1), not Gao's literal root energy. The convolution normalization has a mandatory factor $K$, retained in (458.9) and (459.10)–(459.11). Even formally dividing the bound by $K$ leaves exponent

$$
\frac{37-10\sqrt6}{12}
=1+\frac{25-10\sqrt6}{12}>1,
\qquad 25^2=625>600=10^2\cdot6.
$$

This division does not construct a transfer to (M). [Section 458](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#458-möbius-自卷积与无槽四矩的完整原系数预算), equations (458.11)–(458.12), has balanced exponent $25/12$, which similarly leaves $25/12-1=13/12>1$. Neither bound supplies a same-object root-moment input at exponent at most $1$. These are gaps in the available upper bounds, not lower bounds on the actual energies.

**Prime-labelled projections: the complement remains unpaid.** [Section 456](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#456-精确双频支撑对原系数反射预算的改进), equations (456.1)–(456.4), pays specified projection modes for $0<\ell<9/(1114-108\delta)$, $0<\delta<1/6$, while leaving $\mathrm T_{\rm rat}$. [Section 457](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#457-保留谱幂次与平方部分权重的完整素标记预算), equations (457.1)–(457.3), pays the complete specified prime-labelled projection for $0<\ell<1/1000$ under its common analytical costs. It explicitly leaves the orthogonal complement and other original lengths and heights unpaid. Here $L=K^\ell$ is a sector length; it is not the probe length $\ell=11/3-4\theta$ in Gao's comparison. A saving for a specified projection does not bound the total energy, so these statements cannot replace (M).

**Angular and DDDS estimates: a restricted pairing.** The [fixed-ray angular supplier](faveri2026fixedorder.md#a-full-fixed-ray-angular-supplier-from-the-finite-theta-transform) concerns the coprime squarefree pairing $Q_{\rm sf}(D,N)$ with its original outer phase and fixed profile norms. At balance $K=DN$ its pointwise angular bound is $K^{7/8+\varepsilon}$, weaker than the reused cubic bound $K^{5/6+\varepsilon}$. The [fixed angular second moment](faveri2026fixedorder.md#a-fixed-angular-second-moment-for-the-same-packet), equation (A8), improves that restricted pairing to $D^{1/2}N(DN)^\varepsilon$, hence $K^{3/4+\varepsilon}$ at balance with fixed height. Its DDDS-based improvement still leaves shared primes, nonsquarefree columns, other dual terms and the full actual-order-six contraction as separate obligations. Thus even this stronger packet estimate does not supply Gao's whole source. Its actual witness lengths, ray presentation and cumulative height costs must also remain within its stated contract.

**Floor and contour: no paid replacement.** The compared notes supply no theorem lowering the detector floor $51/100$ or moving the contour $\Re z=17/50$ while paying its analytic obligations. The [OpenAI card's full contours and outer rows](openai2026quasirh.md#全部轮廓主行及外围行) retain that contour and the buffered reciprocal-$L$ restrictions. Section 459 retains the floor; the raw floor exponent following (459.12) satisfies

$$
\frac{201}{100}-2=\frac1{100}>0.
$$

It therefore exceeds the $K^2$ scale of that row-energy problem. An improvement in a different projection or packet does not pay this floor bin or justify an unlicensed contour shift.

**Stop result.** None of these capacity, complete-energy, projection or angular/DDDS estimates gives a strictly stronger same-object input to the $8748087/10^7$ ledger; they do not lower $\theta$. The repository estimates remain conditional on their stated analytical inputs. Possible future inputs through this line include a same-object floor-bin theorem, a separately paid contour change, or a root-moment estimate compatible with Gao's full root-moment contract and providing a strict saving that survives every detector and final-comparison constraint. Reoptimizing the record's existing inputs does not constitute such a new estimate.

## Exact-rescaling ceilings and density substitutions

The external manuscript by `span_of_dilates`, [*Structural ceilings in the cubic-theta quasi-Riemann-hypothesis argument*, v2](https://rstation.ai/problems/riemann_hypothesis/papers/40/v2), records two restrictions on specified modifications of the OpenAI/Liu argument. Its [primary text](https://rstation.ai/api/v1/papers/riemann_hypothesis_40/versions/2/download), Propositions A–B, is the source for this section. These are literature results to reuse, not new repository theorems. The manuscript's introductory zero-free numbers do not replace the later tracker comparison above. No external Lean build or independent certification of its numerical tables is asserted here.

**Exact compensation.** Proposition A permits a finite linear combination of rescaled copies of the same completed average,

$$
\sum_{j=1}^J\beta_jQ^{-c_j}
I_\eta(X/Q^{\alpha_{X,j}},Y/Q^{\alpha_{Y,j}},Z/Q^{\alpha_{Z,j}}).
$$

The real exponents and complex coefficients are independent of the slot prime. The required local Mellin multiplier is exactly $Q^{z-1-w}$ on the product of the three original contour lines, for every good slot prime in an unbounded family. After combining identical affine exponent vectors, the proposition gives the single compensation

$$
(c,\alpha_X,\alpha_Y,\alpha_Z)=(3/2,1,1,0),
\qquad\beta=1.
$$

The source's original rescaled-length condition then gives $\ell\le l_x$ and $h=1+\ell-l_x\le1$. With its nonnegative low-side loss $\lambda$, the direct-comparison bookkeeping boundary satisfies $\sigma_0=1-h/6+\lambda\ge5/6$. This conclusion concerns that exact comparison and compensation class. It gives no obstruction for a different base average, slot-prime-dependent coefficients, a bounded family of primes, or a controlled approximate compensation. The source explicitly leaves its approximate-cancellation heuristic unproved.

**Density substitution in Liu's system.** Write $\xi(\kappa)$ for the smaller root of

$$
(216\kappa-18)\xi^2-(468\kappa-57)\xi+150\kappa-20=0,
\qquad 13/18\le\kappa\le1,
$$

and set $A_*(\kappa)=4/[3(1-\xi(\kappa))]$. Proposition B assumes an additional estimate for the same zero-class row family,
$N_{\rm fam}(a)\ll U^{A(1-a)+\varepsilon}$, and replaces its count exponent by
$\min\{R_\kappa(\delta,x),A(1-\delta)/2\}$, where $\delta=2a-1$.
At Liu's existing optimum, this branch strictly reduces the critical count exactly when

$$
A<A_*(\kappa_{\rm new})=2.180727892\ldots.
$$

For $A\ge A_*(1)=2.183363347\ldots$, the source states that the optimum of this modified Liu system remains unchanged over the whole stated moment range. It leaves the intermediate interval undecided. The local threshold at $\kappa_{\rm new}$ does not decide that interval or establish a new optimum. Its reoptimization tables are explicitly numerical grid searches, rather than certified zero-free bounds.

The extra density input must count the same family with its actual conductor, height, finite ray data and zero multiplicities. A single-$L$ height-density exponent or an all-character conductor estimate cannot be inserted by identifying its exponent symbol with $A$; its family and resource powers must first be transported. The manuscript's comparison with classical density exponents does not itself supply that transport.

**Relation to the complete Möbius/plain energy.** Neither proposition estimates $\|(I-P_L)Ab\|_2^2$ or the full energy of the preceding original coefficient. The critical class and admissible system in Proposition B belong to Liu's zero-free comparison, rather than the maximization in (459.11). The complete-energy bound in §459, the narrow all-small-label projection in [§484](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES_II.md#484-全部小标记的反射主项与完整投影预算), and the final signed Robin restoration remain distinct targets. Reusing these scoped ceilings avoids repeating their parameter optimizations without treating them as a general impossibility theorem for RH.

## Amplitude-resolved counts and the original complete energy

Liu v2 [§10.1, (10.1), and Proposition 29.1, (29.1)–(29.3)](https://arxiv.org/html/2610.12234v2) retain a prime-amplitude coordinate that the complete-energy estimate in §459 does not use. With the source's full Hecke-family zero-free hypothesis $\beta_*\le(1+\kappa)/2$, $13/18\le\kappa\le1$, its required auxiliary-prime length $\ell_{\rm src}/d\ge1/5+\rho$, and its original finite character, bin, height and coefficient contracts, the count exponent is

$$
\begin{aligned}
c_\kappa&=\frac2{3\kappa},&
D_\kappa(x)&=3-(1+c_\kappa)x,&
P_\kappa(x)&=(2-c_\kappa x)(1-x),\\
J_\kappa(\delta,x)&=(5/6-\delta)D_\kappa(x)+\delta P_\kappa(x),\\
R_\kappa(\delta,x)&=1-\delta+
\frac{(5/6-\delta)\delta P_\kappa(x)}{2J_\kappa(\delta,x)},
\qquad 0<\delta<5/6,\quad0\le x\le1/2.
\end{aligned}
$$

The source's original zero-class restrictions also apply; the displayed rectangle is not an assertion that every pair occurs. For the present full row family, its source variables may be taken as $Z=U,d=1$ with the original finite Fourier character family included in the same fixed $\Theta$. Sixth-power-free rows of lower inducing order, all nonunit row zero classes and the common buffer are retained. A Dirichlet-only zero-free input cannot discharge the full Hecke-family hypothesis.

The coordinate $x=\bar g/\delta$ comes from the source's auxiliary prime polynomials

$$
Q_i(u;z)=P_i^{-1/2}\sum_{p\in\mathcal P_i}
\overline{\chi_p(u)}W_i(q_p/P_i)(q_p/P_i)^{z-1},
\qquad
\bar g=\frac{\sum_i\ell_i g_i}{\ell_{\rm src}}.
$$

Here $g_i$ indexes the size of $|Q_i|$, with the bottom bin $g_i=0$ carrying only an upper bound. This is a different observation from the original annular plain polynomial $S_u(U^{1/2})$, or the original inverse polynomial at length $U^{1/2}$.

The count exponent $R_\kappa(\delta,x)$ is decreasing in $x$ on its stated range, and

$$
R_\kappa(\delta,0)=\frac{15-16\delta}{15-6\delta}.
$$

Consequently, merely replacing the count in (459.10), while retaining its inverse supremum and plain fourth moment, returns the same upper envelope as (459.11). The allowed bottom bin is still present, independently of $\kappa$. The known zero-free cutoffs do not remove its maximizing $\delta_*=(15-5\sqrt6)/6$. This substitution alone therefore leaves the bound $\mathcal C^2K^{(49-10\sqrt6)/12+\varepsilon}$ unchanged; it is not a proof that the actual energy saturates that bound.

The remaining interface cannot be supplied by relabelling the source's detector witnesses. Source (5.2) gives the target-polynomial pointwise bounds in terms of the zero bin and lengths, with no $x$ gain. Source (5.5) returns a separate pair of detecting lengths, rather than prescribing the target pair $D=N=U^{1/2}$. Moreover, attaching these prime slots to the existing plain fourth moment at the target pair exhausts the length allowance: (9.4)/(28.2), with row exponent $m_0=1$, conductor exponent $q_0=0$ and hence source allowance $M=1$, requires $n_1+n_2+6\kappa z_{\rm p}\le M$. The two original plain exponents sum to $n_1+n_2=1$, so $1+6\kappa z_{\rm p}\le1$, hence $z_{\rm p}=0$. It supplies no positive-width prime-amplitude gain there.

A stronger original-coefficient estimate would have to relate the same inverse/plain energy to these prime amplitudes, including the bottom bin, or supply another estimate for the complete kernel. Neither the count refinement nor a positive operator-norm lower bound provides that relation. This is a limitation of the specified substitution into §459, not a general impossibility result for amplitude-sensitive methods or RH.

## Actual inverse coefficients: a limit of norm-only refinements

For one original finite Fourier component, reuse the exact coefficient in (458.6), including shared primes:

$$
M_\xi(u)=D^{-1/2}\sum_{d\ {\rm good}}\mu(d)V(q_d/D)\xi(d)\chi_d(u),
\qquad
M_\xi(u)^2=\sum_a g_D(a)\chi_a(u),
$$

$$
g_D(a)=D^{-1}\xi(a)\sum_{d_1d_2=a}
\mu(d_1)\mu(d_2)V(q_{d_1}/D)V(q_{d_2}/D).
$$

Every column and factor sum in this section is over good ideals, meaning ideals prime to $S$; $\xi$ is multiplicative and has modulus one on this semigroup. Ideals are counted once, $q_d=Nd$, and the field and bad-prime set $S$ are fixed. Assume a **fixed nonzero smooth complex annular profile $V$**. The following argument concerns this one Fourier component and its exact self-convolution.

Reuse the classical Bohr lift and Haar Plancherel identity of Hedenmalm–Lindqvist–Seip, [arXiv:math/9512211v1, §2.2, (2-7) and the subsequent Plancherel identity](https://arxiv.org/html/math/9512211v1). For the ideal semigroup, give each prime ideal its own circle coordinate. More precisely, let $\mathcal P_D$ be the finite set of prime ideals dividing the support of

$$
v_D(d)=\mu(d)\xi(d)V(q_d/D),
\qquad
P_D(z)=\sum_d v_D(d)\prod_{\mathfrak p\in\mathcal P_D}
z_{\mathfrak p}^{v_{\mathfrak p}(d)}.
$$

Unique prime-ideal factorization identifies multiplication of these monomials with multiplication of ideals. Thus the coefficient of the monomial indexed by $a$ in $P_D^2$ is exactly $Dg_D(a)$, including the terms with shared primes. Distinct ideals with the same norm remain distinct monomials; a time average of $q_d^{-it}$ would not give this orthogonality.

On the finite torus $\mathbb T^{\mathcal P_D}$, with Haar probability measure $m_D$, Plancherel and Cauchy–Schwarz give

$$
\begin{aligned}
D^2\|g_D\|_2^2
&=\int |P_D|^4\,dm_D\\
&\ge\left(\int |P_D|^2\,dm_D\right)^2\\
&=\left(\sum_{d\ {\rm good}}
\mu(d)^2|V(q_d/D)|^2\right)^2.
\end{aligned}
$$

All sums here are finite. Haar integration is an auxiliary coefficient identity, not an equidistribution assumption for the actual sextic row characters. The bound permits arbitrary complex phases of the fixed profile; it does not rely on retaining positive terms in a complex convolution expansion.

For the squarefree count, directly reuse the principal-character case of [G5 and its squarefree expansion](faveri2026fixedorder.md#the-actual-gram-including-all-original-zeros), based on Lemke Oliver–Thorner, Lemma A.3 in [Pasten, arXiv:1705.09251v4](https://arxiv.org/pdf/1705.09251v4). Taking the label $R=1$ and profile $|V|^2$ in G3 gives

$$
D^{-1}\sum_{d\ {\rm good}}\mu(d)^2|V(q_d/D)|^2
\longrightarrow C_{V,S}
=\frac{\operatorname{Res}_{s=1}\zeta_F(s)}{\zeta_F(2)}
\prod_{\mathfrak p\in S}(1+q_{\mathfrak p}^{-1})^{-1}
\int_0^\infty |V(y)|^2\,dy>0.
$$

This uses ideal counting, not an additional restriction to one ray class or a count of unit representatives. Consequently $\liminf_{D\to\infty}\|g_D\|_2^2\ge C_{V,S}^2>0$. Bohr lifting, Haar Plancherel, Cauchy–Schwarz and the counting theorem are classical inputs; this is their application to the existing coefficient, not a new harmonic-analysis, large-sieve or RH theorem.

At $D=U^{1/2}$, the coefficient-independent sixth-order sieve in (458.7) has cost $U^{7/6+\varepsilon}\|g_D\|_2^2$. Together with the unchanged plain fourth moment $\ll U^{1+\varepsilon}$, an inverse fourth-moment exponent $B$ would give complete-energy exponent $(B+3)/2$ when $U\asymp K$. To improve the current §459 exponent through this route requires

$$
B<B_*:=\frac{31-10\sqrt6}{6}=1.084183762\ldots.
$$

Paying this improvement solely by reducing the coefficient norm in the unchanged sieve would require, for some fixed $\eta>0$,

$$
\|g_D\|_2^2\ll U^{B_*-7/6-\eta},
\qquad B_*-7/6=\frac{12-5\sqrt6}{3}<0.
$$

The positive lower bound excludes this norm-only shortcut for every fixed nonzero smooth complex annular profile. For profiles that vary with $D$, the finite Haar inequality remains exact, but a uniform positive constant requires the normalized squarefree mass on its right-hand side to stay bounded away from zero. It gives **no lower bound** for the actual inverse fourth moment, $Q(b)$, any projected energy, or the complement: cross terms between distinct columns can cancel through the row characters. It also gives no corresponding lower bound for a convolution of two different factors such as the original $\mu*\mathrm{plain}$ coefficient, or for the sum of different Fourier components. Coefficient-sensitive estimates for the actual row correlations, zero-bin gains and the full signed Robin restoration remain separate questions.

## The original convolution norm before sixth-power compression

The self-convolution argument above does not apply to two different factors. For the original coefficient, instead reuse the distinct-prime construction in [§473](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#473-对全部-f4-掩码与投影稳定的物理行切面) and the fixed-ray prime-ideal theorem used there. Let $D=N=\sqrt K$ and keep fixed nonzero smooth complex annular profiles $V,W$. Suppose the original finite ray multiplier $\omega$ is nonzero on an allowed class. Then the **uncompressed** coefficient

$$
b(h)=\omega(h)\sum_{dn=h}\mu(d)V(q_d/D)W(q_n/D)
$$

has

$$
\|b\|_2^2\gg_{V,W,\omega,S}\frac{K}{(\log K)^2}
\qquad(K\longrightarrow\infty).
$$

Here is the additional counting interface, not a new prime-distribution theorem. For distinct good prime ideals $p,q$ with $q_p/D,q_q/D$ in fixed positive compact intervals, the unit and product divisors lie outside the inverse annulus for large $D$. The existing semiprime identity therefore gives

$$
b(pq)=-\omega(pq)H(q_p/D,q_q/D),\qquad
H(x,y)=V(x)W(y)+V(y)W(x).
$$

The continuous kernel $H$ is nonzero somewhere. If $V(x)W(x)\ne0$ for some $x$, use $H(x,x)=2V(x)W(x)$ and perturb to distinct arguments. Otherwise choose $V(x)\ne0$ and $W(y)\ne0$; the disjoint nonzero sets give $H(x,y)=V(x)W(y)\ne0$. In either case choose disjoint compact intervals $I,J$ with nonempty interiors on which $|H|$ has a positive lower bound. Choose fixed prime-ray classes whose product is the retained class of $\omega$. The fixed-ray prime-ideal theorem gives $\gg D/\log D$ primes in each of $DI,DJ$, after deleting $S$. Unique ideal factorization and $I\cap J=\varnothing$ make their $\gg D^2/\log^2D$ products distinct. On this class $|\omega|$ is a fixed positive constant, proving the bound.

Consequently, a fixed power saving for the norm of this uncompressed coefficient cannot by itself pay the balanced sixth-order sieve cost. Even a hypothetical bound $Q(b)\ll K^{7/6+\varepsilon}\|b\|_2^2$ would need a coefficient-norm exponent below

$$
\frac{49-10\sqrt6}{12}-\frac76
=\frac{35-10\sqrt6}{12}<1
$$

to improve §459 by this mechanism. This is only a restriction on a norm-only payment: the actual unrestricted-column sieve still requires its original sixth-power decomposition and masks. The argument gives no lower bound after aggregation of sixth-power-equivalent columns, or for $Q(b)$, a projection or its complement, including the actual row energy after the finite Fourier components are recombined. No uniform lower bound is claimed for profiles varying with $D$. It leaves cancellation in the actual row kernel available. The semiprime identity, ray-prime theorem and counting argument are reused classical tools; this paragraph adds no analytic Lean certification, improved Robin bound or literature-priority claim.

## The fixed-order density theorem at the existing critical bin

A separate possible substitution is de Faveri's [arXiv:2610.04045v1, Corollary 1.5](https://arxiv.org/html/2610.04045v1#S1.SS2). For the source's $n$th-power-free Hecke family over a degree-$d_F$ field, it bounds the total zero count by

$$
\sum_{q_a\le X}^{\flat}N(\sigma,T,a)
\ll X^{1-\delta_n(\sigma)+\varepsilon}
T^{1+d_F(1-\sigma)/(3-2\sigma)+\varepsilon}.
$$

This is an existing literature theorem. To replace a count in §459 it would also have to cover every original finite twist and primitive inducing presentation, with its common height buffer. Even granting that transport and discarding the positive height cost, its stated exponent does not improve the maximizing bin. For $n=6$, writing $\delta=2\sigma-1$, the middle branch $1/3\le\delta\le5/6$ gives

$$
R_6(\delta)=1-
\frac{\delta(18\delta-3)}{60\delta-36\delta^2-10}.
$$

At the existing $\delta_*=(15-5\sqrt6)/6\in(1/3,1/2)$, comparison with $R(\delta)=(15-16\delta)/(15-6\delta)$ is exact:

$$
R_6(\delta_*)-R(\delta_*)=
\frac{\delta_*(312\delta_*-252\delta_*^2-55)}
{(15-6\delta_*)(60\delta_*-36\delta_*^2-10)}>0.
$$

Both denominator factors are positive on $[1/3,1/2]$. The numerator's quadratic factor is concave with endpoint values $21,38$, hence positive throughout that interval. Numerically the two count exponents are $R_6(\delta_*)=0.7575635858\ldots$ and $R(\delta_*)=0.6254252143\ldots$. Thus retaining the old count and taking the minimum with this new input still attains the old maximum at $\delta_*$. It leaves the §459 energy exponent $(49-10\sqrt6)/12$ unchanged; replacing the old count outright would be weaker there. The $T$ factor and finite transport costs cannot improve this comparison. No optimization of other bins, new zero-density theorem, or lower bound on the actual energy is asserted. A stronger same-object joint estimate remains required.
