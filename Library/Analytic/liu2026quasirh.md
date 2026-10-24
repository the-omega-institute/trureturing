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

## The actual-order-six correlation for the inverse fourth moment

The remaining correlation can first be sought for the actual inverse square, rather than for an arbitrary two-factor convolution. Reuse $g_D$ from (458.6) above, with the same original row family, fixed Fourier component $\xi$, nonnegative row weight $\Omega$, zero extensions and fixed profile/height contract. Let $r_j(a)$ denote the ideal whose prime valuations are $v_{\mathfrak p}(a)\bmod j$. Since each nonzero Möbius factor is squarefree, every column in $g_D$ is cube-free. Consequently $r_3$ is injective on this support: different columns cannot have an actual ratio character of order two. Different columns with equal $r_2$ have ratio order three; unequal $r_2$ forces order six. These statements refer to the underlying primitive ratio on the coprime locus; its original zeros remain in the row sum.

The actual Möbius structure is retained by this cut. Write a cube-free column uniquely as $a=st^2$, with $s,t$ squarefree and $(s,t)=1$, and put

$$
A_D(s,t)=\sum_{ef=s}V(q_tq_e/D)V(q_tq_f/D).
$$

Every contributing pair is $d_1=te,d_2=tf$, and $\mu(d_1)\mu(d_2)=\mu(s)$. Hence the exact coefficient is

$$
g_D(st^2)=D^{-1}\mu(s)\xi(st^2)A_D(s,t).
$$

Thus the Möbius sign is constant within each parity-core block and cancels from its squared norm; it remains in cross-core products as $\mu(s)\mu(s')$. For complex $V$, no positivity of $A_D$ is asserted. Replacing these fixed cross-core coefficients by an independently chosen vector would lose the intended input.

Define the actual weighted row kernel and two contractions by

$$
\begin{aligned}
\mathcal K_{U,\Omega}(a,b)
&=\sum_{u\ {\rm original}}\Omega(q_u/U)
 \chi_a(u)\overline{\chi_b(u)},\\
H_2^\mu
&=\sum_s\sum_{u\ {\rm original}}\Omega(q_u/U)
 \left|\sum_{r_2(a)=s}g_D(a)\chi_a(u)\right|^2,\\
E_6^\mu
&=\sum_{\substack{a,b\ {\rm cube\!\!-\!free}\\r_2(a)\ne r_2(b)}}
 g_D(a)\overline{g_D(b)}\mathcal K_{U,\Omega}(a,b).
\end{aligned}
$$

The last sum uses ordered pairs and is real by Hermitian symmetry; no nonnegativity is asserted for it. Finite expansion gives the same-object identity

$$
\sum_{u\ {\rm original}}\Omega(q_u/U)|M_\xi(u)|^4
=H_2^\mu+E_6^\mu.
$$

**The cubic block is already paid.** Directly reuse the parity-block supplier in the [existing lower-order decomposition](faveri2026fixedorder.md#separating-the-lower-order-character-blocks). Its proof uses only the divisor envelope and the cited cubic sieve, so it applies to $G_D(a)=Dg_D(a)$, supported on $q_a\asymp K_\mu:=D^2$, with $|G_D(a)|\ll_{V,\varepsilon}q_a^\varepsilon$. With $B_s=(K_\mu/q_s)^{1/2}$, the existing bound and core sums give

$$
\begin{aligned}
H_2^\mu
&\ll_{\varepsilon,\mathrm{fixed\ data}}
 (UK_\mu)^\varepsilon D^{-2}
 \sum_{q_s\ll K_\mu}B_s
 \left(U+U^{1/3}B_s+U^{2/3}B_s^{2/3}\right)\\
&\ll_{\varepsilon,\mathrm{fixed\ data}}(UD)^\varepsilon U.
\end{aligned}
$$

The mandatory $D^{-2}$ is the squared normalization of $g_D$. The source already supplies $\sum_s B_s\ll K_\mu$, $\sum_s B_s^2\ll K_\mu\log(2K_\mu)$ and $\sum_s B_s^{5/3}\ll K_\mu$; they are reused, not new counting results. The bound retains all original sixth-power-free rows, including lower inducing orders. A row enlargement is used only inside the positive cubic blocks, never to erase a mask from $E_6^\mu$.

**The unpaid input is specific to these coefficients.** At $D=\sqrt U$, an upper bound

$$
\operatorname{Re}E_6^\mu
\ll_{\varepsilon,\mathrm{fixed\ data}}U^{B+\varepsilon},
\qquad
1<B<\frac{31-10\sqrt6}{6},
$$

would give an inverse fourth moment of order $U^{B+\varepsilon}$. If uniform over the original finite components and the profile derivatives required by the existing common-cost contract, it would combine with the unchanged plain fourth moment at $D=N=\sqrt U$, $K=U$, to yield

$$
Q(b),\ \|(I-P)Ab\|_2^2
\ll_{\varepsilon,\mathrm{fixed\ data}}
K^{(B+3)/2+\varepsilon},
$$

strictly improving the current §459 exponent. This is a conditional consumer, not a supplied bound for $E_6^\mu$. The generic sixth-order sieve still gives only the $7/6$ inverse-fourth exponent. Separate bounds $H_2^\mu\ll U^{1+\varepsilon}$ and $E_6^\mu\ll U^{1+\varepsilon}$ would reach $K^{2+\varepsilon}$ through this Cauchy step, without a strict saving. These two separate upper bounds do not supply a sub-$U$ bound for the full inverse fourth moment. Other witness lengths, growing-height costs and the final signed Robin restoration remain unpaid. This application reuses the lower-order sieve results and adds no analytic Lean certification or literature-priority claim.


## Small shared-gcd localization using the existing inverse-L input

The same buffered inverse-$L$ input as [§459](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#459-缓冲零点分箱下的完整原卷积联合估计) can be applied to each actual shared-gcd packet in the inverse square. Together with the existing full-interference inequality [(462.10)](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#462-原卷积的大重复部分与完整交叉项), it reduces the unpaid correlation to $q_t\le U^\theta$ for any fixed $\theta>0$. This is an application of the existing analytic bounds and Euler products; the remaining head estimate is not supplied.

Keep the original finite component, all original rows and zeros, and the same fixed or polylog profile/height contract. Set $D=\sqrt U$ and write

$$
(\mathsf A_U f)(u)=\sqrt{\Omega(q_u/U)}\sum_a f(a)\chi_a(u),
\qquad \mathcal T(f)=\|\mathsf A_Uf\|_2^2.
$$

Thus $\mathsf A_Ug_D=\sqrt\Omega\,M_\xi^2$, with the row weight counted once. The original, untruncated inverse polynomial already satisfies

$$
\mathcal T(g_D)\ll U^{B_*+\varepsilon},
\qquad B_*=(31-10\sqrt6)/6.
$$

Indeed, directly reuse (459.7), (459.9) and the evaluated maximum (459.12): a nonfloor bin contributes $U^{R(\delta)+\delta+\varepsilon}$ to the fourth moment, while the floor contributes $U^{51/50+\varepsilon}<U^{B_*+\varepsilon}$. No new optimization is needed. Constants below depend on the same fixed data and required finite profile seminorms; actual polylog costs are absorbed in $U^\varepsilon$.

**Recovering the inverse-$L$ representation packet by packet.** Put $\psi_u(d)=\xi(d)\chi_d(u)$. For squarefree $t$ and $X=D/q_t$, define

$$
C_{X,t}(u)=X^{-1}
\sum_{\substack{e,f\ {\rm squarefree}\\(e,f)=1,\ (ef,t)=1}}
\mu(e)\mu(f)V(q_e/X)V(q_f/X)\psi_u(ef).
$$

All ideals remain good. The exact packet with shared gcd $t$ in the original square is

$$
F_t(u)=\frac{\psi_u(t)^2}{q_t}C_{D/q_t,t}(u),
\qquad M_\xi(u)^2=\sum_t F_t(u).
$$

The factor $q_t^{-1}$ is mandatory: $X/D=1/q_t$. In particular, a collision between $t$ and $u$ makes the original packet zero.

On the initial absolutely convergent lines $\Re s=\Re w=2$, the double Dirichlet series of the sum defining $C_{X,t}$ is

$$
\prod_{\mathfrak p\nmid St}
 (1-\psi_u(\mathfrak p)q_{\mathfrak p}^{-s}
    -\psi_u(\mathfrak p)q_{\mathfrak p}^{-w})
=\frac{\mathscr H_t(s,w;u)}
 {L_{\rm orig}(s,\psi_u)L_{\rm orig}(w,\psi_u)}.
$$

For $z_{\mathfrak p}=\psi_u(\mathfrak p)q_{\mathfrak p}^{-s}$ and $v_{\mathfrak p}=\psi_u(\mathfrak p)q_{\mathfrak p}^{-w}$, the correction is exactly

$$
\mathscr H_t=
\prod_{\mathfrak p\nmid St}
 \frac{1-z_{\mathfrak p}-v_{\mathfrak p}}
 {(1-z_{\mathfrak p})(1-v_{\mathfrak p})}
\prod_{\substack{\mathfrak p\mid t\\\mathfrak p\notin S}}
 \frac1{(1-z_{\mathfrak p})(1-v_{\mathfrak p})}.
$$

The first product differs locally from $1$ by $O(q_{\mathfrak p}^{-\Re(s+w)})$. Consequently, on $\Re s,\Re w\ge a_0=51/100$, it is holomorphic and bounded uniformly in the original characters; the second product costs only $\ll_\varepsilon q_t^\varepsilon$. Original character zeros give local factors $1$. Only $\mathscr H_t$ is used, never its reciprocal, so zeros of its numerator present no obstruction. No $L$-function for $\psi_u^2$ or new moving-conductor zero-free hypothesis is introduced.

Double Mellin inversion now expresses $C_{X,t}$ as

$$
\frac1{X(2\pi i)^2}
\int_{(2)}\!\int_{(2)}
\frac{X^{s+w}\widehat V(s)\widehat V(w)\mathscr H_t(s,w;u)}
 {L_{\rm orig}(s,\psi_u)L_{\rm orig}(w,\psi_u)}\,dw\,ds.
$$

For a row in an original bin indexed by $a$, reuse its same finite zero-free rectangle twice, moving the truncated lines successively to $\Re s=\Re w=a+8e$. The path always has $\Re(s+w)>1$. The already owned reciprocal bounds therefore give, for $\delta=2a-1$,

$$
|C_{X,t}(u)|\ll U^\varepsilon X^{\delta+O(e)}+O(U^{-20}).
$$

This is a new application of the original bounds to the coprimality-corrected packet, not an identification of the truncated whole vector with an original inverse polynomial. If $\operatorname{supp}V\subset[v_-,v_+]$, a nonempty packet has $q_t\le v_+D$, hence $X\ge1/v_+$. The bounded range $1/v_+\le X<1$ involves only finitely many $e,f$ and satisfies the same bound directly. For $X\ge1$, the absolute-line tails and finite horizontal joins are uniformly $O(U^{-20})$ after choosing the outer Mellin decay order. The weighted packet sum costs only $\sum_{q_t\le v_+D}q_t^{-1}\ll\log U$ for these errors.

Fix $0<\theta<1/2$, put $T=U^\theta$, and restrict the original coefficient by

$$
g_{>T}(st^2)=g_D(st^2)\mathbf1_{q_t>T},
\qquad g_{\le T}=g_D-g_{>T}.
$$

The cutoff is independent of the row and restored profile parameters. The existing ideal-counting tail $\sum_{q_t>T}q_t^{-1-\delta}\ll T^{-\delta}$ is uniform for $\delta\ge1/50$. With the actual factor $q_t^{-1}$ in $F_t$, it gives

$$
\left|\sum_{q_t>T}F_t(u)\right|
\ll U^\varepsilon(D/T)^\delta+O(U^{-10}).
$$

Thus each nonfloor bin contributes at most $U^{R(\delta)+(1-2\theta)\delta+\varepsilon}$ to $\mathcal T(g_{>T})$. Reuse $R(\delta)+\delta\le B_*$ and $\delta\ge1/50$, rather than optimizing again. The floor exponent is $51/50-\theta/25$, so the same bound holds there:

$$
\mathcal T(g_{>T})\ll U^{B_*-\theta/25+\varepsilon}.
$$

Fix $\theta$ and the desired strict margin first; choose the bin width and internal losses accordingly, then the finite Sobolev orders, the small original buffer-height exponent and finally the outer Mellin decay order. Mixed profile derivatives replace the two copies of $V$ by their required derivatives in the same formula. Fixed or polylog norm twists enter the same two original $L$-functions; their derivative logarithms and the finite Euler corrections are paid by the same cost contract. This does not extend the original growing-height allowance.

The original full moment and the existing Hilbert inequality (462.10) retain all interference and yield

$$
\left|\mathcal T(g_D)-\mathcal T(g_{\le T})\right|
\ll U^{B_*-\theta/50+\varepsilon}.
$$

Define $E_6^{\mu,\le T}$ by replacing both coefficient occurrences in the preceding ordered cross-core sum by $g_{\le T}$. The same cubic-block supplier applies afresh through its divisor envelope, giving $H_2(g_{\le T})\ll U^{1+\varepsilon}$; coefficient truncation is not asserted to decrease a positive block. Consequently an estimate

$$
\operatorname{Re}E_6^{\mu,\le T}\ll U^{B_*-\nu+\varepsilon},
\qquad 0<\nu<\min\{B_*-1,\theta/50\},
$$

uniform in the original finite components and required profile derivatives, would give $\mathcal T(g_D)\ll U^{B_*-\nu+\varepsilon}$. The already owned plain fourth moment would then give $Q(b),\|(I-P)Ab\|_2^2\ll K^{\kappa_{\rm joint}-\nu/2+\varepsilon}$ at $K=U$. No such head estimate is supplied here. Every squarefree column and the $t=1$ packet remain, with their original Möbius signs, row masks and cross-core phases. This reduces the missing estimate to small actual shared gcds without improving the full moment, proving a sub-$K^2$ bound, or restoring the signed Robin expression. Euler multiplication, finite Mellin shifts, counting and the Hilbert inequality are reused tools; no new analytic Lean certification or literature-priority claim is made.

## Low primitive conductors in the small-gcd head

A second cut uses the gcd **between two columns**, rather than the shared gcd inside one coefficient. It pays the short primitive-conductor part of the preceding head by classical Hecke convexity. This is an application of an existing mean-value tool, not a new character-sum theorem or a bound for the remaining head.

Use a complete good sixth-power-free row moment with smooth annular weight, allowing fixed finite ray partitions. If the actual moment has further row selectors, first use the [existing complete positive majorant](faveri2026fixedorder.md#a-source-conditional-pure-dual-power-contraction), then define its $H_2$ and $E_6$ afresh. Apply the preceding buffer/count inputs to that same complete family with its fixed finite character data. A signed contraction on an arbitrary retained row subset or zero bin cannot be bounded by silently deleting its selector. All quantities below belong to this one complete moment; its positive bound then controls the original restricted moment.

**A complete-row kernel from classical convexity.** For an ordered pair in $E_6$, write

$$
a=hx,\qquad b=hy,\qquad h=(a,b),\qquad (x,y)=1.
$$

After each fixed ray Fourier expansion, let $\chi_0$ be the exact zero-extended ratio character on the row variable, and $\chi$ its primitive inducing character with conductor $\mathfrak f$. At every good prime of $xy$ the reduced sextic exponent is nonzero, so

$$
q_{\mathfrak f}\asymp_S q_{\operatorname{rad}(xy)}
\ll (U/q_h)^2.
$$

This uses the same [Gao–Zhao conductor interface](faveri2026fixedorder.md#the-actual-gram-including-all-original-zeros). Since $r_2(a)\ne r_2(b)$ on the cube-free support, a nontrivial good-prime component remains. A fixed bad-prime/unit twist cannot cancel it; thus $\chi$ is nonprincipal. Primes of $h$ at which the ratio exponents cancel remain zero-only primes of $\chi_0$.

For $\Re s>1$, the exact sixth-power-free row series is

$$
\sum_{u\ {\rm sixth\ power\ free}}\frac{\chi_0(u)}{q_u^s}
=\frac{L(s,\chi_0)}{L(6s,\chi_0^6)}.
$$

The zeros at original conductor and collision primes remain in both imprimitive $L$-functions. In particular the denominator is not replaced by a primitive zeta function. Its reciprocal is absolutely bounded on $\Re s=1/6+\varepsilon$. Restoring the primitive numerator leaves only factors $1-\chi(\mathfrak p)q_{\mathfrak p}^{-s}$ at zero-only primes; their product costs $U^\varepsilon$.

Directly reuse the Rademacher strip estimate quoted in the **proof of Lemma A.3** of [Lemke Oliver–Thorner, Appendix A to Pasten, arXiv:1705.09251v4](https://arxiv.org/pdf/1705.09251v4): over the fixed field, for a primitive nonprincipal finite-order character,

$$
|L(\sigma+it,\chi)|
\ll_\varepsilon
\left(q_{\mathfrak f}(1+|t|)^{[F:\mathbb Q]}\right)^{(1-\sigma+\varepsilon)/2},
\qquad -\varepsilon\le\sigma\le1+\varepsilon.
$$

Lemma A.3's displayed smoothed mean, already used in (G5), has $\sigma=1/2$; it is not being cited as a $1/6$-line mean. Here Mellin inversion of the exact sixth-free series permits the different line $\sigma=1/6+\varepsilon$: the numerator is entire and the inverse denominator is absolutely convergent throughout the shift. The annular profile's Mellin decay pays the polynomial height cost. Thus the complete kernel satisfies

$$
|\mathcal K_{U,\Omega}(a,b)|
\ll U^{1/6+\varepsilon}q_{\mathfrak f}^{5/12+\varepsilon}
\ll U^{1+\varepsilon}q_h^{-5/6}.
$$

Fixed ray Fourier coefficients, all zero-only factors and the required finite profile derivatives are included in the same fixed or polylog cost contract. This argument is applied to the complete row sum, never inside an adaptive zero bin.

**Large pair-gcds are paid absolutely.** The original annuli give $q_a,q_b\asymp U$, and the divisor envelope of $g_D$ gives $|g_D(a)|\ll U^{-1/2+\varepsilon}$. At a fixed ideal $h$ there are at most $O((U/q_h)^2)$ ordered pairs. Consequently, for $1\le G\ll U$,

$$
\begin{aligned}
\sum_{\substack{r_2(a)\ne r_2(b)\\q_{(a,b)}\ge G}}
 |g_D(a)\overline{g_D(b)}\mathcal K_{U,\Omega}(a,b)|
&\ll U^{2+\varepsilon}\sum_{q_h\ge G}q_h^{-17/6}\\
&\ll U^{2+\varepsilon}G^{-11/6}.
\end{aligned}
$$

The same bound holds with $g_{\le T}$ in both coefficient occurrences, through its unchanged pointwise envelope. The last sum uses ordinary ideal counting. At $G=U^{1/2}$ its exponent is $13/12$, strictly below $B_*$ by

$$
\delta_c=B_*-\frac{13}{12}
=\frac{49-20\sqrt6}{12}>0,
\qquad 49^2=2401>2400=20^2\cdot6.
$$

This cut partitions an ordered signed sum directly; it does not truncate a column vector or discard interference, and needs no further Hilbert square-root loss.

**The unpaid head can be restricted to long primitive conductors.** In the preceding head put $T=U^\theta$, and write the two columns as $a=s_at_a^2$, $b=s_bt_b^2$ with $q_{t_a},q_{t_b}\le T$. Cube-freeness gives the conductor lower bound

$$
q_{\mathfrak f}\gg_S
\frac{q_aq_b}{q_h^2q_{t_a}q_{t_b}}
\gg \frac{U^{2-2\theta}}{q_h^2}.
$$

Indeed, $xy$ is cube-free and its squarepart divides $t_at_b$, so $q_{\operatorname{rad}(xy)}\ge q_{xy}/(q_{t_a}q_{t_b})$. Hence pairs with $q_{\mathfrak f}\le U^{1+\eta}$ have $q_h\gg U^{1/2-\theta-\eta/2}$. The absolute bound above pays their entire contribution by

$$
\left|E_{6,\,q_{\mathfrak f}\le U^{1+\eta}}^{\mu,\le T}\right|
\ll U^{13/12+11\theta/6+11\eta/12+\varepsilon}.
$$

Here $\eta\ge0$ and $\theta>0$ are fixed with

$$
\frac{11\theta}{6}+\frac{11\eta}{12}<\delta_c.
$$

Thus a sufficient remaining input is only

$$
\operatorname{Re}E_{6,\,q_{\mathfrak f}>U^{1+\eta}}^{\mu,\le T}
\ll U^{B_*-\nu+\varepsilon},
\qquad
0<\nu<\min\left\{\frac\theta{50},\,
\delta_c-\frac{11\theta}{6}-\frac{11\eta}{12}\right\}.
$$

Its conductor cut is defined separately in each fixed finite ray character component; these components are then summed coherently. The same source, coefficient signs, all squarefree columns and original collision zeros remain. With this unproved input, the paid lower-order block, low-conductor sum and preceding truncation error would give the full inverse-fourth exponent $B_*-\nu$, and hence the existing complete-energy consumer at $\kappa_{\rm joint}-\nu/2$. No such long-conductor estimate is supplied. This application narrows that missing input; it neither improves the full moment on its own nor restores the signed Robin expression. Classical convexity, Euler products, conductor identities and ideal counting are reused, with no analytic Lean certification or literature-priority claim.

## Retaining the conductor cap with Hecke subconvexity

The same original low-conductor sub-sum admits a stronger bound by reusing a uniform Hecke subconvexity theorem and retaining its conductor cap during summation. Fix $F=\mathbb Q(\sqrt{-3})$. Suppose that for all unitary Hecke characters of $F$ one has

$$
|L(1/2,\chi)|\ll_{F,\varepsilon} C(\chi)^{c+\varepsilon},
\qquad 0\le c\le1/4,
$$

with the constant independent of the character and its analytic conductor. Han Wu, [*Burgess-like subconvexity for GL1*, Theorem 1.1, arXiv:1604.08551v6](https://arxiv.org/html/1604.08551v6), published with [DOI 10.1112/S0010437X19007309](https://doi.org/10.1112/S0010437X19007309), supplies

$$
c=\frac14-\frac{1-2\theta_{\rm RP}}{16}.
$$

The paper's character convention is unitary. Blomer–Brumley, [*On the Ramanujan conjecture over number fields*, Theorem 1 and Hypothesis $H_n(\delta)$, arXiv:1003.0559v4](https://arxiv.org/abs/1003.0559v4), [DOI 10.4007/annals.2011.174.1.18](https://doi.org/10.4007/annals.2011.174.1.18), gives $\theta_{\rm RP}=7/64$ over any number field and at every place, including the complex place here. The totally-real restriction in its following twisted-GL2 application is not a restriction on Theorem 1. Thus an unconditional published input is

$$
c=\frac{103}{512},\qquad \alpha=\frac{1+c}{3}=\frac{205}{512}.
$$

**Transport to the complete row kernel.** Applying the central bound to $\chi|\cdot|^{i\tau}$ controls the whole central vertical line, with

$$
C_\tau\asymp_F q_{\mathfrak f}(1+|\tau|)^2.
$$

Interpolate between $\Re s=1/2$ and the absolutely convergent line $1+\varepsilon$ to obtain the exponent $c/3+\varepsilon$ at $5/6+i\tau$. The functional equation then gives

$$
|L(1/6+i\tau,\chi)|
\ll_{F,\varepsilon} C_\tau^{\alpha+\varepsilon},
\qquad \alpha=\frac13+\frac c3.
$$

This uses a bound on the entire central line before interpolation, rather than interpolating an isolated central value leftwards. Apply it on the same $1/6+\varepsilon$ Mellin line to the exact imprimitive ratio $L(s,\chi_0)/L(6s,\chi_0^6)$ above. The nonprincipal primitive numerator has no pole to cross, the inverse denominator is absolutely bounded there, and every original collision zero and zero-only Euler factor is retained. Mellin decay absorbs the polynomial height cost, giving

$$
|\mathcal K_{U,\Omega}(a,b)|
\ll U^{1/6+\varepsilon}q_{\mathfrak f}^{\alpha+\varepsilon}.
$$

The original finite ray components and required profile derivatives obey the same fixed or polylog cost contract. This does not enlarge its growing-height range or insert a complete-row argument inside an adaptive bin.

The unchanged coefficient envelope and pair count give, for $1\le G\ll U$,

$$
\begin{aligned}
\sum_{\substack{r_2(a)\ne r_2(b)\\q_{(a,b)}\ge G}}
 |g_{\le T}(a)\overline{g_{\le T}(b)}\mathcal K_{U,\Omega}(a,b)|
&\ll U^{7/6+2\alpha+\varepsilon}
 \sum_{q_h\ge G}q_h^{-2-2\alpha}\\
&\ll U^{7/6+2\alpha+\varepsilon}G^{-1-2\alpha}.
\end{aligned}
$$

**Keep both conductor bounds in the low head.** Put $Q=U^{1+\eta}$, $T=U^\theta$, with $\eta\ge0$, $\theta>0$ and $\theta+\eta/2<1/2$. The preceding conductor lower bound restricts the low head to $q_h\gg H_0$, where

$$
H_0=U^{1/2-\theta-\eta/2},\qquad
H_1=U^{1/2-\eta/2}.
$$

Keep the actual upper bounds together:

$$
q_{\mathfrak f}^{\alpha}
\ll \min\{Q,(U/q_h)^2\}^{\alpha}.
$$

Ordinary ideal counting in the two ranges $H_0\ll q_h\le H_1$ and $q_h\ge H_1$ gives

$$
\begin{aligned}
\left|E_{6,\,q_{\mathfrak f}\le Q}^{\mu,\le T}\right|
&\ll U^{7/6+\varepsilon}
 \left(Q^\alpha\sum_{H_0\ll q_h\le H_1}q_h^{-2}
       +U^{2\alpha}\sum_{q_h\ge H_1}q_h^{-2-2\alpha}\right)\\
&\ll U^{7/6+\varepsilon}
 \left(Q^\alpha H_0^{-1}+U^{2\alpha}H_1^{-1-2\alpha}\right)\\
&\ll U^{2/3+\alpha+\theta+(1/2+\alpha)\eta+\varepsilon}.
\end{aligned}
$$

Fixed conductor-comparison constants only move the two cutoffs by fixed factors. The coefficient of $\theta$ is now $1$ because the conductor cap was kept inside the sum; this improvement does not depend on subconvexity. With convexity alone, $\alpha=5/12$, the same cap gives $13/12+\theta+11\eta/12$. The additional decrease in $\alpha$ is supplied by Wu and Blomer–Brumley, not by a new subconvexity theorem here.

For their published input, the low-head exponent is

$$
\frac{1639}{1536}+\theta+\frac{461}{512}\eta.
$$

In particular, take

$$
\theta=\frac1{1000},\quad \eta=\frac1{100},\quad
H_0=U^{247/500},\quad H_1=U^{99/200}.
$$

Then the same original low-conductor contribution satisfies

$$
\boxed{
\left|E_{6,\,q_{\mathfrak f}\le U^{101/100}}^{\mu,\le U^{1/1000}}\right|
\ll U^{827183/768000+\varepsilon}.
}
$$

Here $827183/768000=1.077061197916\ldots$ and

$$
\frac{13}{12}-\frac{827183}{768000}
=\frac{4817}{768000}>0,\qquad \frac{13}{12}<B_*.
$$

Thus the missing sufficient input can be restricted to

$$
\operatorname{Re}E_{6,\,q_{\mathfrak f}>U^{101/100}}^{\mu,\le U^{1/1000}}
\ll U^{B_*-\nu+\varepsilon},
\qquad \nu=\frac1{100000}.
$$

This $\nu$ is below both the low-head margin and the existing truncation margin $\theta/50=1/50000$. The remaining sum retains its actual Möbius coefficients, original zeros, all squarefree columns, the $t=1$ packet and coherent finite components. Its estimate is not supplied. The controlled portion of the original head is larger; the full inverse-fourth exponent, complete-energy improvement and signed Robin restoration remain unproved. This is a source-conditional application of the cited analytic results, without Lean certification or a literature-priority claim.

**Stronger printed input.** Yang, [*Relative Trace Formula and Twisted L-functions: the Burgess Bound*, arXiv:2305.10719v1, Corollary 1.2(1.3)](https://arxiv.org/html/2305.10719v1), states the uniform Hecke exponent $c=3/16$. Substitution into the same calculation would give $\alpha=19/48$ and the low-head exponent $17/16+\theta+43\eta/48$. The numerical bound above does not depend on this stronger preprint input. Its Hypothesis 2.1 uses $c_vT_v\le|\gamma_{j,v}|\le C_vT_v$, without $1+|\gamma_{j,v}|$, while subsequent estimates use negative powers of $T_v$. For $\pi=1\boxplus1$ and trivial infinite-type $\chi$, both local parameters vanish. The compact zero-parameter specialization, and the complex-place normalization of $T_v$ relative to analytic conductor, are not independently reconciled here; this is not a refutation of the printed corollary. Yang's [*Symmetric Spectral Reciprocity for GL(2) and Uniform Subconvexity*, arXiv:2607.04476v1](https://arxiv.org/html/2607.04476v1), Theorem B and Corollary 1.4 concern cuspidal GL2, and its Lemma 10.2 invokes the earlier Corollary 1.2. They do not give an independent replacement for the GL1 input used here.

## Using the global strip in the complete row kernel

The complete-row kernel can also use the **upper** global $L$-bound, rather than only the reciprocal bound already used for inverse polynomials. This gives a larger controlled conductor range under the cited zero-free supply. Fix $\beta=7/8$ using the main theorem and `lem:logarithmic-control` of the [pinned OpenAI primary manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex). For every fixed $v>0$, that lemma supplies both $L$ and $1/L$ with analytic-conductor subpower growth on $\Re s\ge\beta+v$ for nonprincipal finite-order Hecke characters. Its principal reciprocal assertion is for $1/\zeta_F$; its principal upper bound is only for the regularized function. These are reused source inputs, not independently Lean-certified results here.

**Move the complete kernel, with buffers.** Keep the exact $\chi_0$, original collision zeros and complete row family from the preceding kernel construction. Put

$$
b=\beta+v,\qquad \sigma=\beta/6+d,
\qquad v,d>0,
\qquad \frac12<1-\sigma<b<1.
$$

On the entire central line, reuse Wu and Blomer–Brumley's exponent $c=103/512$. On the right line $b$, the nonprincipal primitive numerator has the global upper bound $L(b+i\tau,\chi)\ll C_\tau^\varepsilon$, where $C_\tau\asymp_F q_{\mathfrak f}(1+|\tau|)^2$. Phragmén–Lindelöf interpolation between these two full vertical lines, followed by the primitive functional equation, gives

$$
\begin{aligned}
|L(1-\sigma+i\tau,\chi)|
&\ll C_\tau^{c(\sigma+b-1)/(b-1/2)+\varepsilon},\\
|L(\sigma+i\tau,\chi)|
&\ll C_\tau^{\alpha(\sigma,b)+\varepsilon},\\
\alpha(\sigma,b)
&=\frac12-\sigma+
 c\frac{\sigma+b-1}{b-1/2}.
\end{aligned}
$$

The source's polynomial strip growth supplies the interpolation growth condition. The numerator remains nonprincipal by the surviving good-prime component proved above. Thus no principal upper bound or pole removal for that numerator is being assumed.

In the exact ratio $L(s,\chi_0)/L(6s,\chi_0^6)$, the primitive character inducing $\chi_0^6$ belongs to the same finite-order family. After the fixed ray expansion it can be nonprincipal; its good-prime components are principal and its remaining primitive conductor is supported in the fixed finite data. The global reciprocal bound applies on the whole contour deformation because $\Re(6s)\ge\beta+6d>\beta$. If the primitive denominator is principal, its pole at $6s=1$ is a removable zero of the reciprocal and contributes no residue. Every imprimitive numerator and reciprocal-denominator Euler factor is retained. Their finite products cost $U^\varepsilon$ on this fixed positive strip, including the original zero-only primes. Consequently Mellin inversion and the same profile decay give

$$
|\mathcal K_{U,\Omega}(a,b)|
\ll U^{\sigma+\varepsilon}
q_{\mathfrak f}^{\alpha(\sigma,b)+\varepsilon}.
$$

This is still a complete-row argument, not a deletion of selectors inside an adaptive zero bin. Required profile derivatives and fixed or specified polylog height costs obey the previous contract; no larger growing-height range is asserted.

For each final loss, choose $v,d$ sufficiently small and fixed before the Mellin decay order. The limiting values are

$$
\sigma_0=\frac7{48},\qquad
\alpha_0=\frac{17}{48}+\frac c{18}
=\frac{3367}{9216}.
$$

Thus the kernel bound can be written $U^{\sigma_0+\varepsilon}q_{\mathfrak f}^{\alpha_0+\varepsilon}$. Neither the boundary line $6\Re s=\beta$ nor an unbuffered global $L$-bound is used.

**Reuse the conductor-cap sum.** For the same $Q=U^{1+\eta}$, $T=U^\theta$, $H_0=U^{1/2-\theta-\eta/2}$ and $H_1=U^{1/2-\eta/2}$, replace the previous kernel exponents by $\sigma_0,\alpha_0$. The unchanged coefficient envelope, pair count and retained cap give

$$
\begin{aligned}
\left|E_{6,\,q_{\mathfrak f}\le Q}^{\mu,\le T}\right|
&\ll U^{1+\sigma_0+\varepsilon}
 \left(Q^{\alpha_0}H_0^{-1}
       +U^{2\alpha_0}H_1^{-1-2\alpha_0}\right)\\
&\ll U^{r(\theta,\eta)+\varepsilon},\\
r(\theta,\eta)
&=\frac12+\sigma_0+\alpha_0+\theta+
 (\tfrac12+\alpha_0)\eta\\
&=1+\frac{103}{9216}+\theta+
 \frac{7975}{9216}\eta.
\end{aligned}
$$

Choose

$$
\theta=\frac1{1000},\qquad \eta=\frac2{25},\qquad
H_0=U^{459/1000},\qquad H_1=U^{23/50}.
$$

Then

$$
\boxed{
\left|E_{6,\,q_{\mathfrak f}\le U^{27/25}}^{\mu,\le U^{1/1000}}\right|
\ll U^{415259/384000+\varepsilon}.
}
$$

The exponent is $1.081403645833\ldots$, with

$$
\frac{13}{12}-\frac{415259}{384000}
=\frac{247}{128000}>0,
\qquad \frac{13}{12}<B_*.
$$

Therefore the missing sufficient head input is narrowed further to

$$
\operatorname{Re}E_{6,\,q_{\mathfrak f}>U^{27/25}}^{\mu,\le U^{1/1000}}
\ll U^{B_*-\nu+\varepsilon},
\qquad \nu=\frac1{100000}.
$$

This reserve is below both the displayed low-head margin and the previous truncation margin $1/50000$. The new bound pays the original conductor range through $U^{27/25}$ under the cited global-strip supply. The remaining contraction still has its actual Möbius coefficients, all original zeros, finite components, squarefree columns and $t=1$ packet. Its bound is not supplied. This is a source-conditional application of existing strip control, subconvexity, functional equations and the already derived cap sum; it is not a new general $L$-function theorem, a full inverse-fourth improvement, a signed Robin restoration or an RH proof. No literature-priority or local analytic Lean-certification claim is made.

## Fixed-order first moments and the unresolved head

Gao–Zhao, [*First moment of central values of Hecke L-functions with Fixed Order Characters*, arXiv:2306.10726v3](https://arxiv.org/html/2306.10726v3), revised 1 December 2025, provides a nearby double-Dirichlet-series input. Its Theorem 1.3 is unconditional for $j=3,6$ over $K=\mathbb Q(\sqrt{-3})$ and $j=4$ over $\mathbb Q(i)$. It concerns a smoothed first moment of $L(1/2+\alpha,\chi\chi_j^{(n)})$, averaged over the fixed ray characters and all nonzero elements $n$, with

$$
0<\Re\alpha<1/2.
$$

The family is not restricted to squarefree or sixth-power-free parameters and its characters need not be primitive. For $j=6$ the reported error exponent is $2/3-\Re\alpha+\varepsilon$. This is a signed first $L$-value moment, not an upper bound for a positive inverse fourth moment with the actual Möbius polynomial. The quadratic GRH assumptions elsewhere in the paper should neither be attached to this theorem nor discarded when citing those separate quadratic results.

**The fixed-twist scope must remain fixed.** Lemma 2.13 assumes a fixed Hecke twist $\chi$ of trivial infinite type modulo $q$, with $N(q)\le M$, and states its $L$-value mean with an implicit constant $\ll_M$. For $j\ge3$, Lemma 2.14 defines

$$
h_j(r,s;\chi)
=\sum_{m\ {\rm primary}}
\frac{\chi(m)g_K(r,\chi_{j,m})}{N(m)^s}
$$

under the explicit assumptions that the norm of the modulus of $\chi$ is bounded and that $\chi(m)=0$ whenever $\chi_{j,m}$ is undefined. With $\sigma_1=3/2+\varepsilon$ and $\sigma_1-1/2\le\sigma=\Re s\le\sigma_1$, its bound is

$$
\left|\big((j(s-1))^2-1\big)h_j(r,s;\chi)\right|
\ll
N(r)^{(\sigma_1-\sigma+\varepsilon)/2}
(1+|s|^2)^{(\sigma_1-\sigma+\varepsilon)(j-1)/2}.
$$

The displayed $N(r)$ dependence concerns the additive Gauss numerator. It does not specify dependence on a growing conductor of $\chi$. The paper traces this lemma to Patterson's lemma on p.200 and proof on p.205; this citation alone supplies no conductor-uniform estimate. Consequently a fixed-twist bound cannot be used uniformly over the long primitive pair conductors above by hiding their growth in its implicit constant. This limitation of the printed statement does not exclude deriving a conductor-indexed bound from the underlying arguments.

**The v3 main-term normalization requires clarification.** Put $w=1/2+\alpha$, let $S=S_{K,j}$ be the paper's fixed ray modulus, and write

$$
R_j(w)=\frac{r_K}{\#h_{(S)}}
\sum_{\chi\bmod S}\frac{L(jw,\chi^j)}{L(1+jw,\chi^j)}.
$$

Theorem 1.3, display (1.5), prints the leading term $X\widehat\Phi(1)R_j(w)$. However, the same paper's display (3.10) gives

$$
\operatorname{Res}_{s=1}A_j(s,w)=|U_K|R_j(w).
$$

The definition of $A_j$ in (3.2) and the Mellin identity (3.4) use the same all-nonzero-element sum and the same ray average as (1.5). The paper explicitly defines $r_K=\operatorname{Res}_{s=1}\zeta_K(s)$; this is not a unit-averaged residue. The ideal/primary-generator convention for the inner $L$-series in (3.1) does not insert a unit average into that outer element sum. Thus the two displayed leading coefficients differ by $|U_K|$, which is six in the Eisenstein case. The difference occurs in the primary TeX and [PDF, pp.3 and 14](https://arxiv.org/pdf/2306.10726v3), as well as the HTML. This note does not select a repaired theorem or adopt the unresolved exact main-term constant.

**Application boundary.** Directly matching the existing kernel's $L$-argument $w=1/6+\delta$, $0<\delta<1/3$, would require $\Re\alpha=-1/3+\delta<0$, outside Theorem 1.3. The missing head also retains its actual Möbius coefficients, natural collision zeros and coherent finite components, and includes primitive pair-conductor norm exceeding $U^{1+\eta}$. Neither a first-moment identity nor fixed-modulus Gauss continuation supplies that joint estimate. The already recorded sufficient inverse-fourth target remains $B<B_*=(31-10\sqrt6)/6$; this source comparison gives no improvement to $B$, complete Robin bound or Lean certification.

## Mollified central moments retain a shorter inverse length

The relevant literature already treats mollified higher-order Hecke moments.
Its central-value observable, field hypothesis and mollifier range must be
retained before attempting to use it for the actual $M_\xi S_\xi$ moment.

**The existing cubic supplier.** David–de Faveri–Dunn–Stucky,
[*Non-vanishing for cubic Hecke $L$-functions*, arXiv:2410.03048v3](https://arxiv.org/html/2410.03048v3#S1.SS2),
equations (1.26)–(1.27) and the following mollifier-length discussion,
obtain an unconditional second mollified central-moment asymptotic with
mollifier length $M\le X^{1/6-\delta}$ for fixed $\delta>0$. This is the
squarefree cubic row family over the Eisenstein field. The cubic sieve
and Gauss-series moments already used in the
[fixed-order note](faveri2026fixedorder.md) remain reused inputs. The
mollifier discussion supplies neither a sixth-order row theorem nor the
balanced inverse length $D=\sqrt U$. Güloğlu–Yeşilyurt,
[*Mollified moments of cubic Dirichlet $L$-functions over the Eisenstein field*,
arXiv:2301.10979v3](https://arxiv.org/abs/2301.10979v3), published with
[DOI 10.1016/j.jmaa.2023.128014](https://doi.org/10.1016/j.jmaa.2023.128014),
obtain their higher mollified moments under GRH; their unconditional
first mollified moment does not replace that assumption.

**A general-order source.** Diaconu–Ion–Paşol–Popa,
[*On the second moment and non-vanishing of central values of Hecke
$L$-functions of $r$-th order characters*, arXiv:2607.27131v1](https://arxiv.org/html/2607.27131v1),
Theorem 10.5.2, gives twisted second central moments for both squarefree
rows ($\kappa=1$) and $r$-th-power-free rows ($\kappa=0$). The latter
retains the positive local weight
$Q_{\mathfrak a}=\prod_{\mathfrak p\mid\mathfrak a}v_{\mathfrak p}(\mathfrak a)$;
the family is ordered by ideal norm rather than primitive conductor.
The stated standing hypothesis in §1.1.1 and §2.1 is that the number
field contains $\mu_{2r}$. For $r=6$, the current field
$\mathbb Q(\sqrt{-3})$ does not satisfy that hypothesis. No extension
removing it or transport from a larger number field is used here.
Sections 1.4.1 and 4.1.8 explicitly discuss relaxing this premise through
additional technical work; this leaves an extension to verify rather
than a general obstruction.

Even within a field allowed by that theorem, its published mollifier
range is shorter than the required balanced length. Section 10.6,
equation (38) and Proposition 10.6.3, give

$$
\theta_\kappa=
\frac{1-\widetilde\delta_\kappa}
 {1+(2r-1)(1-\widetilde\delta_\kappa)},
\qquad M=X^{\theta_\kappa-\varepsilon}.
$$

For $r=6$ the source parameters specialize to

| Row family | $\widetilde\delta_\kappa$ | $\theta_\kappa$ |
|---|---|---|
| Squarefree, $\kappa=1$ | $13/14$ | $1/25$ |
| Sixth-power-free, $\kappa=0$ | $8/11$ | $3/44$ |

Section 10.1, equation (29), already preserves primes used solely for
zero extension when reducing a twist: a vanished residue exponent is
replaced by exponent $r$ at that prime. Its collision zeros must be
reused, rather than reported as missing from this central-moment source.

The coefficient normalization itself need not be an obstruction. In the
source's convention the mollifier is
$\sum_{\mathfrak b}\lambda_{\mathfrak b}q_{\mathfrak b}^{1/2}
\chi_{\mathfrak a}(\mathfrak b)$ with
$\lambda_{\mathfrak b}\ll q_{\mathfrak b}^{-1+\varepsilon}$.
For the current annular inverse factor the candidate coefficients are

$$
\lambda_{\mathfrak b}
=D^{-1/2}\mu(\mathfrak b)\xi(\mathfrak b)
 V(q_{\mathfrak b}/D)q_{\mathfrak b}^{-1/2}.
$$

On its fixed annulus this satisfies the same coefficient envelope.
The source takes real mollifier coefficients; for a positive upper
bound, split a complex candidate into its real and imaginary coefficient
sequences, with at most a fixed factor two.
The actual support still has length $D$, however; setting $X=U$ and
$D=\sqrt U$ does not fit either displayed mollifier range. The published
absolute summation of its twisted error has envelope

$$
X^{\widetilde\delta_\kappa+\varepsilon}
 M^{1+(2r-1)(1-\widetilde\delta_\kappa)+\varepsilon}.
$$

At the formal balanced substitution $r=6$, $M=\sqrt X$, its exponents
are $51/28$ for $\kappa=1$ and $30/11$ for $\kappa=0$. These are
exponents of an available error bound, not lower bounds for the actual
mollified moments. Retaining additional cancellation in this error
would require another estimate.

There is also an observable to transport: a bound for
$|L^S(1/2,\chi_{\mathfrak a})\mathcal M(\mathfrak a)|^2$ does not by
itself bound the arbitrary annular polynomial product
$|M_\xi S_\xi|^2$. A central value combines the approximate-functional-
equation pieces, which can cancel. No positive domination of each
individual piece follows by deleting the others.

McGoldrick's [*Distribution of central values of Hecke $L$-functions of
$n$-th order characters*, arXiv:2610.17144v1](https://arxiv.org/html/2610.17144v1),
Theorems 1.1–1.2, reuses the general-order twisted moment to obtain an
upper-tail central limit bound and positive moments of order $2k$,
$0<k<1$, on a squarefree family with the same $\mu_{2n}$ field premise.
It supplies no inverse fourth moment or estimate of the present signed
mixed polynomial. These are external analytic inputs with explicit
application limits, not a new mixed-moment bound, an impossibility
result, a Robin proof or Lean certification.

## Reusing the global ordinary-source frontier

At the immutable [QuasiRiemannTracker snapshot `0ce80fdddebb03128d30a917006d8520e7a774b8`](https://github.com/GTimG/QuasiRiemannTracker/tree/0ce80fdddebb03128d30a917006d8520e7a774b8), the merged submissions [Collet #69](https://github.com/GTimG/QuasiRiemannTracker/pull/69) and [Lewko #70](https://github.com/GTimG/QuasiRiemannTracker/pull/70) state stronger boundaries than the Gao value compared above:

| Source | Stated zero-free boundary | Pinned endpoint declaration |
|---|---|---|
| Hailey Collet, *A zero-free half-plane from finite ordinary source moments* | $8747729897/10^{10}=0.8747729897$ | [`QRH.Record1252270103Source.Endpoint.beta_bound`](https://github.com/GTimG/QuasiRiemannTracker/blob/0ce80fdddebb03128d30a917006d8520e7a774b8/submissions/hailey-collet-1252270103/src/Submissions/hailey_collet_1252270103/Record1252270103Source/Core/Endpoint.lean) |
| Mark Lewko, *An acyclic ordinary-source refinement targeting the Dirichlet boundary 0.874772906* | $437386453/500000000=0.874772906$ | [`Lewko.QRH.Endpoint.family_beta`](https://github.com/GTimG/QuasiRiemannTracker/blob/0ce80fdddebb03128d30a917006d8520e7a774b8/submissions/lewko-acyclic-bootstrap-874772906/src/Submissions/lewko_acyclic_bootstrap_874772906/Lewko/QRH/Endpoint.lean) |

Both displayed declarations concern the full relevant finite-order Hecke zero supremum, not only its Dirichlet consequence. Their associated nonvanishing statements use a strict half-plane and exclude the principal pole; the Dirichlet consequences cover every positive modulus. Lewko reuses Collet's ordinary-source machinery in two acyclic parameter steps and explicitly describes the result as a parameter refinement. These are cited external source statements: merged tracker status is observed, but this repository has not built either external Lean development or independently certified its analytic proof. The table is a comparison at the pinned snapshot, not a claim that all later literature has been searched.

**The reusable source is genuinely global in its length domain.** Collet's [primary paper](https://github.com/rohanarun/quasi-rh-hillclimb/tree/594fc4838e9c92d5a16bedf270d07d1f51161be7/submissions/hailey-collet-1252270103/paper), Chapter 28, (G1), states the ordinary initial moment $G(B,\Lambda,h)$ on

$$
m_1,m_2\ge0,\qquad 0\le s\le h,\qquad
m_1+m_2+\Lambda s\le B.
$$

There are no separate lower plain-length edges. The corresponding [`GlobalSource`](https://github.com/GTimG/QuasiRiemannTracker/blob/0ce80fdddebb03128d30a917006d8520e7a774b8/submissions/hailey-collet-1252270103/src/Submissions/hailey_collet_1252270103/Record1252270103Source/Core/Contract.lean) is the literal `UniformUnitFaceSource` with `globalFace B lam cap`; its admissibility and coordinatewise-shortening interfaces are already supplied there. The natural $B=1$ face admits $m_1=m_2=1/2$, $s=0$. The earlier Gao individual-length window therefore cannot be used to reject this newer source. Its mesh precedes the finite slot type and moving arithmetic data; finite controls, polynomial height degree and constant precede the ambient scale and live profiles. Reuse must preserve that order and the allowed ray/anchor data.

**Length admissibility does not change the coefficients.** In the paper's literal row, (158)--(161), write $c_z(I)=\eta(I)\chi_{m^6Az}(I)$, including natural zeros, and

$$
L_z(p,X;t)=\sum_{I\ne0}c_z(I)q_I^{it}p(q_I/X),
\qquad
\mathscr R_z=(X_1X_2)^{-1/2}
 L_z(p_1,X_1;t)L_z(p_2,X_2;t)\prod_j A_j(z).
$$

The $A_j$ are the source's normalized marked prime polynomials with their actual relative coefficients. The estimated energy is

$$
\sum_{z:\,\operatorname{initialKeep}(z)}
 |\mathscr R_z|^2\operatorname{Re}\Phi(q_z/U)
\ll U^{1+\varepsilon}\mathcal H,
$$

with its stated radial, profile and height controls $\mathcal H$. It retains all six units, sixth-power repetitions, fixed-inducing exclusions and root-relative holes. Both ideal sums $L_z$ are ordinary: neither contains $\mu(I)$. With no prime slots and two equal plain factors, the normalized fourth-moment exponent is $U^{1+\varepsilon}$. This is already the exponent used in [(458.8)](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#458-möbius-自卷积与无槽四矩的完整原系数预算); it is not a new improvement to that input. In particular, no extra power of $X_1X_2$ may be gained by comparing normalized and unnormalized sums. Fixed-inducing rows cannot be restored merely by deleting `initialKeep` from the displayed bound.

**The supplied coefficient transport is squarefree-total-product transport.** Chapter 25 proves the exact two-variable kernels between the ordinary pair and its restriction $\mu^2(I_1I_2)$:

$$
h_{\mathfrak p}(X,Y)=(1-X)(1-Y)(1+X+Y)
=1-X^2-XY-Y^2+X^2Y+XY^2,
\qquad k_{\mathfrak p}=h_{\mathfrak p}^{-1}.
$$

Both have no degree-one monomial. The source already proves their subpower absolute central mass and transports the completed positive norm by Minkowski, shortening both actual lengths and retaining common punctures. These identities, mass bounds and domain transport should be reused directly; they are not new coefficient lemmas here. They do not replace either factor by a Möbius polynomial. The paper explicitly excludes treating arbitrary bounded coefficient multiplication as contraction of the quadratic energy.

For comparison, the local quotient needed to change the first ordinary factor to $\mu(I_1)$ is

$$
\frac{(1-X)/(1-Y)}{1/((1-X)(1-Y))}
=(1-X)^2=1-2X+X^2.
$$

For two Möbius factors it is $(1-X)^2(1-Y)^2$. Thus an absolute central divisor-kernel argument of the same kind encounters a degree-one prime contribution. Up to an inverse-factor scale $D$, its mass already includes

$$
2\sum_{q_{\mathfrak p}\le D}q_{\mathfrak p}^{-1/2}
\gg\frac{\sqrt D}{\log D},
$$

by the ordinary prime-ideal theorem over the fixed field, after deleting the fixed bad set. It cannot be absorbed into $U^\varepsilon$ for every $\varepsilon>0$ at $D=\sqrt U$. This is an algebraic comparison with the existing absolute-mass method, not a nonrepresentation theorem or an obstruction to a different transport retaining cancellation.

### Cost of absorbing the Möbius sign into Hecke phases

A different proposed transport is to express the actual Möbius coefficient as a mixture of ordinary Hecke twists. Its total variation cannot be treated as a subpower cost, even on the original $t=1$ packet. This is an application of the existing inverse-$L$ identity and zero-free input, not a new zero-free theorem or an actual-moment lower bound.

Fix a nonnegative, nonzero smooth annular profile $V$, and on good squarefree ideals put

$$
w_D(s)=A_D(s,1)=\sum_{ef=s}V(q_e/D)V(q_f/D),
\qquad W_D=\sum_s w_D(s).
$$

A fixed subinterval on which $V$ is bounded below, and the ordinary prime-ideal theorem applied to distinct prime ideals $e,f$ in that subinterval, give

$$
W_D\gg D^2/(\log D)^2.
$$

Let $\beta\in[1/2,1)$ be a uniform zero-free boundary for the finite-order Hecke family, with the reciprocal-strip control used above. For $\beta=7/8$, the inputs are the main theorem and `lem:logarithmic-control` of the [pinned OpenAI primary manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex). Its reciprocal statement includes the principal character. The analytic input is cited, not independently Lean-certified here.

Allow phases $\eta(a)=\eta_0(a)q_a^{it}$, where $\eta_0$ is a finite-order Hecke character covered by that input. Its conductor norm, any additional zero-extension modulus norm, and $|t|$ are at most $(\log D)^C$ for a fixed $C$. No nonzero angular infinite type or unrestricted moving conductor is included. The same $t=1$ double inverse-$L$ identity gives

$$
\begin{aligned}
R_D(\eta)&=\sum_s\mu(s)w_D(s)\eta(s)\\
&=\sum_{\substack{e,f\ {\rm squarefree}\\(e,f)=1}}
 \mu(e)\mu(f)V(q_e/D)V(q_f/D)\eta(ef),\\
\sup_\eta|R_D(\eta)|&\ll D^{2\beta+\varepsilon}.
\end{aligned}
$$

Indeed, the double Euler product is

$$
\prod_{\mathfrak p\notin S}
 (1-\eta(\mathfrak p)q_{\mathfrak p}^{-z}
    -\eta(\mathfrak p)q_{\mathfrak p}^{-w})
=\frac{\mathscr H(z,w;\eta)}{L_S(z,\eta)L_S(w,\eta)}.
$$

The correction $\mathscr H$ is the already used coprimality correction, bounded on fixed lines $\Re z,\Re w>1/2$; its reciprocal is not used. Moving both Mellin lines to $\beta+v$, with $v$ chosen within the final loss, gives the displayed bound. The cited global reciprocal strip supplies the height control, Mellin decay pays its polynomial costs, and all fixed exclusions and phase zero-only factors are retained. Polylog conductor and norm-twist costs are absorbed in $D^\varepsilon$.

Suppose a finite complex measure $\nu_D$ gives $r_D(s)=\int\eta(s)\,d\nu_D(\eta)$ on the support of $w_D$, and, for a fixed $0\le\rho<1$,

$$
\sum_s w_D(s)|r_D(s)-\mu(s)|\le\rho W_D.
$$

Pairing with $w_D(s)\mu(s)$ and interchanging a finite ideal sum with the measure integral gives

$$
(1-\rho)W_D
\le\left|\int R_D(\eta)\,d\nu_D(\eta)\right|
\le\|\nu_D\|_{\rm TV}\sup_\eta|R_D(\eta)|.
$$

Consequently, for every final $\varepsilon>0$,

$$
\boxed{\|\nu_D\|_{\rm TV}
\gg (1-\rho)D^{2-2\beta-\varepsilon}.}
$$

Exact coefficient transport is the case $\rho=0$. At $D=\sqrt U$, $\beta=7/8$, even fixed-relative-error transport requires $\|\nu_D\|_{\rm TV}\gg U^{1/8-\varepsilon}$. The original fixed factor $D^{-1}\xi(s)$ can be multiplied back into the coefficient representation; original row collision zeros then remain term by term. The approximate version is a coefficient-error statement and supplies no row-energy error estimate.

This rules out a particular black-box budget. Even granting a uniform ordinary squarefree-total-product energy bound $U^{1+\varepsilon}$ for every transported phase, applying only that bound and Minkowski produces the certificate $U^{1+\varepsilon}\|\nu_D\|_{\rm TV}^2$. A certificate with target exponent $B<B_*$ would require a total-variation exponent below $(B_*-1)/2=0.042091881\ldots$, whereas the necessary exponent is at least $1/8$. In general this template's coefficient-cost threshold is $3-2\beta$, equal to $5/4$ here. This is a limitation of the uniform-per-phase bound plus total variation, not a lower bound for the actual moment or for a norm-aware or cancellation-preserving transport. It does not rule out a joint phase estimate, a larger-cost phase family paid by another argument, or a direct estimate of the original long-conductor kernel. The full inverse-fourth and Robin estimates remain unpaid.

Consequently the newer source is available for its actual ordinary subenergies, while a transfer to $\sum_u\Omega|M_\xi S_\xi|^2$ or $\sum_u\Omega|M_\xi|^4$ remains unpaid. Merely substituting the smaller zero-free boundary also leaves the existing critical bin $a_*=(1+\delta_*)/2$, $\delta_*=(15-5\sqrt6)/6$, inside the allowed zero range, so it does not remove the maximum in (459.12). The small-gcd, long-conductor contraction specified above still requires a coefficient-sensitive estimate on the original object. The reusable literature advance is the stronger ordinary-source interface and endpoint; no full inverse-fourth improvement, strict Robin conclusion, analytic Lean certification or priority claim is supplied by this comparison.

## Actual-family finite measurements

The [reproducible experiment at `919b49399f8a256b2e313e4efeddafff37f0c757`](https://github.com/the-omega-institute/trureturing-experiments/tree/919b49399f8a256b2e313e4efeddafff37f0c757/docs/reports/sextic-inverse-fourth) evaluates the actual inverse fourth moment at $D=\sqrt U$, with trivial fixed ray twist, good ideals prime to 2 and 3, every sixth-power-free row in $U<q_u<2U$, all six unit multiples and the original collision zeros. It retains the stated smooth profiles, actual ideal Möbius coefficients, parity-core blocks and full interference. Its code, complete data and comparison definitions are in the private experiments repository; this note adds only their research interface.

Across five scales $U=256,1024,4096,16384,65536$, the program evaluates 158,322 physical rows. Its measured $E_6^\mu$ is approximately $-0.672730$ at $U=256$ and $45.893416$ at $U=65536$; the separately evaluated $t=1$ head also has both measured signs. At $U=65536$, the measured Möbius fourth moment is $2686.143572$, while replacing its signs by positive coefficients on the same squarefree support gives $2649.062665$. These finite observations do not support assuming a uniformly negative cross-core term or bounding the signed Möbius moment by the same-support positive-coefficient moment. Character arithmetic and collision tests use exact integers; profiles and moments use binary64 with independent scalar checks, not interval certificates. No uniform exponent, inverse-fourth improvement, strict Robin conclusion or RH proof follows. The missing analytic input remains an upper bound for the positive cross-core contribution with its actual coefficients, uniformly over the required original components and profiles.

## The length cost of a complete Kloosterman character channel

Blomer--Pascadi, [*Bilinear forms with Kloosterman sums via quadratic
characters*, arXiv:2607.24311v1](https://arxiv.org/pdf/2607.24311v1),
Theorem 1.1 and Remark 1.2, printed pp.1--2, supplies a uniform bound
for arbitrary complex coefficients on integer intervals. At lengths
$M=N\asymp\sqrt c$ its unnormalized Kloosterman matrix satisfies

$$
\left|\sum_{m\in I,n\in J}\alpha_m\beta_n S(am,n;c)
\mathbf1_{(m,n,c)=1}\right|
\ll c^{31/32+o(1)}\|\alpha\|_2\|\beta\|_2,
\qquad a\in(\mathbb Z/c\mathbb Z)^\times.
$$

This is a cited preprint estimate, not a local Lean-certified input.
There is an exact standard Gauss channel into this matrix, so lack of a
formal character identity alone is not the transfer obstacle. Its complete
length cost must also be retained. The calculation below is a repo-derived
method comparison using the cited theorem, with no priority claim or
estimate for the original inverse fourth moment.

**Keep the complete character channel.** Let $c>1$ and let $\kappa$ be a
primitive cubic Dirichlet character modulo $c$, extended by zero. Set
$e_c(x)=e^{2\pi ix/c}$, $\tau(\kappa)=\sum_{m\bmod c}\kappa(m)e_c(m)$ and
$G(\kappa)=\tau(\kappa)/\sqrt c$. With
$S(m,n;c)=\sum_{x\in(\mathbb Z/c\mathbb Z)^\times}e_c(mx+nx^{-1})$,
the primitive Gauss identity gives, for every integer $n$,

$$
\frac1c\sum_{m\bmod c}\kappa(m)S(am,n;c)
=G(\kappa)^2\overline\kappa(an).
$$

Indeed, opening $S$ makes the inner $m$-sum
$\tau(\kappa)\overline\kappa(ax)$. Substitution $y=x^{-1}$ in the remaining
sum gives $\tau(\kappa)\overline\kappa(n)$, including its zero value when
$(n,c)>1$. Thus the exact input vector is
$\alpha_m=\kappa(m)/c$, with
$\|\alpha\|_2=\sqrt{\varphi(c)}/c$. Its unit support automatically meets
the theorem's condition $(m,n,c)=1$. A known unit phase changes no norm;
a quadratic readout or prescribed zero mask in $n$ can remain in $\beta_n$.

**Charge its actual length before using the short-interval saving.** Grant
the additional favorable hypothesis that $n$ occupies an integer interval
of length $N\asymp\sqrt c$. Partition $0\le m<c$ into intervals $I_j$
of length at most $N$. Then

$$
\sum_j\|\alpha|_{I_j}\|_2
\le\sqrt{\lceil c/N\rceil}\frac{\sqrt{\varphi(c)}}c
\ll c^{-1/4}.
$$

The same quantity is at least
$\varphi(c)/(c\sqrt N)=c^{-1/4-o(1)}$: on each interval its $\ell^1$
norm is at most $\sqrt N$ times its $\ell^2$ norm, and the total $\ell^1$
norm is $\varphi(c)/c$. Consequently the norm cost in this blockwise
triangle procedure has this power, rather than an uncharged single-block
length. Applying the displayed Blomer--Pascadi estimate on each block
gives only

$$
\left|\sum_{n\in J}\beta_nG(\kappa)^2\overline\kappa(an)\right|
\ll c^{23/32+o(1)}\|\beta\|_2.
$$

The represented character channel already has the elementary bound
$\sqrt N\|\beta\|_2\ll c^{1/4}\|\beta\|_2$, since $|G(\kappa)|=1$.
The blockwise certificate is worse by $c^{15/32+o(1)}$. This compares
available bounds and the charged norm cost of this specified procedure;
it is not a lower bound for the signed sum or an obstruction to every
Kloosterman representation.

Additive Fourier transformation does not shorten this primitive channel:
$c^{-1/2}\sum_m\kappa(m)e_c(rm)=G(\kappa)\overline\kappa(r)$ has
$\varphi(c)=c^{1-o(1)}$ nonzero coordinates. Multiplicative Fourier
concentration instead returns the Gauss multiplier; the resulting operator
is no longer the short additive-interval matrix in Theorem 1.1.

**Original-object boundary.** The existing Gauss--Jacobi reduction,
including the conductor sign in
[Berg--Ryan--Young, Lemma 3.21](bergryanyoung2023sextictwists.md#the-source-already-supplies-the-sextic-gauss-factorization),
must be reused with its hypotheses. Even granting a reduction to the fixed
Dirichlet channel above does not provide the required original Hecke
aggregate: its ideal variables, pair-dependent primitive conductor,
Möbius convolution, quadratic readout and zero-only primes still require
one common estimate. The integer-interval hypothesis used in the comparison
has not been supplied for that aggregate. A useful further transport must
preserve cancellation over the complete channel, or supply genuinely short
separated inputs with a paid norm cost. The original $t=1$ long-conductor
sector, strict improvement below $B_*$ and signed Robin restoration remain
unpaid. No conclusion about RH follows from this method comparison.
