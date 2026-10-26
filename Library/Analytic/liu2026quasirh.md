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

The external manuscript by `span_of_dilates`, [*Structural ceilings in the cubic-theta quasi-Riemann-hypothesis argument*, v5](https://rstation.ai/problems/riemann_hypothesis/papers/40/v5), records two restrictions on specified modifications of the OpenAI/Liu argument. Its [primary text](https://rstation.ai/api/v1/papers/riemann_hypothesis_40/versions/5/download), Propositions A–B and §5, is the source for this section. These are literature results to reuse, not new repository theorems. The manuscript's introductory zero-free numbers do not replace the later tracker comparison above. No external Lean build or independent certification of its numerical tables is asserted here.

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

**The Gauss-source selection is already classified.** In v5, §5, Lemma G
and Proposition S, restrict to the source's sextic setting over
$\mathbb Q(\omega)$, with its primitive additive character, primary
representatives, good squarefree modulus and fixed bad-prime data. Write
$\gamma_j(c)=\tau(\chi_c^j)/\sqrt{q_c}$ for $j\not\equiv0\pmod6$.
The equivalence $\equiv$ allows multiplication by a unitary Hecke
character and a function of a fixed ray class. For integer exponents,
the supplied selection rule is

$$
\prod_i\gamma_{k_i}^{e_i}\equiv\mu
\quad\Longleftrightarrow\quad
K+3(E+1)\equiv0\pmod6,
\qquad E=\sum_i e_i,\quad K=\sum_i e_i k_i.
$$

For one cubic-theta source $\gamma_2$ and $k$ GL(1) Poisson duals
$\gamma_{4+3\tau_i}$, $\tau_i\in\{0,1\}$, **with no conjugate duals**,
this becomes $k\equiv1\pmod3$ and $k+\sum_i\tau_i$ even. Hence at most
three duals give only the existing single quadratically twisted sextic
dual. The next allowed cases have four duals. This classification
should be reused when selecting another probe, rather than inferred
from a numerical phase census.

The no-conjugate restriction matters here: the same source explicitly
allows $\gamma_2\overline{\gamma_1}^{\,2}\equiv\mu$ with two conjugate
duals. Neither that allowed product nor the selection rule estimates
its size, supplies the automorphic source, or pays the original
Möbius/plain or inverse-square contraction. In particular, the conjugate
pair in (C20) is outside the stated no-conjugate uniqueness class.
The FIB composition rotation $C=MJ$ and five Zeckendorf window states
are not identified with residue-character orders by this selection rule.

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

## Complete-dual estimates and the remaining head

The [complete-dual application note](../Fourier/liu2026quasirhdual.md) contains the
Möbius--Gauss transport, cubic coefficient interface (J4)--(J6),
all-row common-gcd estimate (J8), its cube-free low-repeat extension
(J11)--(J13), and the weighted all-core bound (J17), which pays
$P\ge U^{1/5}$ for actual Type-II coefficients without a repeat cutoff.
The direct whole-tail bound (J22) instead permits a repeat cutoff
$T=U^{1/12}$; retaining both core caps then pays $P\ge U^{1/6}$ by (J23).
The note records the sufficient aggregate small-$P$ targets
[(J15)](../Fourier/liu2026quasirhdual.md#truncate-before-the-positive-class-partition)
and [(J20)](../Fourier/liu2026quasirhdual.md#an-untruncated-sufficient-target-for-the-actual-type-ii-factor),
and the smaller-$P$, truncated actual-Type-II target
[(J24)](../Fourier/liu2026quasirhdual.md#a-direct-repeat-tail-and-a-smaller-sufficient-head).
None of these head estimates is supplied; the full inverse-fourth saving, signed Robin
restoration and RH remain open.

## Actual-family finite measurements

The [reproducible experiment at `919b49399f8a256b2e313e4efeddafff37f0c757`](https://github.com/the-omega-institute/trureturing-experiments/tree/919b49399f8a256b2e313e4efeddafff37f0c757/docs/reports/sextic-inverse-fourth) evaluates the actual inverse fourth moment at $D=\sqrt U$, with trivial fixed ray twist, good ideals prime to 2 and 3, every sixth-power-free row in $U<q_u<2U$, all six unit multiples and the original collision zeros. It retains the stated smooth profiles, actual ideal Möbius coefficients, parity-core blocks and full interference. Its code, complete data and comparison definitions are in the experiments repository; this note adds only their research interface.

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


## A larger conductor cut from exact gcd grouping

The [sixth-order operator supplier](faveri2026fixedorder.md#the-large-sieve-statement)
and the [sixth-power-free-row cubic supplier](faveri2026fixedorder.md#separating-the-lower-order-character-blocks)
can be applied before Poisson summation. Retaining a sharp conductor
selector as an operator mask, rather than taking absolute values of each
row kernel, gives a stronger low-conductor application. This reuses the
existing sieves and finite triangular truncation; it is not a new
large-sieve theorem or a full inverse-fourth improvement.

Work with the same complete positive row majorant used above, the actual
cube-free coefficient

$$
c(a)=g_{\le T}(a),\qquad q_a\asymp U,\qquad
|c(a)|\ll U^{-1/2+\varepsilon},
$$

and its original zero-extended characters. The implied constants retain
the same fixed or polylog profile and finite-data costs. The argument
applies afresh to this complete moment: no signed selector is removed
from an adaptive row bin. Let $E_6(c;Q)$ be its original ordered
unequal-parity contraction with the additional condition
$q_{\mathfrak f}\le Q$, using the primitive ratio conductor in each
original fixed row-Fourier component. These components are summed
coherently after the estimates. Then

$$
\boxed{
|E_6(c;Q)|\ll U^\varepsilon
\left(U+U^{5/6}T^{1/3}Q^{1/6}\right).
}
\tag{C1}
$$

Here the original annuli and finite data are fixed, $T,Q\ge1$, and the
normalization is the existing $D^{-1}$ in $g_D$ at $D=\sqrt U$.

**The sharp selector costs only logarithms.** The finite estimate needed
here is the elementary upper-bound form of classical triangular
truncation; see Kwapień--Pełczyński,
[*The main triangle projection in matrix spaces and its applications*](https://doi.org/10.4064/sm-34-1-43-67).
For a rectangular matrix $K$ and positive independent column keys
$k_i,l_j$, its staircase mask obeys

$$
\left\|\bigl(K_{ij}\mathbf1_{k_i l_j\le R}\bigr)_{ij}\right\|
\ll \log(2+N)\|K\|,
\tag{C2}
$$

where $N$ is the total number of row and column indices and the norms
are Euclidean operator norms. The required finite proof is short. Merge
the row keys $k_i$ and column thresholds $R/l_j$ in increasing order,
placing a row key before a tied threshold. In a balanced binary tree on
this list, each permitted pair has a unique node where its row is in
the left child and its column threshold is in the right child. At each
depth these rectangles have disjoint row supports and disjoint column
supports, so the corresponding sum of compressions of $K$ has norm at
most $\|K\|$. There are $O(\log(2+N))$ depths. This proves (C2), including
ties, without claiming that the masked matrix is positive. Since all
indices below have norm $O(U)$, this logarithm is an epsilon loss.

For the original exact gcd write $a=hx$, $b=hy$, $(x,y)=1$. Cube-freeness
ensures that every good prime of $xy$ has a nonzero reduced exponent
modulo six. Thus the good part of the primitive ratio conductor is
exactly $\operatorname{rad}(x)\operatorname{rad}(y)$. Partition the
original finite column ray data far enough to fix their $S$-local
characters. Within each resulting pair of classes, the bad conductor
norm is one fixed factor $c_S$, and

$$
q_{\mathfrak f}=c_S q_{\operatorname{rad}(x)}
                         q_{\operatorname{rad}(y)}.
\tag{C3}
$$

There are only a fixed number of these class pairs. In each row-Fourier
component any extra row character is a diagonal multiplier of modulus
at most one. For the coprimality expansion below, extend the selector
*off* the coprime locus by the same product on the right of (C3), not by
the primitive conductor of the newly introduced pair. This extension
depends on $x,y$, not on the divisor used to detect their gcd, so the
Möbius cancellation is exact.

**The complete gcd block.** Temporarily include the equal-parity terms.
Detect $(x,y)=1$ by $\sum_{e\mid(x,y)}\mu(e)$ and write $x=er$, $y=es$.
For fixed $h,e$ the two original common factors cancel on the coprime
row locus and leave exactly the row mask $(u,he)=1$. Without the
conductor selector, the scalar is the quadratic form with coefficients
$c(her)$ in the Gram matrix

$$
K_{he}=C^*W_{he}C,\qquad C_{u,r}=\chi_r(u).
$$

Here $W_{he}$ retains the original nonnegative row weight, its
$(u,he)=1$ mask and, in a row-Fourier component, its fixed diagonal
character. Finite column-class blocks are the corresponding rectangular
compressions. Bound this unmasked operator first using the existing
positive row moment; a bounded row multiplier cannot increase that
operator bound. Then apply (C2), with key
$k_r=q_{\operatorname{rad}(er)}$. In particular no row restriction is
deleted inside a nonpositive conductor-masked form.

Put $q_h\asymp H$, $q_e\asymp E$. Every surviving column $r$ is cube-free,
its norm is $O(U/(HE))$, and the actual coefficient envelope gives

$$
\sum_r|c(her)|^2\ll U^\varepsilon/(HE).
\tag{C4}
$$

For a rectangular class pair use the product of the two coefficient
norms, with the same bound. Reuse

$$
F_6(U,B)=U+B+U^{5/6}B^{1/3}+U^{1/3}B^{5/6}
$$

at $B\asymp U/(HE)$. There are $O(H)$ ideals $h$ and $O(E)$ squarefree
ideals $e$ in these dyads. Triangle over their Möbius coefficients is
now legitimate because the positive operator bound has already been
applied to each actual fixed pair. Summing $E$ over dyads gives

$$
|\mathcal T_H(Q)|\ll U^\varepsilon
\left(U+\frac UH+
U^{7/6}H^{-1/3}+U^{7/6}H^{-5/6}\right),
\tag{C5}
$$

for the conductor-masked total exact-gcd block. The $U$ term has only a
logarithmic number of dyads; all other $E$ powers are summable.

**Subtract the lower-order pairs with their masks retained.** On the
original coprime locus, $r_2(a)=r_2(b)$ holds precisely when both $x,y$
are squares. Write $x=z^2$, $y=w^2$ with $z,w$ squarefree and coprime.
Detect $(z,w)=1$ by a squarefree divisor $e$ and use the actual vector
$c(he^2r^2)$ against the cubic characters $\chi_r^2$. Its remaining
length and squared norm satisfy

$$
B_r\asymp \frac{\sqrt{U/H}}E,\qquad
\sum_r|c(he^2r^2)|^2\ll U^\varepsilon B_r/U.
$$

Apply (C2) to the corresponding cubic Gram as well; its independent
keys are again $q_{\operatorname{rad}(er)}$. The already supplied cubic
row bound is

$$
F_3^{(6\mathrm f)}(U,B_r)
=U+U^{1/3}B_r+U^{2/3}B_r^{2/3}.
$$

Counting $h,e$ and summing the dyads therefore gives the equal-parity
subtraction, including its diagonal,

$$
|\mathcal P_H(Q)|\ll U^\varepsilon
\left((UH)^{1/2}+U^{1/3}+U^{1/2}H^{1/6}\right)
\ll U^{1+\varepsilon},\qquad H\ll U.
\tag{C6}
$$

Thus the unequal-parity block is the exact difference
$\mathcal T_H(Q)-\mathcal P_H(Q)$ and satisfies (C5) with an additional
$O(U^{1+\varepsilon})$, already present there. It is not obtained by
asserting positivity of an unequal-parity or conductor selector.

**Consume the actual small-$t$ condition.** Reuse the conductor lower
bound already established above:

$$
q_{\mathfrak f}\gg_S\frac{U^2}{q_h^2T^2}.
$$

Consequently only $H\gg U/(T\sqrt Q)$ can occur in the original
low-conductor sum. Omit the other exact-gcd blocks before the
coprimality expansion, where their absence is an exact support fact.
Sum (C5)--(C6) over the remaining dyads. For
$H_0\asymp\max\{1,U/(T\sqrt Q)\}$ the result is

$$
|E_6(c;Q)|\ll U^\varepsilon
\left(U+U^{7/6}H_0^{-1/3}\right)
\ll U^\varepsilon\left(U+U^{5/6}T^{1/3}Q^{1/6}\right),
$$

which is (C1). All original squarefree columns, the $t=1$ packet,
shared primes, finite class components and collision zeros remain.
The staircase step imposes no transform-height or moving-conductor
cost; the same original bounded or polylog profile contract is used.

In particular choose $T=U^{1/1000}$ and $Q=U^{3/2}$. Then

$$
\boxed{
|E_{6,\,q_{\mathfrak f}\le U^{3/2}}^{\mu,\le U^{1/1000}}|
\ll U^{3251/3000+\varepsilon},
\qquad
B_*-\frac{3251}{3000}
=\frac{12249-5000\sqrt6}{3000}>0.
}
\tag{C7}
$$

The sign of the last margin follows from $12249^2>6\cdot5000^2$.
More generally $T=U^\theta$, $Q=U^q$ gives the exponent
$(5+q+2\theta)/6$ when this exceeds $1$; it is below $B_*$ for
$q<26-10\sqrt6-2\theta$.

This replaces the earlier sufficient high-conductor target by the exact
complement

$$
\operatorname{Re}E_{6,\,q_{\mathfrak f}>U^{3/2}}^{\mu,\le U^{1/1000}}
\ll U^{B_*-1/100000+\varepsilon}.
\tag{C8}
$$

Such an estimate, still not supplied here, would combine with (C7) and
the existing truncation/interference margin $1/50000$ to improve the
full inverse-fourth exponent by $1/100000$. No squarefree column or
finite component is discarded from that remaining target. The present
application enlarges the controlled conductor range; it does not prove
(C8), improve the full inverse-fourth moment, restore the signed Robin
expression or prove RH. It carries no local Lean certification or
literature-priority claim.


## Removing the repeated-factor cutoff from the low-conductor estimate

Squarepart density permits a stronger application of the same sixth-order
supplier, staircase bound (C2) and parity subtraction (C6). This is a
`repo-derived` use of those existing tools, conditional on their stated
analytic inputs and the same fixed or polylog cost contract. It applies
to the full original cube-free coefficient $g_D$, without discarding
large repeated factors. More generally, let $c$ have the same normalized
envelope $|c(a)|\ll U^{-1/2+\varepsilon}$ on $q_a\asymp U$ and cube-free
support. Then its original sharp low-conductor contraction satisfies

$$
\boxed{
|E_6(c;Q)|\ll U^\varepsilon
\left(U+U^{5/6}Q^{1/6}+U^{11/12}Q^{1/9}\right).
}
\tag{C9}
$$

The conductor and finite-component conventions are those of (C3).
This assertion concerns the complete row majorant, with its actual
coherent finite components; it is not a deletion of a signed row
selector inside an adaptive bin.

**Retain the squarepart density before applying the sieve.** Use the
exact gcd $a=hx$, $b=hy$ and decompose

$$
x=\alpha^2v,\qquad y=\beta^2w,
\qquad q_h\asymp H,\quad q_\alpha\asymp A,\quad q_\beta\asymp B.
$$

Here $\alpha,\beta,v,w$ are squarefree, $(\alpha,v)=(\beta,w)=1$.
The original condition $(x,y)=1$ is exactly

$$
(\alpha,\beta)=1,\qquad
(v,\alpha\beta)=(w,\alpha\beta)=1,\qquad(v,w)=1.
$$

Fix the permitted $\alpha,\beta$ and retain the middle two conditions
as separate column masks. Detect only the last condition by
$\sum_{e\mid(v,w)}\mu(e)$, writing $v=er$, $w=es$. Thus $e$ is squarefree
and coprime to $\alpha\beta$, while $r,s$ remain squarefree and each
coprime to $e\alpha\beta$. These restrictions are retained even when
$(r,s)>1$ in the Möbius expansion. Put

$$
X=\frac{U}{HA^2},\qquad Y=\frac{U}{HB^2},\qquad q_e\asymp E.
$$

The actual left and right vectors are $c(h\alpha^2er)$ and
$c(h\beta^2es)$, with their masks and finite class conditions. Their
remaining lengths are $O(X/E)$ and $O(Y/E)$, so

$$
\|c_L\|_2\|c_R\|_2
\ll U^\varepsilon\frac{\sqrt{XY}}{UE}
=\frac{U^\varepsilon}{HABE}.
\tag{C10}
$$

The common characters of $h,e$ leave their original collision mask.
The remaining factor $\chi_\alpha^2\overline{\chi_\beta^2}$ is a bounded
row multiplier, including its zeros. Consequently the rectangular row
operator is bounded by
$\sqrt{F_6(U,X/E)F_6(U,Y/E)}$ before imposing the conductor selector.
The class-pair constants and row-Fourier characters are retained as in
(C3)--(C5).

The off-coprime conductor extension is still the original product
$q_{\operatorname{rad}(x)}q_{\operatorname{rad}(y)}
=q_\alpha q_v q_\beta q_w$, independent of the detecting divisor $e$.
For fixed $e$ its independent staircase keys are $q_\alpha q_{er}$ and
$q_\beta q_{es}$. Apply (C2) to this rectangular operator, not to an
expression with deleted row masks. There are $O(HABE)$ choices of
$h,\alpha,\beta,e$ in these dyads; this count cancels the density in
(C10). Monotonicity of $F_6$ and the logarithmic number of $E$ dyads give

$$
|\mathcal T_{H,A,B}(Q)|
\ll U^\varepsilon\sqrt{F_6(U,X)F_6(U,Y)}.
\tag{C11}
$$

All quantities in this bound belong to the same actual pair realization.
No separately optimized coefficient vectors replace $c$.

**Use the joint support constraints.** On the original coprime locus,
the good conductor norm is $q_\alpha q_v q_\beta q_w\asymp
U^2/(H^2AB)$. Thus a nonempty low-conductor block obeys

$$
H^2AB\gg U^2/Q,\qquad
1\ll A,B\ll\sqrt{U/H},\qquad 1\ll X,Y\ll U.
$$

Omit empty original blocks before the Möbius expansion. The same joint
constraints give

$$
\begin{aligned}
\sqrt{XY}
&=\frac{U}{HAB}
\ll\min\left\{\frac UH,\frac{HQ}{U}\right\}
\ll Q^{1/2},\\
X,Y
&\ll\min\left\{\frac UH,\frac{H^2Q^2}{U^2}\right\}
\ll Q^{2/3}.
\end{aligned}
\tag{C12}
$$

For the second line use the first support inequality together with
$A^2,B^2\ll U/H$. Since $X,Y\ll U$, the reused four-term sieve simplifies
to $F_6(U,X)\ll U+U^{5/6}X^{1/3}$, and similarly for $Y$. Hence

$$
\begin{aligned}
\sqrt{F_6(U,X)F_6(U,Y)}
&\ll U+U^{11/12}(X^{1/6}+Y^{1/6})
       +U^{5/6}(XY)^{1/6}\\
&\ll U+U^{11/12}Q^{1/9}+U^{5/6}Q^{1/6}.
\end{aligned}
$$

Sum the $H,A,B$ dyads, costing only $U^\varepsilon$. This bounds the
complete conductor-masked contraction including equal-parity pairs.
Subtract those pairs using (C6): its proof requires only the cube-free
support and normalized envelope, not a bound on the repeated factor.
It therefore costs $U^{1+\varepsilon}$ for this full $c$ as well and
proves (C9). In particular, no positivity of the sharp conductor mask
or of the unequal-parity restriction has been assumed.

For the full original $c=g_D$ at $Q=U^{3/2}$, both nontrivial terms in
(C9) are $U^{13/12}$. Thus

$$
\boxed{
|E_{6,\,q_{\mathfrak f}\le U^{3/2}}^\mu|
\ll U^{13/12+\varepsilon},\qquad
B_*-\frac{13}{12}=\frac{49-20\sqrt6}{12}>0.
}
\tag{C13}
$$

Here $49^2=2401>2400=6\cdot20^2$. The estimate includes every original
repeated factor and all original squarefree columns, finite components
and collision zeros.

A sufficient missing input can consequently be stated directly for the
full original coefficient:

$$
\operatorname{Re}E_{6,\,q_{\mathfrak f}>U^{3/2}}^\mu
\ll U^{B_*-\nu+\varepsilon},
\qquad 0<\nu<B_*-13/12.
\tag{C14}
$$

Together with (C13) and the already paid cubic block, (C14) would improve
the inverse-fourth exponent to $B_*-\nu$. This implication needs no
repeated-factor truncation or tail-interference estimate. The same
original plain-fourth consumer would then apply with its original
length and cost restrictions.

The preceding small-$t$ target is also compatible with this full one.
Put $c_T=g_{\le T}$, $T=U^\theta$, $0<\theta<1/2$. Apply (C9) to both $g_D,c_T$ and use
the exact full/low/high decomposition. The existing moment-interference
bound and the cubic block bounds give

$$
\left|E_{6,\,q_{\mathfrak f}>U^{3/2}}^\mu
-E_{6,\,q_{\mathfrak f}>U^{3/2}}^{\mu,\le T}\right|
\ll U^{B_*-\theta/50+\varepsilon}+U^{13/12+\varepsilon}.
\tag{C15}
$$

This is an identity followed by bounds on whole moments and whole
low-conductor sums, not an assertion that a conductor mask decreases
interference. At $\theta=1/1000$ it preserves the previously specified
saving $\nu=1/100000$. Neither form of the remaining high-conductor
estimate is supplied here. The new application removes the repeated-factor
cutoff from the paid low-conductor portion and simplifies the sufficient
full-coefficient target; the full inverse-fourth strict improvement,
signed Robin restoration and RH remain open. No literature-priority or
local Lean-certification claim is made.


## Localizing the remaining contraction by the product squarepart

The rectangular estimate before the conductor-cap step also pays a
high-conductor sector. Reuse (C10)--(C11), with the same full original
cube-free coefficient, row family, finite components and fixed or polylog
cost contract. No new large-sieve input is needed.

For an original pair write $a=h\alpha^2v$, $b=h\beta^2w$ as above, so
$v,w$ are squarefree and coprime. Define the intrinsic product-squarepart
norm

$$
P(a,b)=q_{h\alpha\beta}
=\left(\frac{q_aq_b}{q_{r_2(ab)}}\right)^{1/2}.
\tag{C16}
$$

Indeed, $ab=(h\alpha\beta)^2vw$ and $r_2(ab)=vw$. In the original
coefficient coordinates $a=s_at_a^2$, $b=s_bt_b^2$, the same quantity is
$q_{t_at_b(s_a,s_b)}$. Thus this cut retains the relationship between the
two actual columns; it does not select two independently optimized
coefficient vectors.

For a fixed $0<r<1$ put $R=U^r$. The full original unequal-parity
contraction on $P(a,b)\ge R$ satisfies

$$
\boxed{
|E_{6,\,P\ge R}(c)|
\ll U^\varepsilon
\left(U^{13/12}+U^{7/6}R^{-1/3}\right).
}
\tag{C17}
$$

Here $c=g_D$, or any cube-free coefficient with the same normalized
envelope. To prove this, impose the exact $P\ge R$ condition while fixing
$h,\alpha,\beta$. It is then a scalar restriction on those parameters,
independent of the remaining $e,r,s$ variables in the coprimality
expansion. Retain all original cross-coprimality, finite-class and row
collision masks. The norm-density cancellation in (C10) and the unmasked
rectangular operator in (C11) therefore still apply; no primitive-conductor
selector or staircase estimate is required here.

On a nonempty $H,A,B$ block, $HAB\gg R$ and
$X=U/(HA^2)$, $Y=U/(HB^2)$ satisfy $X,Y\ll U$. Consequently,

$$
\begin{aligned}
\sqrt{F_6(U,X)F_6(U,Y)}
&\ll U+U^{11/12}(X^{1/6}+Y^{1/6})
       +U^{5/6}(XY)^{1/6}\\
&\ll U^{13/12}+U^{7/6}(HAB)^{-1/3}.
\end{aligned}
$$

Summing the permitted dyads costs only $U^\varepsilon$. This first
bounds the total contraction including equal-parity pairs. On those
pairs $r_2(ab)=1$, hence $P(a,b)=\sqrt{q_aq_b}\asymp U$. Since $r<1$,
all of them belong to $P\ge U^r$ for sufficiently large $U$. Their
subtraction is exactly the already paid full cubic block
$H_2\ll U^{1+\varepsilon}$, with its actual coefficients and zeros.
This proves (C17), without asserting positivity of the squarepart cut or
introducing a new bound for a partially retained cubic block. The bounded
initial range is absorbed in the implied constant.

In particular, the full original coefficient obeys

$$
\boxed{
|E_{6,\,P\ge U^{1/4}}^\mu|
\ll U^{13/12+\varepsilon}.
}
\tag{C18}
$$

This pays more than a short-conductor phenomenon. From (C3), on the
original annuli and fixed finite component,

$$
q_{\mathfrak f}\asymp_S\frac{U^2}{q_hP(a,b)},
\qquad q_h\le P(a,b).
\tag{C19}
$$

The paid locus can therefore have $q_h\asymp1$,
$P(a,b)\asymp U^{1/4}$ and primitive conductor of size $U^{7/4}$.
Conversely, the remaining locus $P<U^{1/4}$ forces
$q_{\mathfrak f}\gg_S U^{3/2}$. These conductor comparisons retain their
fixed constants; they do not identify the two sharp cutoffs.
Equivalently, its parity-disagreement core has
$q_{r_2(ab)}\gg U^{3/2}$.

A sufficient remaining input for the full inverse-fourth improvement is
now the conductor-unrestricted estimate

$$
\boxed{
\operatorname{Re}E_{6,\,P<U^{1/4}}^\mu
\ll U^{B_*-\nu+\varepsilon},
\qquad 0<\nu<B_*-13/12.
}
\tag{C20}
$$

Indeed, the two $P$ regions partition the same original ordered sum;
combine (C18), (C20) and the paid cubic block. No claim that masking
reduces interference is used. This target retains the coprime squarefree
pairs $h=\alpha=\beta=1$, so the hardest actual Möbius cross-core
correlation remains. The gain is the additional paid sector and the
removal of the total primitive-conductor selector from the sufficient
unpaid input. The large parity-disagreement estimate (C20), full moment
improvement, signed Robin restoration and RH remain unproved. This is
an application of the existing operator bounds, without a literature-priority
claim or local Lean certification.


## Removing a short Type-I part from the remaining coefficient

The zero-slot plain fourth moment in [Xu–Sang v2, Theorem 2.2](https://arxiv.org/html/2610.17675v2),
the existing full inverse-fourth bound, and (C18) permit a further exact
source reduction. This is a `repo-derived` application of those inputs
and the standard truncated Dirichlet-inverse identity; no new sieve or
Möbius identity is claimed. Keep the same original physical rows,
finite components, collision zeros and fixed or polylog cost contract.

Fix one original presentation $\psi_u$, put $D=\sqrt U$, and choose
fixed $0<a<b$ with $\operatorname{supp}V\subset[a,b]$. Let

$$
z=(bD)^{1/2},\qquad A=U^{1/25},\qquad
\mu_z(d)=\mu(d)\mathbf1_{q_d\le z}.
$$

For sufficiently large $U$, $A<z<aD$. The familiar order-two truncated
inverse formula is $\mu=2\mu_z-\mu_z*\mu_z*1$ on $q_d\le z^2$.
It follows directly because $(\mu-\mu_z)*(\mu-\mu_z)*1$ has support
$q_d>z^2$. On the original annulus $aD\le q_d\le bD$, the $2\mu_z$
term vanishes. Multiplying the formula by $\mu^2(d)$ retains exactly the
original squarefree support. Thus, with all ideals good, define

$$
\begin{aligned}
\lambda_{\mathrm{II}}(d)
&=-\mu^2(d)
\sum_{\substack{rsc=d\\q_r,q_s\le z\\q_{rs}>A}}
\mu(r)\mu(s),\\
M_{\mathrm{II}}(u)
&=D^{-1/2}\sum_d\lambda_{\mathrm{II}}(d)
\psi_u(d)V(q_d/D),\\
M_{\mathrm I}(u)
&=-D^{-1/2}\sum_{\substack{q\ {\rm sf}\\q_q\le A}}
\mu(q)\tau(q)\psi_u(q)
\sum_{\substack{c\ {\rm sf}\\(c,q)=1}}
\psi_u(c)V(q_qq_c/D).
\end{aligned}
\tag{C21}
$$

Here $\tau$ counts ideal divisors. The small-$rs$ terms have $rs=q$
squarefree and $q_q\le A<z$, so every ordered factorization of $q$ is
allowed and $\sum_{rs=q}\mu(r)\mu(s)=\mu(q)\tau(q)$. Consequently the
original inverse polynomial satisfies the exact identity
$M_\psi=M_{\mathrm I}+M_{\mathrm{II}}$. No original row or prime collision
has been removed.

**Pay the whole Type-I part without a moving-modulus theorem.** In its
inner sum expand $\mu^2(c)=\sum_{e^2\mid c}\mu(e)$. The condition
$(c,q)=1$ forces $(e,q)=1$. Detect the remaining coprimality by
$\sum_{v\mid(c/e^2,q)}\mu(v)$ and write $c=e^2vn$. The row scalar
$\psi_u(e^2v)$ has modulus at most one, including its zeros; the remaining
$n$ sum is the original unpunctured plain polynomial at length
$D/(q_qq_e^2q_v)$. This step introduces no extra inducing character or
moving puncture into the plain supplier.

For the weighted $L^4$ norm on the same original row set, that supplier
and Minkowski therefore give

$$
\begin{aligned}
\|M_{\mathrm I}\|_4
&\ll U^{1/4+\varepsilon}
\sum_{q_q\le A}\frac{\tau(q)}{\sqrt{q_q}}
\sum_{v\mid q}q_v^{-1/2}
\sum_{q_e\ll\sqrt{D/q_q}}q_e^{-1}\\
&\ll U^{1/4+\varepsilon}A^{1/2},\\
\mathcal T_{\mathrm I}:=\|M_{\mathrm I}\|_4^4
&\ll U^{27/25+\varepsilon}.
\end{aligned}
\tag{C22}
$$

All nonempty subunit lengths are bounded below by the fixed support
constant $1/b$ and use the usual bounded annular enlargement. Ideal
counting and divisor bounds pay the sums; the $e$ sum costs only a
logarithm. These are positive-norm estimates for the complete Type-I
polynomial, not positivity assertions about a selected correlation.

**Pay its full interference before applying any pair cut.** Reuse the
original $\mathcal T_\mu:=\|M_\psi\|_4^4\ll U^{B_*+\varepsilon}$.
Since $27/25<B_*$, the exact decomposition and Minkowski give
$\mathcal T_{\mathrm{II}}:=\|M_{\mathrm{II}}\|_4^4
\ll U^{B_*+\varepsilon}$. The reverse triangle inequality for the norms
and the difference of fourth powers imply

$$
\begin{aligned}
|\mathcal T_\mu-\mathcal T_{\mathrm{II}}|
&\ll(\|M_\psi\|_4+\|M_{\mathrm{II}}\|_4)^3
\|M_{\mathrm I}\|_4\\
&\ll U^{C_*+\varepsilon},\qquad
C_*:=\frac{3B_*+27/25}{4}
=\frac{829-250\sqrt6}{200}<\frac{13}{12}.
\end{aligned}
\tag{C23}
$$

The exact margin is
$13/12-C_*=(750\sqrt6-1837)/600>0$, since
$6\cdot750^2-1837^2=431$. The finite components are restored coherently
with the original common cost; the decomposition is made on each
original presentation, without replacing any vector by an independently
optimized one.

**The remaining pair target has a specific new source.** The coefficient
$\lambda_{\mathrm{II}}$ is squarefree-supported and
$|\lambda_{\mathrm{II}}(d)|\le\tau_3(d)$. Hence

$$
g_{\mathrm{II}}(a)=D^{-1}\sum_{d_1d_2=a}
\lambda_{\mathrm{II}}(d_1)\lambda_{\mathrm{II}}(d_2)
V(q_{d_1}/D)V(q_{d_2}/D)\xi(a)
$$

has cube-free support, $q_a\asymp U$ and the normalized envelope
$|g_{\mathrm{II}}(a)|\ll U^{-1/2+\varepsilon}$ used in (C18).
The same full cubic block costs $U^{1+\varepsilon}$ for this coefficient,
and its complete large-$P$ block costs $U^{13/12+\varepsilon}$.
Subtract their two exact full/small/large decompositions and use (C23):

$$
\boxed{
\left|E_{6,\,P<U^{1/4}}^\mu
      -E_{6,\,P<U^{1/4}}(g_{\mathrm{II}})\right|
\ll U^{13/12+\varepsilon}.
}
\tag{C24}
$$

This uses whole-moment interference and two separately paid whole
large-$P$ blocks; it does not assert that a pair mask contracts an error.
For every fixed $0<\nu<B_*-13/12$, (C20) may therefore equivalently be
sought with this explicit $g_{\mathrm{II}}$ in place of $g_D$.

The change is in the actual coefficient, not just its name. For squarefree
$d$ put $d_{\le z}=\prod_{\mathfrak p\mid d,\ q_{\mathfrak p}\le z}
\mathfrak p$. If $q_{d_{\le z}}\le A$, then
$\lambda_{\mathrm{II}}(d)=0$: every allowed $rs$ divides $d_{\le z}$.
Thus the remainder excludes prime $d$ and all $d=pm$ with $q_p>z$
and $q_m\le A$. It changes coefficients on other columns, so (C24) is
not a bound for deleting just those columns from the original moment.
Balanced two-prime factors and their cross-correlations remain.

No estimate below $B_*$ for this remaining Type-II contraction is
supplied. The full inverse-fourth improvement, signed Robin restoration
and RH remain open; this application has no local Lean certification or
literature-priority claim.


## A smooth Type-I cutoff using the existing reciprocal strip

The paid support reduction can be enlarged by combining the same
truncated inverse with a two-variable Euler correction. Reuse
`lem:logarithmic-control`, `lem:deleted-euler-factors` and
`lem:smooth-calculus` of the [pinned OpenAI primary manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex),
and the zero-slot plain fourth moment used in (C22). This is a
`repo-derived` application of those analytic inputs, not a new zero-free
region or truncated-inverse identity. Keep the same original physical
rows, presentations, collision zeros and fixed or stated polylog costs.
Use $\beta=7/8$ from that source; a Dirichlet-only nonvanishing statement
would not supply the required Hecke-family reciprocal bound. The
no-linear-term correction and absolute-mass transport reuse the mechanism
of Collet's Chapter 25 described [above](#reusing-the-global-ordinary-source-frontier);
the application here concerns the actual smooth Type-I coefficient.

**Exact smooth split.** Choose a fixed smooth $0\le W\le1$, equal to $1$
on $[0,1]$ and $0$ on $[2,\infty)$. With the same $z=(bD)^{1/2}$, now put
$A=U^{1/20}$. For sufficiently large $U$, $2A<z<aD$. Define

$$
\begin{aligned}
\lambda_{\mathrm{II},W}(d)
&=-\mu^2(d)\sum_{\substack{rsc=d\\q_r,q_s\le z}}
 \mu(r)\mu(s)\bigl(1-W(q_{rs}/A)\bigr),\\
M_{\mathrm I,W}(u)
&=-D^{-1/2}\sum_{\substack{q,c\ {\rm sf}\\(q,c)=1}}
 \mu(q)\tau(q)\psi_u(qc)W(q_q/A)V(q_qq_c/D),\\
M_{\mathrm{II},W}(u)
&=D^{-1/2}\sum_d\lambda_{\mathrm{II},W}(d)
 \psi_u(d)V(q_d/D).
\end{aligned}
\tag{C25}
$$

Then $M_\psi=M_{\mathrm I,W}+M_{\mathrm{II},W}$ exactly. Indeed, wherever
$W(q_{rs}/A)$ is nonzero, $q_{rs}<2A<z$, so all ordered factorizations
of $q=rs$ occur, with sum $\mu(q)\tau(q)$. The minus sign in
$M_{\mathrm I,W}$ is global; its two-variable coefficient below is
$\mu(q)\tau(q)$.

**A summable correction preserves the plain factor.** On an absolutely
convergent starting half-plane, the series for squarefree coprime
$(q,c)$ has local factor $1-2x+y$, where
$x=\psi_u(\mathfrak p)q_{\mathfrak p}^{-s}$ and
$y=\psi_u(\mathfrak p)q_{\mathfrak p}^{-t}$. Factor it as

$$
\begin{aligned}
F_u(s,t)&=L(s,\psi_u)^{-2}L(t,\psi_u)H_u(s,t),\\
(H_u)_{\mathfrak p}
&=\frac{(1-2x+y)(1-y)}{(1-x)^2}
 =1-\frac{(x-y)^2}{(1-x)^2},\\
H_u(s,t)&=\sum_{d,e}h(d,e)\psi_u(de)q_d^{-s}q_e^{-t}.
\end{aligned}
\tag{C26}
$$

The multiplicative coefficient $h(d,e)$ is independent of the row.
All nonconstant local terms have total degree at least two. Hence, for
$\sigma>1/2$, $\tau>1/2$ and $\sigma+\tau>1$,

$$
\sum_{d,e}|h(d,e)|q_d^{-\sigma}q_e^{-\tau}<\infty:
\qquad
\sum_{(j,k)\ne(0,0)}|h(\mathfrak p^j,\mathfrak p^k)|
 q_{\mathfrak p}^{-j\sigma-k\tau}
\le\frac{(q_{\mathfrak p}^{-\sigma}
          +q_{\mathfrak p}^{-\tau})^2}
         {(1-q_{\mathfrak p}^{-\sigma})^2}.
$$

Equality of coefficients in (C26) expresses the joint coefficient as
an $h$-convolution of $(\mu*\mu)(r)\psi_u(r)$ in the first variable
and the plain coefficient $\psi_u(n)$ in the second. This is a formal
coefficient transport followed by finite polynomial estimates; no
pointwise bound for $L(t,\psi_u)$ near the central line is invoked.
Original zero-only primes give local factor $1$ throughout, including
in the transported coefficient.

For a smooth annular profile $P$ and length $R\gg1$, moving its Mellin
line to $\sigma=\beta+v$, $v>0$, in the inverse-square series gives

$$
\sup_u\left|R^{-1/2}\sum_r(\mu*\mu)(r)\psi_u(r)P(q_r/R)\right|
\ll U^\varepsilon R^{\sigma-1/2}\,p_J(P).
$$

Here $p_J$ is a fixed finite smooth seminorm, chosen after the desired
loss. The source's full reciprocal strip controls $L(s,\psi_u)^{-2}$;
its deleted-factor lemma includes both the primitive conductor and the
complete original deletion radical. A principal reciprocal has a zero,
rather than a pole, at $s=1$ and contributes no residue. The remaining
plain factor uses the same original nonprincipal row supplier as (C22).
For a fixed finite twist, a principal inducing character on a sixth-power-free
physical row forces its good-prime support into the fixed twist support;
with valuations at most five these rows are bounded, hence absent from
sufficiently large annuli. Retain the original finite exceptional-row
treatment at bounded scales; no arbitrary principal row is added to the
plain moment theorem.

Dyadically localize the total first variable at $q_q\asymp Q\ll A$ and
the second at $q_c\asymp C=D/Q$. Their joint profile is smooth on a
fixed compact annulus, uniformly in $Q/A$: derivatives of $W(Qx/A)$
are bounded there. Separate it by a common logarithmic Fourier measure.
Its rapidly decreasing transform pays the fixed polynomial growth of
the two annular profile seminorms. These Fourier parameters belong to
the profiles; the original row twists and their height contract are
unchanged. The global reciprocal strip handles the inverse factor's
internal Mellin heights.

After $q=dr$, $c=en$, normalization contributes $(q_dq_e)^{-1/2}$.
The inverse-square supremum and the plain $L^4$ bound therefore give,
for this dyadic piece,

$$
\begin{aligned}
\|M_{\mathrm I,W;Q}\|_4
&\ll U^{1/4+\varepsilon}Q^{\sigma-1/2}
 \sum_{\substack{q_d\ll Q\\q_e\ll C}}
 |h(d,e)|q_d^{-\sigma}q_e^{-1/2}\\
&\ll U^{1/4+\varepsilon}Q^{\sigma-1/2}C^\eta,
 \qquad \eta>0.
\end{aligned}
$$

The last step uses the absolute mass in (C26) at
$(\sigma,1/2+\eta)$. Shifted lengths below a fixed positive support
constant are empty; all remaining subunit lengths are bounded-factor
annular scales. Thus none causes an extra power. Choose $v,\eta$ within
the final loss, and sum $Q$ dyadically. At $\beta=7/8$ and $A=U^{1/20}$,

$$
\boxed{
\mathcal T_{\mathrm I,W}
 :=\|M_{\mathrm I,W}\|_4^4
 \ll U^{1+\varepsilon}A^{4\beta-2}
 =U^{43/40+\varepsilon}.
}
\tag{C27}
$$

**Whole interference and the same remaining target.** Since
$43/40<B_*$, the full-moment argument of (C23) now gives

$$
\begin{aligned}
|\mathcal T_\mu-\mathcal T_{\mathrm{II},W}|
&\ll U^{C_W+\varepsilon},\\
C_W&=\frac{3B_*+43/40}{4}
 =\frac{663-200\sqrt6}{160}
 =C_*-\frac1{800}<\frac{13}{12}.
\end{aligned}
$$

The remainder is still squarefree-supported and bounded by $\tau_3$.
Its actual square coefficient $g_{\mathrm{II},W}$ therefore has the
same cube-free normalized envelope as $g_{\mathrm{II}}$. Pay its whole
cubic and large-$P$ blocks separately, as in (C24), to obtain

$$
\boxed{
\left|E_{6,\,P<U^{1/4}}^\mu
      -E_{6,\,P<U^{1/4}}(g_{\mathrm{II},W})\right|
\ll U^{13/12+\varepsilon}.
}
\tag{C28}
$$

All finite components are restored coherently with the same common
cost. If $q_{d_{\le z}}\le A=U^{1/20}$, then every allowed $rs$ satisfies
$W(q_{rs}/A)=1$, so $\lambda_{\mathrm{II},W}(d)=0$. This enlarges the
paid support exclusion in (C24). Coefficients on other columns change
as well; the operation is not deletion of only that set from the
original moment. For $0<\nu<B_*-13/12$, the unpaid (C20) can be sought
with this explicit smooth remainder. The required Type-II gain, full
inverse-fourth improvement, signed Robin restoration and RH remain
open. These source-conditional applications carry neither local Lean
certification nor a literature-priority claim.


## Combining two bounds on the same buffered Type-I bin

The smooth cutoff can be enlarged further by using both sides of the
already supplied local $L$-control. Reuse the exact coefficient
transport (C26), the original buffered bins and counts from
[§459](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#459-缓冲零点分箱下的完整原卷积联合估计),
and `lem:buffered-bins`, `lem:detector-dyads` and `lem:plain` of the
[pinned OpenAI primary manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex).
This is a `repo-derived` application to the actual smooth Type-I
coefficient, not a new zero-density, Euler-transport or bilinear theorem.

In the exact identity (C25), take the cutoff
$A_{\rm b}=U^{1/12}$, and denote the resulting components by
$M_{\mathrm I,b}$, $M_{\mathrm{II},b}$ and
$\lambda_{\mathrm{II},b}$. Eventually $2A_{\rm b}<z<aD$, as required.
Keep the original floor $a_0=51/100$, the same physical row family,
all original zero extensions and the same fixed or polylog cost
contract. On a nonfloor bin $\mathcal B_{i,a}$ put $\delta=2a-1$.
Its original counting exponent is

$$
R(\delta)=
\begin{cases}
(15-16\delta)/(15-6\delta),&1/50<\delta\le5/6,\\
1-\delta,&5/6\le\delta\le1.
\end{cases}
$$

For a dyadic block $q_q\asymp Q\ll A_{\rm b}$, $q_c\asymp C=D/Q$,
write $T_Q(i,a)=\sum_{u\in\mathcal B_{i,a}}
\Omega(u)|M_{\mathrm I,b;Q}(u)|^4$. Two existing estimates apply to
this same positive quantity:

$$
\boxed{
T_Q(i,a)\ll U^\varepsilon
\min\left\{U^{R(\delta)+\delta},\ UQ^{2\delta}\right\}.
}
\tag{C29}
$$

**The first bound uses the local upper and reciprocal bounds together.**
Apply double Mellin inversion to the uniformly smooth joint annular
profile from (C26). Move its two finite contours to
$\Re s=\Re t=a+8e$. The original buffered-bin lemma bounds both
$L_{\rm orig}$ and its reciprocal on these contours; the mass of $H$
is absolutely convergent there. Thus the same actual row satisfies

$$
|M_{\mathrm I,b;Q}(u)|
\ll U^\varepsilon D^{-1/2}Q^{a+8e}C^{a+8e}
=U^\varepsilon D^{a-1/2+8e},
$$

up to a negligible tail. Its fourth power costs
$U^{\delta+O(e)+\varepsilon}$. Multiply by the same bin's count to
obtain the first branch. This uses the local upper bound on that bin,
not a global upper bound below $7/8$.

**The second bound keeps the whole plain fourth moment.** Repeat the
normalized $h$-convolution estimate preceding (C27), now using the
inverse-square bound on the same finite local line $a+8e$. Its mass
is taken at $(a+8e,1/2+\eta)$, paying the same $C^\eta$ factor. After
bounding the row scalar $\psi_u(de)$ in modulus and applying Minkowski
on the bin-restricted positive norm, enlarge only the plain positive
fourth moment to the original full row family. The result is
$T_Q(i,a)\ll U^{1+\varepsilon}Q^{2\delta+O(e)}$.
Both bounds retain the same coefficient and same bin, so their minimum
is legitimate. No selector is removed from a signed correlation.

For both arguments, truncate the common two-variable Fourier measure
and the internal Mellin frequencies inside a fixed fraction of the
original buffer height $T_1$. The two variables share that budget.
Only finite contour segments are shifted; the remaining tails stay
on absolute lines. The original fixed polynomial bounds and arbitrary
Fourier/Mellin decay pay those tails and the horizontal joins. Choose
the bin losses and finite internal orders first, then the small buffer
height exponent, and finally the outer decay order. This is the height
order of §459 and the primary source, with no extension to infinite
local contours or enlargement of the original row-twist contract.
All finite profile costs, complete deletion radicals and finite
presentations belong to one common envelope. The original nonprincipal
physical rows allow the plain shift without a pole; bounded principal
exceptions retain their original treatment.

**Consume the two bounds before taking the worst bin.** Since
$Q\ll U^{1/12}$, the second branch has exponent at most $1+\delta/6$.
For $\delta\le1/2$ this is at most $13/12$. For
$1/2\le\delta\le5/6$ the first branch suffices, because

$$
\frac{13}{12}-R(\delta)-\delta
=\frac{(2\delta-1)(12\delta-5)}{4(15-6\delta)}\ge0.
$$

For $5/6\le\delta\le1$, $R(\delta)+\delta=1$.
The original floor has $O(U)$ rows; applying only the second branch
with $\delta_0=1/50$ gives $U^{301/300+\varepsilon}$, also below
$U^{13/12+\varepsilon}$. No lowered floor is required. Choose the bin
width and internal losses within the final $\varepsilon$, then sum the
finitely many bins and dyadic blocks in the original norm and restore
all finite components coherently. This gives

$$
\boxed{
\mathcal T_{\mathrm I,b}:=\|M_{\mathrm I,b}\|_4^4
\ll U^{13/12+\varepsilon},\qquad A_{\rm b}=U^{1/12}.
}
\tag{C30}
$$

**The larger cutoff has a different paid transfer error.** The complete
inverse-fourth bound and (C30) imply, by the same full-interference
inequality as (C23),

$$
\begin{aligned}
|\mathcal T_\mu-\mathcal T_{\mathrm{II},b}|
&\ll U^{C_{\rm b}+\varepsilon},\\
C_{\rm b}&=\frac{3B_*+13/12}{4}
=\frac{199-60\sqrt6}{48},\\
B_*-C_{\rm b}&=\frac{B_*-13/12}{4}
=\frac{49-20\sqrt6}{48}>0.
\end{aligned}
\tag{C31}
$$

The last inequality follows from $49^2-6\cdot20^2=1$. In particular
$13/12<C_{\rm b}<B_*$: the smaller transfer error in (C28) is not being
claimed for this enlarged cutoff. The new remainder is still
squarefree-supported with $|\lambda_{\mathrm{II},b}|\le\tau_3$, so its
actual square $g_{\mathrm{II},b}$ retains the same cube-free envelope.
Subtract the two complete cubic/large-$P$/small-$P$ decompositions and
pay each whole cubic and large-$P$ block as before. Since their exponent
$13/12$ is smaller than $C_{\rm b}$, the result is

$$
\boxed{
\left|E_{6,\,P<U^{1/4}}^\mu
      -E_{6,\,P<U^{1/4}}(g_{\mathrm{II},b})\right|
\ll U^{C_{\rm b}+\varepsilon}.
}
\tag{C32}
$$

Thus it remains sufficient to prove (C20) for this explicit remainder
with any fixed $0<\nu<(B_*-13/12)/4$. The identity for the remainder
now excludes $q_{d_{\le z}}\le U^{1/12}$, including the corresponding
near-prime inverse factors. Its other coefficients also change.
The smaller allowable saving is explicit and remains strictly positive;
no such Type-II estimate is supplied. The complete inverse-fourth
exponent, signed Robin restoration and RH are not improved by the
support reduction alone. No local analytic Lean certification or
literature-priority claim is made.


## Rough support of the actual Type-II remainder

The rough-prime theorem in [Xu–Sang v2, Proposition 7.2](https://arxiv.org/html/2610.17675v2)
applies to a specific part of (C32). The following `repo-derived`
interface uses that theorem and its finite-profile proof; it does not
assume a contraction under coefficient masking. Fix
$A=A_{\rm b}=U^{1/12}$, retain the original annulus
$q_d\asymp D=\sqrt U$, and take a fixed smooth $0\le\rho\le1$ with
$\rho=0$ on $[0,2]$ and $\rho=1$ on $[4,\infty)$. Put

$$
r_A(d)=\prod_{p\mid d}\rho(q_p/A),\qquad
R(u)=D^{-1/2}\sum_d r_A(d)\lambda_{\mathrm{II},b}(d)
\psi_u(d)V(q_d/D).
$$

On the nonzero rough support, only $q=1$ contributes to the Type-I
coefficient in (C25), since $W(q_q/A)=0$ for $q_q>2A$.
Its coefficient is $-1$, so the exact decomposition gives

$$
r_A(d)\lambda_{\mathrm{II},b}(d)
=r_A(d)\mu^2(d)(1+\mu(d)).
\tag{C33}
$$

For squarefree $d$ this is twice the rough weight when $\omega(d)$ is
even, and zero when it is odd. For sufficiently large $U$, a supported
$d$ has at most six prime factors, since all exceed $2U^{1/12}$ and
$q_d\ll U^{1/2}$. The nonzero cases therefore have $2,4,6$ prime
factors. This parity statement is restricted to the rough support.

**Restore the actual coupled profiles.** For one original presentation,
write $R^2=\sum_a g_R(a)\chi_a$ in its corresponding orientation,
absorbing its fixed multiplicative ray twist into $g_R$. Split
$g_R=g_{\rm sf}+g_{\rm rep}$ by whether the total column $a$ is
squarefree. The first part consists of a fixed finite sum of convolutions
of $4,6,8,10,12$ distinct primes, each exceeding $2A$.
Partition their norms dyadically, retaining the two original $V$ factors
and the fixed finite ordering/grouping coefficients.

Proposition 7.2 is literally stated for independent smooth prime
weights, so the two coupled product profiles require an interface.
Apply log-Fourier inversion to each original $V$ factor. For a prime
in a fixed dyad, the separated weight has the form
$\eta(x)\rho(F_jx/A)x^{it}$, with a fixed compact annular cutoff $\eta$.
The logarithmic derivatives of $\rho(F_jx/A)$ are uniformly bounded:
where a derivative is nonzero, $F_jx/A$ lies in $[2,4]$.
Lemma 7.1's proof uses a finite order $J>1+12/\tau$ after the fixed
height parameter $\tau$ is selected. Its shifted segment, horizontal
joins and absolute-line tails therefore cost a fixed finite profile
seminorm, polynomially in $(1+|t|)^J$. The common log-Fourier measures
of the two $V$ factors are Schwartz; Minkowski integrates these
polynomial costs. No row spectral parameter is moved and no infinite
local contour is assumed. This finite-seminorm dependence is extracted
from the proof, rather than an arbitrary-coupled-weight hypothesis
added to the literal proposition.

The common family $\mathcal X_u$ in source §6.1 already includes the
fixed finite $S$-ray twists and both orientations. It supplies this
interface for the actual presentations, not arbitrary multiplicative
modulus-one functions. Restore all original finite components by
$L^4$ Minkowski, paying their interference and fixed constants.
For the same nonnegative physical row weight $\Omega$, write
$T_U(c)=\sum_u\Omega(u)|\sum_a c(a)\chi_a(u)|^2$.
Use Proposition 7.2 with $Y=U$, $c=1/12$, $k_0=12$, and the actual
squared-coefficient normalization $D^{-2}=U^{-1}$. It gives

$$
T_U(g_{\rm sf})\ll U^{B_*+\varepsilon}+U^{13/12+\varepsilon}.
\tag{C34}
$$

Indeed its raw exponents are $\kappa_6=B_*+1$ and $13/6-c$.
The repeated columns are still cube-free and each contains $p^2$ for
some $q_p>2A$. Ideal counting and the existing divisor envelope give

$$
\#\operatorname{supp}g_{\rm rep}\ll U/A,\qquad
\|g_{\rm rep}\|_2^2\ll A^{-1}U^\varepsilon.
$$

Here one sums $U/q_p^2$ over $q_p>2A$. The unchanged
$F_6(U,U)\ll U^{7/6+\varepsilon}$ pays
$T_U(g_{\rm rep})\ll U^{13/12+\varepsilon}$, and Cauchy pays the
full cross term:

$$
|T_U(g_R)-T_U(g_{\rm sf})|
\ll U^{(B_*+13/12)/2+\varepsilon}.
\tag{C35}
$$

Thus the available rough-prime theorem returns the same $B_*$ for
this component. This identifies an applicable existing supplier, not
a strict inverse-fourth gain. In the exact decomposition
$M_{\mathrm{II},b}=R+(M_{\mathrm{II},b}-R)$, the other part and its
joint interference remain to be estimated. No domination by the full
remainder or by a same-support positive coefficient is used.

### The new remainder also excludes a norm-only payment

Reuse the [Bohr–Haar coefficient inequality](#actual-inverse-coefficients-a-limit-of-norm-only-refinements)
and the [fixed-ray prime-pair counting interface](#the-original-convolution-norm-before-sixth-power-compression)
for a fixed nonzero smooth complex $V$. Choose a compact interval $I$
with nonempty interior such that $|V(xy)|$ is bounded below for
$x,y\in I$. Distinct good primes with
$q_p,q_q\in\sqrt D\,I$ have $q_p,q_q\gg U^{1/4}\gg A$.
Equation (C33), with $r_A(pq)=1$, gives
$\lambda_{\mathrm{II},b}(pq)=2$.
The existing prime-ideal theorem supplies
$\gg\sqrt D/\log D$ primes in this interval; unique ideal
factorization gives $\gg D/(\log D)^2$ distinct unordered products.
Consequently the actual remainder has normalized coefficient mass

$$
D^{-1}\sum_d|\lambda_{\mathrm{II},b}(d)V(q_d/D)|^2
\gg (\log D)^{-2}.
$$

For one fixed actual finite Fourier component, let
$M_{\mathrm{II},b}^2=\sum_a g_{\mathrm{II},b}(a)\chi_a$,
with its multiplicative unit-modulus ray twist included. The same finite
Bohr lift and Haar Plancherel inequality give

$$
\|g_{\mathrm{II},b}\|_2^2
\ge\left(D^{-1}\sum_d
 |\lambda_{\mathrm{II},b}(d)V(q_d/D)|^2\right)^2
\gg(\log D)^{-4}.
\tag{C36}
$$

Paying a strict full inverse-fourth gain entirely by reducing this
coefficient norm in the unchanged generic sieve would require
$\|g_{\mathrm{II},b}\|_2^2\ll U^{B_*-7/6-\nu}$ for some fixed
$\nu>0$, a negative power incompatible with (C36).
This is the existing norm-only obstruction applied to the actual new
remainder. It gives no lower bound for its physical row energy,
a masked correlation or the recombination of different finite
components. It assumes a fixed nonzero profile and makes no uniform
varying-profile assertion. The prime theorem and Haar inequality are
reused classical inputs; cancellation in the actual row kernel,
(C20), signed Robin restoration and RH remain open. No analytic Lean
certification or literature-priority claim is made.

### Cofactor recursion and the actual prime-slot capacity

The same truncated coefficient has an exact least-prime recursion.
For squarefree good $d$, define the algebraic extensions

$$
K_A(d)=\sum_{e\mid d}\mu(e)2^{\omega(e)}W(q_e/A),\qquad
\Lambda_A(d)=\mu(d)+K_A(d).
$$

On the original inverse annulus,
$\lambda_{\mathrm{II},b}(d)=\Lambda_A(d)$ with $A=U^{1/12}$.
For a smaller cofactor, $\Lambda_A$ is an algebraic extension, not a
claim about the original truncated-inverse coefficient with the same
$z$. Dividing the divisors of $pm$ according to whether they contain
$p$, for $p\nmid m$, gives

$$
K_A(pm)=K_A(m)-2K_{A/q_p}(m),\qquad
\Lambda_A(pm)=\Lambda_A(m)-2\Lambda_{A/q_p}(m).
\tag{C37}
$$

Choose a fixed prime-ideal order refining norm, and let $P^-(m)$ be its
least factor, with $P^-(1)=\infty$. The actual polynomial is therefore

$$
M_{\mathrm{II},b}(u)=D^{-1/2}
\sum_{m\ {\rm sf}}\psi_u(m)
\sum_{p\prec P^-(m)}\psi_u(p)V(q_pq_m/D)
 \left[\Lambda_A(m)-2\Lambda_{A/q_p}(m)\right].
\tag{C38}
$$

Its ordering restriction, threshold and cofactor phase remain joint
weights. Even on a smoothly separated block $PC\asymp D$, using only
a conditional prime bound $P^a$ and then taking absolute values over
all cofactors costs $D^{-1/2}CP^a=D^{a-1/2}C^{1-a}$.
It does not supply the original inverse bound without that extra
factor. An estimate retaining the cofactor phase is still required.

There is also a concrete limit on identifying the actual rough primes
with the fine auxiliary slots in
[Liu v2, §10.1 and Proposition 29.1](https://arxiv.org/html/2610.12234v2#S29).
Within that source's full hypotheses, including
$13/18\le\kappa_{\rm src}\le1$,
$\beta_*\le(1+\kappa_{\rm src})/2$ and its auxiliary length reserve,
the proof permits total selected widths

$$
z_M\le\frac{4-c}{20-4c}<\frac15,\qquad
z_S\le\frac c{12}=\frac1{18\kappa_{\rm src}}\le\frac1{13},
\qquad c=\frac2{3\kappa_{\rm src}}.
\tag{C39}
$$

The source selects whole factors from sufficiently fine, fixed prime
slots, with a fixed margin in its moment inequalities. Every actual
rough prime here has exponent at least $1/12+o(1)>1/13$, so none
fits the plain branch's capacity. The supported balanced semiprimes
$pq$ have two exponents $1/4+o(1)$, exceeding even the inverse
capacity $z_M<1/5$. A prime cannot be replaced by several smaller
prime factors to meet that hypothesis. External fine auxiliary slots
remain available, but their amplitudes have not been related to these
actual cofactor sums by a joint moment. Equation (C39) limits this
specified identification, rather than all amplitude-sensitive methods.

Finally, fix a squarefree good ideal $b_0$. For sufficiently large $U$,
$q_{b_0}\le A$, and distinct primes with $q_p,q_q>2A$ outside $b_0$ satisfy

$$
K_A(b_0pq)=K_A(b_0)=\mu(b_0),\qquad
\lambda_{\mathrm{II},b}(b_0pq)=2\mu(b_0)
\tag{C40}
$$

on the original annulus. For $b_0\ne1$ these terms lie in the
nonrough complement; they still contain the same balanced semiprime
cofactor, at scale $D/q_{b_0}$. If $S_X$ denotes the corresponding
normalized polynomial over $c=pq$ with coefficient $2$, this exact
subfamily contributes
$\mu(b_0)q_{b_0}^{-1/2}\psi_u(b_0)S_{D/q_{b_0}}(u)$,
including its original collision zeros. Thus removing the rough part
does not remove these coarse prime slots from the remaining coefficient.
This identity gives no lower bound for the whole row moment or for a
masked correlation, and does not preclude cancellation between different
small factors. The unproved input is a coarse-slot or conditional-cofactor
joint estimate on the same rows. The recursions and source-capacity
comparison are applications of existing arithmetic and moment inputs;
no new prime theorem, full inverse-fourth gain or Lean certification
is asserted.

## Finite signs in the remaining small-squarepart sector

The [original-family program and data](https://github.com/the-omega-institute/trureturing-experiments/tree/907f48d6d61c17f24628d2ed31f3f115598a3515/docs/reports/sextic-inverse-fourth#product-squarepart-correlation)
also evaluate the $P<U^{1/4}$ contraction in (C20) at the reported finite
scales, with the fixed trivial ray twist, every original good sixth-power-free row in
$U<q_u<2U$, all six unit multiples and the original collision zeros.
The strict cut is tested as the integer inequality $P^4<U$.

For unit weights on the inverse annulus $D/2<q_d<3D/2$ and the row
annulus $U<q_u<2U$, the integer-arithmetic computation at $U=2048$ gives

$$
E_{6,\,P<U^{1/4}}^\mu=\frac{747}{64}>0.
$$

Here $U^{1/4}<7$, the least good prime-ideal norm, so every retained pair
has $P=1$. This is the coprime squarefree-column sector. The flat values
on these finite norm grids can be realized by smooth profiles supported
in the same open annuli, placing the transitions between adjacent sampled
norms. This assertion supplies a fixed profile for that finite example;
it does not supply one common profile or uniform derivative costs across
scales. The positive value prevents a blanket all-scales nonpositive-sign
substitute for (C20); it does not disprove eventual nonpositivity for a
specified fixed profile.

A separate integer checker visits the four original ordered inverse-factor
slots and every physical unit row, without the grouped inverse plan,
pair plan or unit-orthogonality shortcut. It reproduces $747/64$. The
fixed smooth bumps from the earlier actual-family experiment also give
both observed signs for the small-$P$ contraction: approximately
$-0.1603369703$ at $U=128$ and $0.2490045477$ at $U=4096$. Those bump
values use binary64 and are not interval certificates.

The new split reconstructs the complete signed identity
$\mathcal T=H_2+E_{6,\,\mathrm{small}\ P}+E_{6,\,\mathrm{large}\ P}$;
its full smooth moments agree with the retained earlier baseline. These
finite outputs give no uniform power estimate or local Lean certification.
The upper bound required in (C20), full inverse-fourth improvement,
signed Robin restoration and RH remain unproved.

## The actual radial column mean with both Type-II coefficients

Consider the corefree, $e=1$, common-column-gcd $1$ branch of the
Gauss interface in [J29](../Fourier/liu2026quasirhdual.md). Its
untwisted radial component has column coefficient
$c_s^{\rm rad}=\mathbf1_{s\ {\rm sf}}\sum_{uv=s}
b_U(u)b_U(v)V_1(q_u/D)V_2(q_v/D)$ after the fixed component scalars
are separated. This section estimates that component's column mean;
the other phases of $c_s$ retain their original definitions.
Here $K=\mathbb Q(\sqrt{-3})$, $q_d=Nd$, and ideals, equivalently their
chosen primary representatives, are counted once. Keep the original
fixed bad-prime set $S$, $D=U^{1/2}$ and $A=U^{1/12}=D^{1/6}$.
Reuse (C37), on the original squarefree inverse annulus, as
$b_U(d)=\lambda_{\mathrm{II},b}(d)=\mu(d)+K_A(d)$, with the same
$W=1$ on $[0,1]$, $W=0$ on $[2,\infty)$.

Let $V_1,V_2$ be fixed smooth compact annular profiles within that
annulus, and let $\Phi$ be smooth on their product annulus. Write
$\Psi(x,y)=V_1(x)V_2(y)\Phi(xy)$ and, for squarefree good $P$ with
$q_P\le U^{1/6}=A^2$, define

$$
\begin{aligned}
M(P;\Phi)&=\sum_{\substack{uv\ {\rm sf}\\(uv,SP)=1}}
 b_U(u)b_U(v)\Psi(q_u/D,q_v/D)
 =\sum_{\substack{s\ {\rm sf}\\(s,SP)=1}}c_s^{\rm rad}\Phi(q_s/U),\\
I_\Phi&=\int_0^\infty\!\int_0^\infty
 V_1(x)V_2(y)\Phi(xy)\,dx\,dy.
\end{aligned}
\tag{C41}
$$

The condition $uv$ squarefree includes $(u,v)=1$. There is no
replacement of either $b_U$ by a smooth weight. With
$\kappa=\operatorname*{Res}_{s=1}\zeta_K(s)$, put

$$
\begin{aligned}
C_P&=\kappa^2\prod_{p\in S}(1-q_p^{-1})^2
 \prod_{p\notin S}(1+2q_p^{-1})(1-q_p^{-1})^2
 \prod_{p\mid P}(1+2q_p^{-1})^{-1},\\
\Theta_A(P)&=\sum_{\substack{e,f\ {\rm sf}\\(e,f)=1\\(ef,SP)=1}}
 \frac{\mu(e)\mu(f)2^{\omega(e)+\omega(f)}
 W(q_e/A)W(q_f/A)}{\prod_{p\mid ef}(q_p+2)}.
\end{aligned}
\tag{C42}
$$

This is a coupled truncated inverse: primes cannot occur in both $e$
and $f$. In particular it is not the square of an independent sum.
The product defining $C_P$ converges absolutely, and $0<C_P\ll1$.

**Absolute-error expansion.** Unconditionally, for every $\varepsilon>0$
there are $c,c'>0$ and a finite $J$ such that, uniformly in this $P$,

$$
\boxed{\begin{aligned}
M(P;\Phi)&=U C_P I_\Phi\Theta_A(P)
 +O_\varepsilon\!\left(\mathcal N_J
 [Ue^{-c\sqrt{\log U}}+U^{19/24+\varepsilon}]\right),\\
|\Theta_A(P)|&\ll e^{-c'\sqrt{\log A}}.
\end{aligned}}
\tag{C43}
$$

Here $\mathcal N_J=\max_{0\le i,j\le J}\|\partial_x^i
\partial_y^j\Psi\|_\infty$ on a fixed rectangle containing the support;
constants depend on $K,S,W$, the supports and $\varepsilon$.
The statement also holds for any smooth $\Psi$ on that rectangle, with
$I_\Phi$ replaced by $\iint\Psi$. Fixed or polylogarithmic seminorm
costs remain explicit. This is neither a relative asymptotic nor a
lower bound for the actual $\Theta_A(P)$.

**The $K_AK_A$ term.** Expand the two divisor sums and fix $e\mid u$,
$f\mid v$. Only squarefree coprime $e,f$ outside $SP$ survive. For
$\Re s,\Re t>1$ their pair Dirichlet series is
$\zeta_K(s)\zeta_K(t)G_{e,f,P}(s,t)$. With $x=q_p^{-s}$,
$y=q_p^{-t}$, the local factors of $G$ are

$$
\begin{array}{c|c}
p\notin SefP&(1+x+y)(1-x)(1-y)\\
p\mid e&x(1-x)(1-y)\\
p\mid f&y(1-x)(1-y)\\
p\mid SP&(1-x)(1-y).
\end{array}
$$

The unforced factor has no linear terms. Thus this literal product is
normally convergent for $\Re s,\Re t>1/2$. No division by
$1+x+y$, which can vanish off the real axes, is used to continue it.
On fixed closed substrips it satisfies
$G_{e,f,P}(s,t)\ll_\eta(q_eq_fq_P)^\eta
q_e^{-\Re s}q_f^{-\Re t}$ for every $\eta>0$.
At $s=t=1$, forcing $p$ into $u$ changes its base factor by
$q_p^{-1}/(1+2q_p^{-1})=(q_p+2)^{-1}$; the same holds for $v$.
Excluding $p\mid P$ changes it by $(1+2q_p^{-1})^{-1}$.
These are exactly the factors in (C42).

Apply double smooth Mellin inversion, with
$\widehat\Psi(s,t)=\iint\Psi(x,y)x^{s-1}y^{t-1}\,dx\,dy$.
Shift each line from $1+\delta$ to $\sigma=1/2+\delta$.
The double residue is $U C_P I_\Phi/\prod_{p\mid ef}(q_p+2)$.
The two single-residue integrals and the double shifted integral have
combined error

$$
\begin{aligned}
E_{e,f}&\ll\mathcal N_J(q_eq_fq_P)^\eta
 \left[D^{1+\sigma}(q_e^{-\sigma}q_f^{-1}
                 +q_e^{-1}q_f^{-\sigma})
       +D^{2\sigma}(q_eq_f)^{-\sigma}\right],\\
E_{KK}&\ll_\varepsilon\mathcal N_J U^\varepsilon
 (D^{3/2}A^{1/2}+DA)
 \ll_\varepsilon\mathcal N_J U^{19/24+\varepsilon}.
\end{aligned}
\tag{C44}
$$

Indeed $q_e,q_f\le2A$, $|\mu(e)|2^{\omega(e)}\le\tau(e)$,
$\sum_{q_e\le2A}\tau(e)q_e^{-\sigma}\ll
A^{1-\sigma}\log(2A)$ and
$\sum_{q_e\le2A}\tau(e)/q_e\ll\log^2(2A)$.
Choose $\delta,\eta$ small in terms of $\varepsilon$ and use the
fixed-field polynomial vertical growth of $\zeta_K$ and rapid Mellin
decay. Horizontal integrals vanish. The precise scale arithmetic is
$D^{3/2}A^{1/2}=U^{3/4+1/24}=U^{19/24}$ and $DA=U^{7/12}$.
Both mixed contours are needed for the first exponent.

**All three terms containing $\mu$.** The mature analytic inputs here
are the classical fixed-field de la Vallée Poussin zero-free theorem,
its prime-ideal theorem, and smooth Mellin inversion (for the latter
see [DLMF §2.5](https://dlmf.nist.gov/2.5)). In this field
$\zeta_K(s)=\zeta(s)L(s,\chi_{-3})$. Precisely, one may fix $c_0,B_0>0$
so that its reciprocal is holomorphic, taking value $0$ at $1$, in
$\Re s\ge1-c_0/\log(3+|\Im s|)$ and is bounded there by a fixed
power of $\log(3+|\Im s|)$ after narrowing $c_0$.
The fixed conductor allows any fixed exceptional-zero issue to be
absorbed in $c_0$; there is no moving-conductor assertion. The associated
PNT gives the prime-ideal reciprocal sum bound used below. Ordinary
ideal counting gives $\#\{d:q_d\le X\}\ll_K X$.

For any fixed $C$ and smooth annular $F$, these inputs imply the uniform
deleted-factor Möbius bound

$$
\begin{aligned}
S_r(D;F)&:=\sum_{(d,r)=1}\mu(d)F(q_d/D)
 \ll_C\|F\|_{C^J}D e^{-c_C\sqrt{\log D}},\qquad q_r\le D^C,\\
\sum_{(d,r)=1}\frac{\mu(d)}{q_d^s}
 &=\zeta_K(s)^{-1}\prod_{p\mid r}(1-q_p^{-s})^{-1}.
\end{aligned}
\tag{C45}
$$

To see the uniformity, truncate smooth Mellin inversion at
$T=\exp(a\sqrt{\log D})$ and shift to
$\Re s=1-c_0/(2\log(3+T))$. On this rectangle the deleted product
costs only a power of $\log D$: split its primes at $(\log D)^2$.
For small primes, $q_p^{1-\Re s}=1+o(1)$ uniformly and
$\sum_{q_p\le X}q_p^{-1}\ll\log\log(3X)$ by the fixed-field PNT;
for the others use $\sum_{p\mid r}\log q_p\le C\log D$.
The large-prime contribution is $O(1)$.
Rapid decay pays the tails and horizontal joins for a sufficiently
large fixed $J$ and a suitable $a>0$. This proves (C45), with polynomial
$q_r$ costing polylogarithms rather than a power loss.

In the $\mu K_A$ term fix $v$ and take $r=\operatorname{rad}(SvP)$.
The inner profile $F_v(x)=V_1(x)\Phi(xq_v/D)$ has uniformly bounded
derivatives; $q_r\ll Dq_P\le D^{4/3}$.
The divisor expansion and ideal counting give
$\sum_v|K_A(v)V_2(q_v/D)|\ll D\log^2(2A)$.
Thus the complete four-term accounting is

$$
\begin{aligned}
M_{KK}&=U C_P I_\Phi\Theta_A(P)
       +O_\varepsilon(\mathcal N_J U^{19/24+\varepsilon}),\\
|M_{\mu K}|+|M_{K\mu}|+|M_{\mu\mu}|
 &\ll\mathcal N_J U e^{-c\sqrt{\log U}},\qquad
M=M_{KK}+M_{\mu K}+M_{K\mu}+M_{\mu\mu}.
\end{aligned}
\tag{C46}
$$

For $K\mu$ interchange the variables; for $\mu\mu$ the outer absolute
mass is $O(D)$. No Möbius-containing term has been discarded.

For completeness the subpower bound in (C43) follows from the same
classical contour. Fix $f$ in (C42), set $r=\operatorname{rad}(SPf)$,
and Mellin-invert its inner $e$ sum. Its Dirichlet series is
$\zeta_K(1+z)^{-2}h_r(z)$, where the good local factor of $h_r$ is
$[1-2q_p^{-z}/(q_p+2)]/(1-q_p^{-1-z})^2$ and the factor at
$p\mid r$ is $(1-q_p^{-1-z})^{-2}$.
This correction is normally convergent for $\Re z>-1/2$.
The simple pole of $\widehat W(z)$ at $0$ is canceled by the double
zero of $\zeta_K(1+z)^{-2}$. Shift to
$\Re z=-c_0/(2\log(3+T))$, now with
$T=\exp(a\sqrt{\log A})$. Since $q_r\ll A^3$, its deleted factors
again cost polylogarithms. The inner sum is
$O(e^{-c\sqrt{\log A}})$ uniformly in $f$; its outer absolute mass
is $O(\log^2(2A))$, absorbed by decreasing $c$. This proves (C43).
It supplies no unconditional fixed-power decay or nonzero main term.
This is a paper-level `repo-derived` application of classical inputs
to the actual coefficients, not a new zero-free theorem or a
literature-priority claim.

## The coupled Euler product under an explicit reciprocal strip

The two-variable series behind the actual $\Theta_A(P)$ in (C42) is,
initially for $\Re z,\Re w>0$,

$$
\begin{aligned}
F_P(z,w)&=\prod_{p\notin SP}
 \left(1-\frac{2(q_p^{-z}+q_p^{-w})}{q_p+2}\right)
 =\zeta_K(1+z)^{-2}\zeta_K(1+w)^{-2}H_P(z,w),\\
(H_P)_p&=\begin{cases}
\displaystyle\frac{1-2(q_p^{-z}+q_p^{-w})/(q_p+2)}
 {(1-q_p^{-1-z})^2(1-q_p^{-1-w})^2},&p\notin SP,\\[4pt]
\displaystyle\frac1{(1-q_p^{-1-z})^2(1-q_p^{-1-w})^2},&p\mid SP.
\end{cases}
\end{aligned}
\tag{C47}
$$

The correction $H_P$ is holomorphic for $\Re z,\Re w>-1/2$, by
normal convergence. On compact real substrips its unexcluded local
factor minus $1$ is bounded by a constant times
$q_p^{-2-\Re z}+q_p^{-2-\Re w}+q_p^{-2-2\Re z}
+q_p^{-2-2\Re w}+q_p^{-2-\Re z-\Re w}$.
Every exponent exceeds $1$ in that domain. The displayed denominators
cannot vanish there; there is no mixed polar divisor, and no division
by the possibly vanishing numerator is used. Uniformly in the imaginary
parts on such substrips, $H_P\ll_\eta q_P^\eta$ for every $\eta>0$.

**Reciprocal hypothesis.** For $1/2\le\beta<1$, let $R_\beta$ mean
that $\zeta_K$ has no zeros in $\Re s>\beta$ and, for every
$\delta>0$, there are finite $B_\delta,C_\delta$ such that

$$
\left|\zeta_K(\sigma+it)^{-1}\right|
 \le C_\delta(1+|t|)^{B_\delta}
 \quad(\sigma\ge\beta+\delta),
\qquad \zeta_K(1)^{-1}:=0.
\tag{C48}
$$

This is a hypothesis about the principal Dedekind zeta function itself.
It is stronger than the classical shrinking zero-free region used in
(C43); a nonprincipal Hecke bound does not replace it.

Under $R_\beta$, double Mellin inversion gives
$\Theta_A(P)=(2\pi i)^{-2}\iint
\widehat W(z)\widehat W(w)A^{z+w}F_P(z,w)\,dz\,dw$.
Move both lines to $\beta-1+\delta>-1/2$.
Each simple pole of $\widehat W$ at $0$ is canceled by the corresponding
double reciprocal-zeta zero, so neither shift produces a residue.
The fixed strip margin, (C48), normal convergence of $H_P$ and rapid
decay of $\widehat W$ pay both vertical integrals and horizontal joins.
This gives $\Theta_A(P)\ll A^{-2(1-\beta)+2\delta}q_P^\eta$.
Allocate $\delta,\eta$ to $\varepsilon$ using $q_P\le A^2$.
For reciprocal growth exponent $B_\delta$, derivative order
$J>2B_\delta+10$, enlarged for the ordinary zeta bounds in (C44),
suffices for these Mellin steps.

The same hypothesis moves the line in (C45) to $\beta+\delta$ and
gives $S_r(D;F)\ll\|F\|_{C^J}D^{\beta+\delta}q_r^\eta$.
Indeed the deleted product costs $q_r^\eta$ on each fixed positive
real substrip. Keep $q_r\ll D^{4/3}$ and repeat the three outer-mass
estimates in (C46); each Möbius-containing term is
$O_\varepsilon(\mathcal N_J U^{(1+\beta)/2+\varepsilon})$.
The $KK$ error is unchanged. Consequently

$$
\boxed{\begin{aligned}
M(P;\Phi)&=U C_P I_\Phi\Theta_A(P)
 +O_\varepsilon\!\left(\mathcal N_J
 [U^{(1+\beta)/2+\varepsilon}+U^{19/24+\varepsilon}]\right),\\
\Theta_A(P)&\ll_\varepsilon U^{-(1-\beta)/6+\varepsilon},\\
M(P;\Phi)&\ll_\varepsilon\mathcal N_J
 U^{1-(1-\beta)/6+\varepsilon}.
\end{aligned}}
\tag{C49}
$$

In particular, under $R_{7/8}$ the four exponents are explicit:

$$
\begin{aligned}
\Theta_A(P)&\ll_\varepsilon U^{-1/48+\varepsilon},\qquad
M(P;\Phi)\ll_\varepsilon\mathcal N_J U^{47/48+\varepsilon},\\
\frac{M(P;\Phi)}U
 &=C_P I_\Phi\Theta_A(P)
 +O_\varepsilon\!\left(\mathcal N_J
 [U^{-1/16+\varepsilon}+U^{-5/24+\varepsilon}]\right).
\end{aligned}
\tag{C50}
$$

The two unnormalized errors are $U^{15/16+\varepsilon}$ and
$U^{19/24+\varepsilon}$; also $M/D\ll_\varepsilon
\mathcal N_J U^{23/48+\varepsilon}$.
The [pinned primary manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex)
states the $7/8$ region in `thm:main`; `lem:logarithmic-control`
includes the principal regularizer and conditional reciprocal bound.
This numerical use is **source-conditional** on $R_{7/8}$, not a
classical unconditional zero-free theorem or certification of that
source's major proof.

Equations (C41)–(C50) supply the actual radial density input missing
from a direct use of [Xu–Sang v2, (3.9)](https://arxiv.org/html/2610.17675v2).
They do not give a full weighted Gram formula or a positive actual
theta main term. For a ray group of order $h$, two class indicators
give this trivial-trivial Fourier component coefficient $h^{-2}$;
general finite weights give their own trivial-trivial coefficient.
The remaining ray modes, unit and angular factors, common-$e$ signed
detector, all cores and column gcds, nonexceptional frequencies, bad
duals and their joint profile costs still require estimates on the
same original $\beta$ rows. No moving-$U$ replacement of $b_U$ is used.
The complete J29/J40 contraction, signed Robin restoration and RH
remain open; there is no Lean certification or priority claim here.

## Four-factor exceptional continuation

The four-factor exceptional, cutoff and interface results C51–C68,
and their exact frequency-residue continuation C69–C76, are in the
[Fourier note](../Fourier/liu2026quasirhdual.md#four-inverse-factors-on-the-same-coprime-realization).
They reuse C21–C50 here with their original hypotheses and scopes.
