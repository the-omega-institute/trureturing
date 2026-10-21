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

**Stop result.** None of these capacity, complete-energy, projection or angular/DDDS estimates gives a strictly stronger same-object input to the $8748087/10^7$ ledger; they do not lower $\theta$. The repository estimates remain conditional on their stated analytical inputs. A future improvement through this line requires a same-object floor-bin theorem, or a root-moment estimate compatible with Gao's full root-moment contract and providing a strict saving that survives every detector and final-comparison constraint. Reoptimizing the record's existing inputs does not constitute such a new estimate.
