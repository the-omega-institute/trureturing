---
bibkey: "iyer2025empirical"
authors: "Gautam Iyer and Raghavendra Venkatraman"
year: 2025
title: "Convergence of empirical measures for i.i.d. samples in W^{-alpha,p}"
doi: null
url: "https://arxiv.org/abs/2512.17794v1"
claim: "Proposition 2.2 computes the exact negative-Sobolev second moment of an i.i.d. empirical-measure error; its proof also treats unsmoothed point measures above the Hilbert embedding threshold."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# A collapsed posterior noise measure and its group variation

Iyer and Venkatraman, [arXiv:2512.17794v1](https://arxiv.org/pdf/2512.17794v1),
Proposition 2.2, PDF page 5, gives an exact second-moment identity for an
i.i.d. empirical measure on Euclidean space after Gaussian smoothing.
Section 5, pages 13–14, derives the identity by independence and centering.
The end of that proof permits zero smoothing when the Hilbert smoothness
index exceeds half the dimension. Theorem 1.1 addresses more general
Lp-based negative Sobolev norms. These are antecedents for measuring point
fluctuations in a topology weaker than measure total variation.

Chapter 42 of [the posterior-field volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_POSTERIOR_FIELD.md)
uses a length-four circle, an explicitly normalized Fourier norm, and
conditionally independent but heterogeneous Bernoulli labels only under
its auxiliary law. Its Hilbert second-moment identity is proved directly
by vanishing cross terms. Summability of the Fourier weights proves norm
continuity of a moving Dirac mass for s greater than one half. Neither
that computation nor the threshold is claimed as new. The Euclidean
i.i.d. theorem is not invoked as a theorem about the actual dependent
pair/path observations or their fixed-size posterior.

A second direct methodological precedent is Berend and Kontorovich,
*On the Convergence of the Empirical Distribution*,
[arXiv:1205.6711v2](https://arxiv.org/pdf/1205.6711v2).
Lemma 8, PDF page 5, bounds the expected l1 error of a countable empirical
distribution by the sum of square roots of its probabilities divided by
the square root of sample size. Equation (5) and Theorem 3, page 3,
give the resulting countable-support tail bound when that square-root
sum is finite. The elementary Cauchy–Schwarz step is exactly the
precedent for summing square roots of group intensities. The paper's
fixed countable i.i.d. sampling law differs from the changing arithmetic
groups and conditional label law here. Its l1 convention equals the full
variation norm of the signed error; Chapter 42 also uses full variation,
without a one-half probability-distance factor.

The `repo-derived` content is the actual-model combination. The same
posterior noise that has a resolved Brownian profile collapses to its
own Gaussian endpoint times a Dirac mass in the stated Hilbert norm,
while its aggregated whole-score-group variation grows as Q to the
one-quarter power with an explicit positive constant. Uniform actual
point-group occupancy, a nonlinear square-root Riemann sum and a
summable square-root-intensity tail estimate establish that constant.
Cumulative variance-clock convergence alone does not prove those steps.

The exact fixed-size posterior is handled by one complete label-vector
comparison and the simultaneous subset-center bound from
[Siripraparat–Neammanee's local-probability application](siripraparat2021local.md).
Applying that bound to the positive and negative center-error subsets
controls the sum of absolute errors. Group variation aggregates all
equal-score labels before taking absolute values; summing individual
label magnitudes gives a different statistic. One common data and label
realization couples the measure with the full endpoint and profile.

The conclusion concerns probability and distributional convergence in
the specified Hilbert and compact path spaces. It does not transfer
actual moments through total variation, claim an extra independent
Gaussian amplitude, assert a different path topology, or provide an
all-amplitude or growing-window theorem. The primary precedents delimit
the classical tools; the bounded comparison is not a global originality
certificate.

## First spatial moment after the collapsed mass

Chapter 43 of [the posterior-field volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_POSTERIOR_FIELD.md)
subtracts the exact moving point mass and resolves the first spatial
moment of the same posterior noise. In the explicitly normalized real
negative Sobolev space, differentiation of a moving Dirac mass is a
classical distributional operation. Its spatial derivative is the
negative of its distributional derivative. Fourier summability gives
the stated threshold and continuity directly; those facts are used
inside the model theorem and are not presented as new standalone results.

A direct precedent for the moment/Dirac-derivative expansion is Neyt
and Vindas, *Asymptotic boundedness and moment asymptotic expansion in
ultradistribution spaces*, [arXiv:1906.06232v3](https://arxiv.org/pdf/1906.06232v3)
(2019 preprint, version dated 17 August 2021). Equation (1), PDF page 2,
records the classical expansion with signed moment coefficients and
Dirac derivatives. Definition 1 and equation (19), page 9, specify its
test-function meaning; Theorem 5, page 10, concerns a fixed element of
the stated ultradistribution dual space. These are not norm-uniform
estimates for a changing random posterior measure. Chapter 43 proves
its own Hilbert remainder, weighted environment bounds and exact-center
transfer. No ultradistribution theorem is imported without its topology
and fixed-object hypotheses.

The Hilbert second-moment mechanism has the same elementary independence
and centering basis as Iyer–Venkatraman's Proposition 2.2, discussed
above. The new proof must use weighted second moments of the actual
count-group environment. The unweighted collapsed-measure estimate from
Chapter 42 cannot be divided by the much smaller spatial scale.
Instead a fresh Hilbert-valued exact-center bound follows from the
conditional Bernoulli density ratio: cancel its constant term, then
apply Cauchy–Schwarz and the fourth moment of the unweighted label sum.
This estimate acts directly on the difference-quotient coefficients.
It does not infer actual moments from posterior total variation.

Classical Gaussian random-measure integration describes the resulting
joint law. The dipole coefficient is the first mark integrated against
the same Gaussian noise that supplies the resolved profile. Symmetry
makes it independent of the total mass, while its covariance with each
finite profile value is explicitly nonzero. Subtracting the endpoint
projection to form the bridge preserves this covariance.

The actual-model bridge also proves weighted remote-group control,
including the low-count Poisson tail and the additive actual-row
comparison remainders. On a compact mark interval, exact Stieltjes
integration by parts expresses the first mark as a functional of the
already jointly convergent profile. Weighted tail control then removes
the truncation. This constructs the new coordinate on the same actual
label realization and the same limiting Gaussian noise, jointly with
the old threshold and capacity fields.

The `repo-derived` assertion is restricted to this compensated arithmetic
posterior construction, its exact moving center, and the stated joint
distributional limit. The distributional Taylor expansion, Gaussian
integrals, integration by parts and Sobolev threshold are classical.
No all-amplitude law, actual moment convergence, alternative path
topology or critical-regularity theorem is asserted. The moving center
cannot be replaced by zero merely from its convergence to zero: that
replacement requires control relative to the finer spatial scale.

## Critical logarithmic energy of the shrinking posterior measure

Chapter 48 of [the window-phase volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_WINDOW_PHASES.md)
returns to the original intensity sequence and the same signed measure
from Chapters 42–43. It examines finite Fourier cutoffs at powers of the
inverse spatial contraction scale. Its statement concerns a finite
quadratic statistic, not membership of an atomic measure in the critical
negative Sobolev space.

The logarithmic Fourier kernel is classical. Frerick, Müller and
Thomaser, *A Fourier Integral Formula for Logarithmic Energy*,
Potential Analysis 61 (2024), 685–699,
[DOI 10.1007/s11118-024-10125-9](https://doi.org/10.1007/s11118-024-10125-9),
recall the circle Fourier-series energy formula in equation (1), printed
page 686. Their Theorem 1, printed page 687, states a Euclidean mutual
logarithmic-energy formula with its integrability conditions. For
complex measures, absolute logarithmic integrability is material;
positive measures have a separate existence formulation. The signed
atomic self-energy in the present construction cannot simply be assumed
to satisfy those hypotheses. Every finite Fourier sum is nevertheless
well defined, and the chapter estimates that finite sum directly.

The relevant elementary uniform bound is that the harmonic cosine sum
through frequency N differs by a bounded amount from the minimum of
log N and log inverse separation. Taylor's inequality below the inverse
separation and summation by parts above it prove the bound. Replacing
the harmonic weights with the specified Sobolev weights changes the
kernel by a uniformly bounded amount. These facts remain classical
steps inside the model proof, not newly named mathematical results.

A second antecedent is Wiener's lemma. Cuny, Eisner and Farkas,
*Wiener's lemma along primes and other subsequences*, Advances in
Mathematics 347 (2019),
[DOI 10.1016/j.aim.2019.02.005](https://doi.org/10.1016/j.aim.2019.02.005),
[arXiv:1701.00101v6](https://arxiv.org/pdf/1701.00101v6)
(version dated 18 February 2023), Theorem 1.1, state the classical
Cesàro Fourier-power identity for a fixed finite complex Borel measure:
the limit is the sum of squared atom masses. This motivates the
high-frequency diagonal term. It does not provide a rate uniform in a
changing array of atom locations and random masses. The version's
qualification concerning a separate polynomial return-time example is
unrelated to the classical theorem and no such example is used here.

The `repo-derived` assertion is the simultaneous actual-posterior
transition across logarithmic frequency scales. All distinct count-group
separations have the same leading logarithm. Their off-diagonal terms
therefore retain the square of the same random total mass up to the
inverse contraction scale. Beyond that scale, the extra logarithmic
energy has a deterministic limiting slope, obtained from concentration
of the sum of squared whole-group posterior charges. The endpoint,
resolved profile, bridge and first spatial moment remain on the same
underlying label realization; no independent copy replaces a cross term.

To justify the deterministic slope, compact uniform actual group
occupancy is combined with whole-line tail control. Under the calibrated
product law the group fourth moments give concentration of the squared
charges. A separate absolute exact-center bound controls their change
under posterior centering, and one complete-vector comparison transfers
only probability statements. The uniform Fourier-kernel remainder is
bounded using the number of possible count groups and their squared
charges. This supplies a changing-array estimate that a fixed-measure
Wiener identity alone does not yield.

The result keeps the fixed amplitude, fixed sparsity exponent, original
intensity sequence, and fixed positive compact range of frequency
exponents. It asserts convergence in probability and joint distribution,
not convergence of actual energy moments, finite critical full-spectrum
energy, or a universal shrinking-window theorem. The classical primary
sources delimit the ingredients; the bounded source comparison does not
certify global originality.

## A quadratic fluctuation beneath the deterministic spectral slope

Chapter 49 of [the window-phase volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_WINDOW_PHASES.md)
examines the next fluctuation scale of the same whole-score-group energy.
Its centering is the observed environment's auxiliary variance, not an
unproved rate-level replacement by its limiting constant. The limiting
Gaussian coordinate is jointly independent of the endpoint, compact
profile, bridge and first spatial moment from the same label realization.

Normal limits for quadratic forms are classical. Peter de Jong,
*A Central Limit Theorem for Generalized Quadratic Forms*, Probability
Theory and Related Fields 75 (1987), 261–277,
[DOI 10.1007/BF00354037](https://doi.org/10.1007/BF00354037),
Definition 2.1, printed page 263, defines clean quadratic forms through
vanishing conditional expectations with independent underlying inputs.
Theorem 2.1, page 264, assumes negligible normalized row variance and a
normalized fourth moment tending to three. Both assumptions matter: the
following discussion explains that negligible row variances alone allow
a nonnormal chi-square limit. Theorem 5.2 gives another sufficient
criterion using tails and eigenvalues for an independent-input quadratic
form with zero diagonal.

Those results are antecedents for quadratic Gaussian limits, not
theorems about dependent actual observations or the exact fixed-size
posterior used here. The chapter uses the simpler independent group-array
Lyapunov theorem after conditioning on the observed environment. The
fourth moment of a centered squared group sum follows by expanding the
eighth moment of bounded independent labels. Mixed linear and quadratic
forms satisfy the same criterion. Only after their joint Gaussian limit
is established do vanishing mixed third cumulants prove independence.
The independent-array theorem, moment expansions and Cramér–Wold step
remain classical ingredients inside the model proof.

The additional actual-model obligation is a squared variance clock.
Ordinary cumulative variance convergence does not determine the sum of
squared group variances. Compact uniform point occupancy provides that
clock locally; the actual one- and two-row estimates bound second
moments of remote group occupancy and remove the cutoff. No four-row
actual comparison or independence of observed rows is assumed. These
estimates identify the explicit integral of the squared Gaussian
intensity as the quadratic fluctuation variance.

The sharper noise scale also requires a sharper use of the existing
exact-center bound. Its explicit rate makes the displacement of the
whole-group coefficient vector negligible after the new normalization.
A single full-window posterior comparison then transfers bounded tests
and events. Auxiliary moment calculations are not promoted into
convergence of actual unbounded quadratic moments.

The environment center is essential at the stated resolution: convergence
to a constant alone permits a displacement of order the fourth root of
the grid size, which diverges after division by its square root. Likewise,
alternating the variance mass between adjacent groups preserves the
cumulative clock but doubles its squared-clock limit. These are
counterexamples to insufficient inference rules, not counterexamples
within the actual observation model.

The finite high-frequency difference slope from Chapter 48 has a
remainder small even at this finer scale. It therefore carries the same
quadratic Gaussian coordinate. The random low-frequency mass term
cancels in its leading difference, with the cutoff-floor residual
controlled separately. This connects the spectrum and the grouped
posterior statistic without introducing a new independent label sample.

The `repo-derived` content is the actual squared-clock and posterior
transfer together with this same-realization second-order spectral law.
The assertion keeps the original intensity, fixed amplitude and beta,
fixed profile windows and fixed frequency exponents. It does not replace
the environment center by a constant without a convergence rate, assert
actual moment convergence, or import old-field jointness from marginal
limits. The comparison with classical quadratic-form theory is bounded
and does not certify global originality.

## Resolving the critical spectral transition

Chapter 50 of [the window-phase volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_WINDOW_PHASES.md)
resolves the cutoff at a fixed multiple of the inverse cluster width.
After subtracting the logarithmic total-mass square, the actual posterior
spectrum converges to a random curve built from the Fourier transform of
the same real Gaussian noise that supplies the spatial profile. Finite
resolved frequency bands remain random even conditional on the endpoint.
This is a finer statement than the leading logarithmic slope law.

Gaussian limits of empirical characteristic functions and quadratic
spectral functionals are classical subjects. John T. Kent,
*A weak convergence theorem for the empirical characteristic function*,
Journal of Applied Probability 12(3) (1975), 515–523,
[DOI 10.1017/S0021900200048324](https://doi.org/10.1017/S0021900200048324),
is a historical antecedent identified by its publisher abstract. Its
full theorem conditions are not used here. The chapter proves its own
conditional Fourier tightness from the already established actual
weighted variance clock and the independent auxiliary labels.

Richard A. Davis, Muneya Matsui, Thomas Mikosch and Phyllis Wan,
*Applications of Distance Correlation to Time Series*,
[arXiv:1606.05481v1](https://arxiv.org/abs/1606.05481v1),
Theorem 3.2 and Appendix A, Lemma A.1, are closer functional antecedents.
They establish Gaussian characteristic-function fields on compacts and
separate near-zero bounds for integrated squared fields under stationary
mixing, marginal/product moment and weight-integrability assumptions.
These mechanisms do not directly handle the present triangular posterior
label array, its random total mass, or its exponentially moving cutoff.
The chapter supplies those actual-model obligations explicitly.

Thomas Mikosch and Yuwei Zhao,
*The integrated periodogram of a dependent extremal event sequence*,
[arXiv:1503.04022v1](https://arxiv.org/abs/1503.04022v1),
[DOI 10.1016/j.spa.2015.02.017](https://doi.org/10.1016/j.spa.2015.02.017),
Theorem 15, is a functional Gaussian limit for the centered integrated
periodogram of a stationary regularly varying sequence. Its assumptions
include Condition (M1), anti-clustering and mixing-rate requirements,
summability of the extremogram, and a nonnegative Holder-continuous
weight with exponent greater than three quarters. It does not apply
directly to the conditional fixed-size posterior field here. In
particular, the singular inverse-frequency weight and the changing
microscopic cutoff require separate estimates.

Norbert Henze and Maria Dolores Jimenez-Gamero,
*Logarithmic energy distances and Gini covariance for Hilbert-valued
random elements*, [arXiv:2606.18365v1](https://arxiv.org/abs/2606.18365v1),
Section 4.1 and Theorem 4.1, study independent two-sample observations
under equality of distributions and a finite squared logarithmic-distance
moment. Their degenerate-kernel formulation is an antecedent for
non-Gaussian quadratic limits. The finite logarithmic moment excludes
positive-probability collisions between independent copies; the present
actual score law is atomic. Neither the independent-sample model nor its
diagonal integrability is silently imported into the posterior problem.
There is also an internal normalization discrepancy in v1: equation (4.2)
makes N times the Gini statistic equal to nm/N times the energy statistic,
whereas the two displayed limits in Theorem 4.1 differ by an additional
factor p(1-p). No normalization formula from that theorem is used here.

The deterministic calculation uses the classical harmonic-sum constant,
a summable correction between the Sobolev weights and reciprocal
integers, and a Riemann-sum estimate for an absolutely continuous
function divided by its argument. Subtracting the value at zero is
essential. An H1 bound controls that subtraction uniformly, including
the first frequency cell. The zero Fourier mode and both signs of the
frequency determine the explicit finite constant. These are classical
analysis ingredients within the model-specific argument.

The Gaussian field is driven by a real random measure. Both its ordinary
covariance and its covariance without complex conjugation must therefore
be retained. Its odd sine component is independent of the even cosine
component and the endpoint; its nonzero quadratic contribution proves
positive conditional band variance. Gaussian conditioning and fourth
moment identities remain classical and concern the limit object only.

The `repo-derived` contribution is the actual posterior H1 control and
exact-center transfer, the uniform constant-order cutoff expansion, and
the common-realization spectral curve with its residual conditional
randomness. The result keeps fixed frequency intervals and fixed
additive logarithmic cutoff intervals. It does not assert actual energy
moment convergence, a finite full critical Sobolev norm, a uniform
second-order expansion over fixed macroscopic exponent intervals, or
an unrestricted growing-frequency theorem. This comparison is bounded
and does not certify global originality.

## 增长谱尺度：对数二次型与独立 Gaussian 斜率

[窗口相位卷第 51 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_WINDOW_PHASES.md)
在原 lambda=Q³ 序列中，把频率上限同时扩大到 exp(u/sqrt(delta))/h，
其中 u 在固定正紧区间内变化。减去同一端点平方的主项及精确环境中心后，
整条谱曲线趋于随机仿射函数。截距是同一空间 Gaussian 测度的对数二次 Wiener 积分，
斜率是第 49 章的独立二次 Gaussian 坐标。以下文献覆盖经典工具及接近的先例，
不把它们计作新的概率机制。

Ivan Nourdin、Jan Rosiński，
*Asymptotic independence of multiple Wiener–Itô integrals and the resulting limit laws*，
Annals of Probability 42(2), 497–526 (2014)，
[DOI:10.1214/12-AOP826](https://doi.org/10.1214/12-AOP826)，
[arXiv:1112.5070v4](https://arxiv.org/pdf/1112.5070v4)，
是混合 Gaussian／非 Gaussian 极限的重要直接先例。
所引 v4 的 Theorem 3.4 对固定阶、多重 Wiener 积分的有限族，
在二阶矩一致有界下，把分块渐近矩独立等价为跨块平方的协方差趋零，
或全部非平凡跨块收缩趋零。这里的判据不是普通协方差趋零。
Corollary 3.6 另要求各块边缘收敛及极限边缘的矩确定性，才推出联合独立极限。

其 Theorem 4.7（PDF 第 22–23 页）更直接处理一块 Gaussian 极限和另一块可为非 Gaussian 的极限：
两块均由固定阶 Wiener 积分构成，第一块的最小阶不小于第二块的最大阶；
已有两块边缘极限、第二块边缘矩确定性及跨块普通协方差趋零时，
可得联合独立极限。这些 Gaussian 底空间、阶数和矩确定性条件不可省略。
在精确 Gaussian 参考数组中，对角平方涨落属于第二阶，
非对角对数型属于第二阶，线性轮廓属于第一阶。
对角型与非对角型的协方差精确为零；平方时钟、最大权消失及
Hilbert–Schmidt 逼近可分别验证其边缘极限。
对数极限的特征值平方可和，使中心化矩生成函数在零点邻域存在，故满足矩确定性。
这给出了该混合机制的经典对应。

实际约束后验标签并非 Wiener 积分。第 51 章先在一个辅助 Bernoulli 乘积律中，
对有限区间和与二次坐标证明联合 Gaussian 极限，再经有控制的阶梯核逼近建立独立性。
它没有凭不同阶的正交性推出独立性，也没有把 Gaussian 参考定理直接套到后验数组。
例如 G 与 G²−1 不相关而依赖；这足以否定只比较普通协方差的捷径。

Vlad Bally、Lucia Caramellino，
*An Invariance Principle for Stochastic Series II. Non Gaussian Limits*，
[arXiv:1607.03703v1](https://arxiv.org/pdf/1607.03703v1)，
给出另一个接近的非 Gaussian 二次型先例。
该版本 Theorem 1.4 对中心化、单位方差、独立输入及一致三阶绝对矩界，
以低影响量控制三次可微测试函数下的替换误差；此平滑版本不要求连续密度下界。
Theorem 1.1、1.5 的总变差结论则使用 (1.1) 的局部 Lebesgue 下界，
以及各阶矩控制、低影响和最高阶不退化条件。
有限 Bernoulli 组和是离散变量，不能直接满足这个 Lebesgue 下界。
Proposition 3.5（PDF 第 15–17 页）把一个方差型估计量的极限表示为二重 Wiener 积分；
其卷积核含对数奇点，证明明确拆开对角与非对角部分。
这是与对数核极限密切相关的已有构造，其输入结构、控制测度、核与观测模型均与本章不同。
第 51 章未使用未经核对的全局替换，也未主张自身获得总变差收敛到连续极限。

前一节所列 Henze–Jiménez-Gamero 的 logarithmic energy U-statistic
也是平方可积对数核与中心化 chi-square 级数的直接先例。
其独立同分布双样本、固定样本比例及平方对数距离可积条件仍为实质前提；
随机碰撞的原子对角不能径直赋予有限对数自能。
第 51 章删除的是实际完整得分组之间的精确对角，
各有限阶梯核先减去自己的有限对角均值，再作 L² 完备化；
这不涉及不存在的对数核对角迹。
该 2026 原文版本的规范化差异已在前节说明，本章不导入其中任何规范化公式。

本章所增加的模型结论依赖四个具体桥梁：同一真实支持下的不同组两行占据数界；
近对角线与远处相邻组的统一对数平方尾界；
先消去发散端点项后可用的精确中心误差率；
在整个固定正尺度区间上一致的有限 Fourier 尾估计。
无权尾质量收敛乘以发散的 log²Q 不能替代第二个桥梁。
同样，固定分辨率 Gaussian 曲线的再取极限会遗漏同时放大后仍存活的二次 Gaussian 涨落。
环境中心 V_M 不能只凭其趋于 gamma 就替换：还需要额外的增长尺度乘中心误差趋零。

经典 Fourier 级数、Wick 中心化、Hilbert–Schmidt 核逼近、Lyapunov 定理及 Gaussian 累积量
均保留为已有工具；本章的新增内容是这些工具在实际算术得分组与精确后验中的共同实现和统一谱律。
这里的文献对应是所列原文范围内的比较，不是全局原创性认证。
结论不包含实际谱能量矩的收敛、旧场联合性、变化振幅、增长空间窗口或有效有限起始尺度。

## Arithmetic-line variance bias and deterministic centering

Chapter 52 of
[the window-phase volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_WINDOW_PHASES.md)
adds a quantitative expansion of the actual calibrated posterior variance
clock on the original fixed Liouville-amplitude sequence. Its leading
relative bias is of order inverse intensity and depends explicitly on the
fractional part of the signal mean. The phase need not converge. This rate
permits deterministic centering in the quadratic fluctuation and the
simultaneous spectral curve of Chapters 49 and 51.

Stirling expansion, Gaussian moments and Poisson summation are classical
ingredients. The coefficient is a local Edgeworth-type coefficient with a
moving target. The substantive model calculation is the transfer from
dependent stationary pair/path observations and globally calibrated
posterior weights to a single primitive count-line mass, followed by a
uniform expansion on that line. Neither the Poisson comparison law nor
the auxiliary Bernoulli law is substituted for the actual observation
law. The theorem is repo-derived in this stated sense, without a global
originality claim.

J. P. Buhler, A. C. Gamst, R. L. Graham and A. W. Hales,
*Explicit error bounds for lattice Edgeworth expansions*,
[arXiv:1710.08845v1](https://arxiv.org/abs/1710.08845v1), study sums of a
fixed bounded integer-valued IID law. Their Theorem 1 expresses the
leading tilt about the mean through the third moment and a congruence
phase, and the subsequent bounds make the one-term approximation
effective. The fixed law, its span and its Fourier constants are part of
that statement. A congruence-dependent correction is therefore a
classical precedent; it is not a new general principle of Chapter 52.
That theorem does not itself provide a uniform local mass estimate for
the present triangular array whose primitive integer coefficients grow.

Sergey G. Bobkov, *Central limit theorem and Diophantine approximations*,
[arXiv:1706.09643v1](https://arxiv.org/abs/1706.09643v1), Theorem 1.1,
relates an Edgeworth-corrected Kolmogorov rate for fixed IID sums with a
finite fourth absolute moment to polynomial separation of the
characteristic function from modulus one, with logarithmic factors.
Corollary 1.2 specializes this relation to the four-point law on plus or
minus one and plus or minus an irrational parameter, using its finite
Diophantine type. Thus nonlattice support alone does not supply arbitrary
polynomial approximation rates. These are distribution-function
statements with stated arithmetic conditions; no shrinking local-density
or growing-span conclusion for the ultra-Liouville model is imported.
Both references here identify the exact arXiv versions; the manuscripts
also display later dates than their archive-version headers.

Dmitry Dolgopyat and Yeor Hafouta, *Edgeworth expansions for independent
bounded integer valued random variables*,
[arXiv:2011.14852v2](https://arxiv.org/abs/2011.14852v2), Theorem 1.5,
characterize classical local expansions through the characteristic
function and its derivatives at nonzero resonant points. Their
Theorem 11.1 explicitly covers triangular arrays, with polynomial and
trigonometric corrections. Its common bound on the absolute size of all
summands is essential to the stated resonance set and constants. The
present projected Poisson law has unbounded compound increments; a
bounded-jump decomposition would still have jumps growing with the
arithmetic denominator. The word triangular therefore does not itself
verify the uniformity needed here.

Yeor Hafouta, *Non-uniform Edgeworth expansions for weakly dependent
random variables and their applications*,
[arXiv:2511.06414v1](https://arxiv.org/abs/2511.06414v1), Theorem 8,
requires both the small-frequency logarithmic-characteristic derivative
bounds of Assumption 4 and the growing-frequency integral bound of
Assumption 6. Its conclusion is a distribution-function expansion with
polynomial spatial decay. This recent dependent-data result retains a
quantitative frequency hypothesis and does not by itself turn CDF errors
into the relative microscopic point-mass estimate used in Chapter 52.

Chapter 52 instead uses the explicit two-Poisson mass on the count line.
The actual one-/two-row relative point comparison gives an occupancy
error smaller than every fixed inverse power of the intensity, and the
calibration variance has zero first derivative at the midpoint. On the
deterministic line, the odd first correction cancels in a symmetric
Gaussian lattice sum. Poisson summation bounds the remaining nonzero
dual-grid contributions exponentially in the arithmetic denominator.
Integrating the even correction retains the moving floor phase and gives
the displayed bias coefficient. This mechanism does not require a
uniform nonlattice local limit theorem.

The result concerns convergence in actual-data probability and the
previously specified weak joint posterior limits. It does not identify
the auxiliary variance with the finite actual posterior mean energy,
prove actual moment convergence, describe the distribution of the floor
phase, extend the spectral parameter to zero, or give a useful finite
onset. The bounded comparison above distinguishes relevant classical
mechanisms from the actual-model synthesis; it does not certify the
absence of other antecedents.

## 连续谱尾的 Gaussian 化与混合 OU 极限

[窗口相位卷第 53 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_WINDOW_PHASES.md)
研究第 50、51 章已经定义的同一连续 Gaussian 极限对象。
减去线性均值和同噪声的非 Gaussian 截距后，余项恰为核
2Ci(omega exp(s)|x−y|) 的二重 Wiener 积分。
其方差为 16 exp(−s) integral rho² 加上 O(exp(−2s))；
在固定对数分辨率窗口内放大 exp((s+t)/2)，得到平稳 OU 过程。
该极限相对于整个原始 Gaussian sigma-field 混合收敛。
以下区分这一具体谱尾计算和已有的概率机制。

David Nualart、Giovanni Peccati，
*Central limit theorems for sequences of multiple stochastic integrals*，
Annals of Probability 33(1), 177–193 (2005)，
[DOI:10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621)，
[arXiv:math/0503598v1](https://arxiv.org/pdf/math/0503598v1)，
Theorem 1（所引电子重印版 PDF 第 3 页）固定实 isonormal Hilbert 空间上的混沌阶数 n≥2，
在方差趋于一时，把 Gaussian 收敛等价为四阶矩趋于三，或全部非平凡收缩趋零。
第 53 章的归一化核具有有界 Hilbert–Schmidt 范数及 O(exp(−s/2)) 的算子范数，
所以二阶混沌的一阶收缩的平方范数为 O(exp(−s))。
这直接验证该经典定理在每个非退化有限线性组合上的条件；
退化组合直接在 L² 中趋零。标量 Gaussian 机制不是新增理论。

Giovanni Peccati、Murad Taqqu，
*Stable convergence of multiple Wiener–Itô integrals*，
[arXiv:math/0604530v1](https://arxiv.org/pdf/math/0604530v1)，
Definition IV（PDF 第 7 页）以与参考 sigma-field 上变量的联合特征函数刻画稳定收敛。
Theorem 7（第 7–8 页）是更广的稳定混合律结论，使用适应的广义积分、
投影分解、早期投影范数消失、嵌套 sigma-fields 及积分范数平方的概率极限。
第 53 章不未经构造就假定这些附加结构；它直接删去任意固定有限组 Gaussian 坐标，
用算子范数控制删去部分的 L² 误差，再以柱函数的 L¹ 逼近取得混合结论。
这是经典投影与稳定收敛方法的具体应用。

Ciprian A. Tudor，
*Joint convergence in Wiener chaos via transport hierarchy and Malliavin covariances*，
[arXiv:2606.14812v1](https://arxiv.org/pdf/2606.14812v1)，
Theorem 1（PDF 第 7–8 页）对固定阶 p≥2 的多重 Wiener 积分，
在其分布趋于方差严格为正的 Gaussian 时，给出与同一 Gaussian 空间上
任意固定平方可积变量的联合独立极限。
这直接涵盖本章每个非退化标量组合与固定谱截距、端点或线性坐标的渐近独立性。
该 v1 的 arXiv 页眉日期为 2026 年 6 月 12 日，正文日期为 6 月 16 日；
引用以明确版本为准，不把此固定变量结论算作本仓新机制。
从有限维结论到 C(I) 路径仍须本章的统一增量估计。

Shuyang Bai、Mamikon S. Ginovyan、Murad S. Taqqu，
*Functional Limit Theorems for Toeplitz Quadratic Functionals of Continuous time Gaussian Stationary Processes*，
[arXiv:1501.05574v2](https://arxiv.org/pdf/1501.05574v2)，
研究实平稳 Gaussian 过程在增长时间区间内、对固定差核的中心化二次泛函。
Theorem 2.1（PDF 第 2 页）在全文的 f,g 可积前提下，要求 fg 同时属于 L¹、L²，
并要求所列方差极限。Theorem 2.2（第 3 页）的 C[0,1] Brownian 极限另用
协方差 r 属于 Lᵖ、生成核 a 属于 Lᑫ，且 p,q≥1、1/p+1/q≥3/2。
这提供二次型、协方差时钟与四阶矩路径紧性的直接先例。
本章的移动高通乘子作用在带权 Gaussian 测度上，
尚未建立与该固定核、增长观察区间模型的等价关系。
Ci 核不绝对可积；原实噪声 Fourier 场的非共轭协方差又依赖两频率之和，
不能把它直接当成该文的实标量平稳过程。

Samir Ben Hariz、Duc-Quang Bui、Youssef Esstafa，
*Quantitative central limit theorem for an integrated periodogram via the fourth moment theorem*，
[arXiv:2604.00642v2](https://arxiv.org/pdf/2604.00642v2)，
Theorem 2.1（PDF 第 2 页）处理离散实平稳 Gaussian 序列和固定偶实谱权重。
其 f,g 可积，且分别写成零点幂次乘慢变函数，指数在 (−1,1)，两指数之和小于 1/2。
定量 Wasserstein 率另外要求 (2.3) 的相对局部光滑性。
该文通过二阶混沌、方差、收缩和算子迹控制正态逼近，是相邻的近期结果；
它未直接给出本章移动至无穷的频率截断及对数分辨率 OU 路径，
本章也不借用未经验证的 Wasserstein 率。

本章的具体连接是：同噪声谱截距与曲线之差的 Ci 核；
余弦 Plancherel 给出的精确双尺度内积；带权高通算子的范数衰减；
以及由此计算的方差系数、统一协方差误差和路径紧性。
Fourier 变换、谱分解、四阶矩定理、有限投影及 Brownian 时间变换均为已有工具。
所列原文中未见同时陈述该曲线、余项、常数与路径耦合的定理；
这是有限文献范围内的比较，不是全局原创性认证。

混合收敛允许联合保留整个旧噪声产生的任意固定可分空间随机对象，
却不表示给定整个旧噪声后的条件律依概率趋于 Gaussian：
前极限在该 sigma-field 下已知，条件特征函数的模恒为一。
本章没有把此连续对象的再取极限代入实际数据的弱收敛，
不提供实际增长参数近似率、实际后验矩收敛或 u=0 的路径延拓。

## 实际谱曲线的移动边界与端点障碍

[谱边界层卷第 54 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
在原来的实际成对样本、连续路径和固定 Liouville 序列中研究同一精确中心谱曲线。
只要左边界 a_M 趋零而 a_M/sqrt(delta) 发散，整个移动区间上的谱曲线
都一致逼近原来的随机截距加 Gaussian 随机斜率；不要求额外的 log Q 分离。
但完整闭区间上的曲线不满足 J1 紧性：在宽度 c sqrt(delta) 内，
同一实现的谱增量收敛到一个非零的有限频带二阶 Wiener 积分。
该章为 repo-derived 的实际模型桥接；以下工具及相邻结论已有文献。

Christian Döbler、Mikołaj J. Kasprzak、Giovanni Peccati，
*Functional Convergence of U-Processes with Size-Dependent Kernels*，
[arXiv:1912.02705v3](https://arxiv.org/pdf/1912.02705v3)，
Section 2 使用共同分布的独立输入及固定阶数的对称核，允许核随样本量变化。
Theorem 3.1（PDF 第 8 页）要求归一化 Hoeffding 分量方差极限、
指定收缩范数趋零以及带额外正幂余量的收缩有界性，得到所列 Gaussian 过程极限。
这是变化核的函数极限须另行控制紧性的直接先例。
本章的索引是对数频率，条件组和非同分布，核又与实际得分格相关；
未建立它与该顺序 U 过程的等价关系。
这里的有限频带极限和保留的谱截距属于非 Gaussian 二阶混沌，
所以不能直接套用该文的 Gaussian 过程结论。

Ivan Nourdin、Guillaume Poly，
*Convergence in law in the second Wiener/Wigner chaos*，
[arXiv:1205.2684v3](https://arxiv.org/pdf/1205.2684v3)，
Proposition 2.1 及其后累积量公式（PDF 第 4 页）给出实对称平方可积核的谱表示：
二阶 Wiener 积分与 sum_j lambda_j (G_j²−1) 同分布，
第 m 阶累积量为 2^(m−1)(m−1)! sum_j lambda_j^m。
在本章已识别的 Gaussian 极限空间中，有限频带核有界、对称且不为零，
故其方差严格为正，四阶矩至多为方差平方的 15 倍。
结合经典 Paley–Zygmund 不等式，即得明确的正概率增量下界。
这一计算只作用于极限对象，没有把有限精确后验标签当作 Gaussian，
也没有通过总变差比较转移实际无界矩。

Andreas Søjmark、Fabrice Wunderlich，
*Weak Convergence of Stochastic Integrals on Skorokhod Space in Skorokhod's J1 and M1 Topologies*，
[arXiv:2309.12197v1](https://arxiv.org/pdf/2309.12197v1)，
Appendix A、Definition A.1（PDF 第 65 页）给出有限闭区间上的 J1 度量，
时间变换是固定两端点的递增同胚。
由此定义，J1 紧集在左端点必须一致右连续；本章用收敛子列和时间变换直接证明这一必要条件。
该文主要的随机积分收敛定理另外要求联合收敛及半鞅分解等条件，
本章不借它把后验曲线宣称为鞅，也不作 M1 或其它拓扑的结论。
既有 Whitt 条目的半直线紧性模数有末区间约定；本章的左端点证明直接在有限闭区间内完成。

前一节所引 Ben Hariz–Bui–Esstafa 的 2026 年积分周期图定理，
要求实平稳 Gaussian 输入及固定谱权重，还不能提供当前实际后验数组的移动区间余项。
原来的条件 Bernoulli 表示、补集局部极限定理与精确中心估计沿用本卷相应条目及其文献来源。
有限余弦和、Ci 恒等式、一维 Sobolev 不等式、Gaussian 乘积公式和紧集判据都是经典工具。

新增连接是保留有限 Ci 核后，先对空间格上的条件方差加权，
得到统一的 exp(−s) 二阶界，再把单位区间的最大值界求和。
实际不同组的两行占据数估计足够供给该平均界；辅助标签独立性供给二次型等距式。
统一精确中心位移和一次完整后验向量比较再把最大值事件送回实际模型。
端点障碍使用同一实现的两个固定分辨率，因此没有把增长参数代入固定参数弱极限。

所核原文未直接给出这一完整模型、尺度、共同噪声及端点下界的联合陈述；
这是有界文献比较，不是全局原创性认证。
结论保持原固定幅度、固定 beta 和固定右端点，不主张任意左边界序列的必要充分条件、
实际无界矩收敛、变化右端点、其它路径拓扑或未知方向下的新后验定义。

## 谱边界层的完整轮廓与尺度分离判据

[谱边界层卷第 55 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
把实际谱曲线减去同一随机截距和线性项，在内层时间 s=u/sqrt(delta) 上观察。
该余项经 s/(1+s) 紧化后，联合收敛到同一实 Gaussian 噪声上的 Ci 二阶积分曲线。
极限在无穷远连续归零，保留与原截距、端点、空间轮廓、桥和偶极子的共同来源；
原 Gaussian 斜率独立于这一整族对象。
这给出外层仿射近似误差趋零的必要充分条件：左边界与 sqrt(delta) 的比值发散。
比值趋于有限 c 时，最大误差收敛到该同噪声极限曲线在 [c,infinity) 的绝对值上确界。
比值有界还给出显式非消失概率下界，未用实际后验的无界矩收敛代替概率结论。

Shunsuke Imai，*Gaussian Approximation for High-Dimensional Second-Order U and V-statistics
with Size-Dependent Kernels under i.n.i.d. Sampling*，
[arXiv:2511.08870v1](https://arxiv.org/pdf/2511.08870v1)，2025 年 11 月 12 日提交，PDF 日期为 13 日。
Section 2 允许不同可测空间上的独立非同分布输入和随样本量变化的对称核族。
Section 3.1 要求各二阶核具有四阶矩、各坐标方差为正；
Theorem 1（PDF 第 7 页，相关误差定义在第 6–8 页）
给出高维矩形事件上的 Gaussian 近似误差，显式依赖收缩项和矩项。
应用为渐近定理时，必须另外证明这些误差趋零。
Appendix A.2、Theorem 2（PDF 第 15 页）
为具有 L^(q∨2) 矩的有限族退化对称核给出最大不等式，
包含 q+log p 因子及条件积分平方核的范数。
因此该文不限于同分布组，也不是仅对固定核的结果。
但它不自动提供这里的实际占据数比较、精确中心和完整后验向量转移。

尤其在固定有限 s 处，本章非零实对称核 K_s 的算子具有非零特征值，
一阶收缩的平方范数是 sum_j lambda_j(K_s)^4>0。
其二阶 Wiener 积分的第四累积量严格为正，故内层极限不是 Gaussian。
不能把上述 Gaussian 近似结论直接用作本章完整内层曲线的极限。
有限参数格的最大不等式也仍需解决格间控制和紧化端点；
本章分别以固定区间 H1 紧嵌入及可求和的尾部估计处理这两个义务。

前节 Döbler–Kasprzak–Peccati 1912.02705v3 的函数极限定理
使用共同分布的独立输入、指定 Hoeffding 方差和收缩条件。
其变化核紧性方法是经典先例，但 Gaussian 顺序过程的结论
不直接识别当前非 Gaussian 内层及其与原谱截距的联合来源。
这里同时逼近 H 和有限族 K_s，以同一空间分块、同一组标签得到所有二次坐标；
这一步防止把分别成立的边缘极限拼成未经证明的联合极限。

前节 Søjmark–Wunderlich 2309.12197v1 的 Appendix A
在第 65 页定义紧区间 J1 时间变换，第 66 页说明连续极限处的一致收敛性质。
本章使用这一性质处理移动取值和移动下端点的最大值。
从每个固定内层区间收敛到紧化区间收敛，还需单独控制无穷远：
单位区间 Sobolev 界可求和，先得到极限几乎处处归零，
再以同一实际尾部概率界移除连续截断。
原始右端点和人工零延拓处的左跳也在这个尾部界内，
未借半直线局部拓扑的端点约定省略它们。

Nourdin–Poly 1205.2684v3 的 Proposition 2.1 及累积量公式
供给第二混沌的谱表示和四阶矩上界。
本章另在 Ci 为负且绝对值至少为一的近对角带上给出一致正方差下界，
结合 Paley–Zygmund 和开集 Portmanteau，得到有界比例序列的 1/60 概率障碍。
这些经典工具作用于已识别的极限；回到实际数据只转移事件和有界测试。

本章的 repo-derived 连接是实际完整边界层、原截距和旧空间对象的共同耦合，
紧化端点的可求和控制，以及由非退化内层推出的精确尺度分离判据。
H1 紧嵌入、连续映射、截断逼近、Gaussian 谱公式及概率不等式均非新工具。
所核原文未直接陈述这个实际模型及联合尺度结论；比较仅限所查文献，不认证全局原创性。
固定幅度、固定 beta、固定 U、条件先验空间与无条件固定支持的边界保持不变。
同时改用确定性 gamma 中心时余项逐样本完全相消，并非另一次渐近近似。
本章不证明增长 s_M 下放大余项的实际 OU 极限、实际后验矩收敛、变化 U 或其它拓扑。

## 实际增长频率的 OU 极限与网格解析条件

归属：`repo-derived`。
对应 [谱边界卷第 56 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。
该章把固定紧区间上的连续第二混沌 OU 尾极限连接到原始平稳独立对和连续路径实验，
允许任意确定性 s_M→∞、exp(s_M)δ→0，不另要求幂次或对数分离余量。
承重新增内容是增长核心的实际方差相对误差、放大后的精确中心控制、
一个共同组向量的定量 Gaussian 耦合、零对角 Ci 采样的平方核误差，
以及同一联合极限中与旧二次坐标和整个旧噪声的独立性。
有限截距是定义 54.1 的实际统计量；只有相同弱极限的另一截距不足以替代它。

Siripraparat–Neammanee，*A local limit theorem for Poisson binomial random variables*，
ScienceAsia 47 (2021), 111–116，
[DOI 10.2306/scienceasia1513-1874.2021.006](https://doi.org/10.2306/scienceasia1513-1874.2021.006)，
Theorem 2，第 112 页，是前述 Bernoulli 局部近似的来源。
独立 Bernoulli 输入可有不同成功概率；总方差 σ²>1 时，
点概率与匹配正态密度的最大绝对差为 O(σ⁻²)。
本章只把它用于辅助独立标签律，先证明补集方差与合法条件计数，
再推出一次完整后验向量比较。
在每个增长核心组中，方差 d_j≥q^(9/10)；
截断标准化坐标于 d_j^(1/6) 后对局部误差求和，给出 CDF 误差 O(d_j^(-1/3))。
逆分布函数共同耦合再使全部核心组同时接近同一个 Gaussian 向量。
局部定理本身不声称实际观测行独立，也不提供精确后验中心的放大误差。

Nourdin–Peccati–Reinert，*Invariance principles for homogeneous sums:
Universality of Gaussian Wiener chaos*，Annals of Probability 38 (2010), 1947–1985，
[arXiv:0904.1153v2](https://arxiv.org/abs/0904.1153v2)，2010-11-05，
Theorem 7.1，PDF 第 26 页，给出独立中心单位方差输入的齐次和替换原理。
该处要求输入三阶绝对矩一致有界、对称核在对角线上消失、
各坐标方差为一，并控制各输入最大影响量之和。
对三次可微且三阶导数有界的测试，误差受最大影响量平方根控制。
标准化核心组的四阶矩至多 3+d_j⁻¹，满足所需矩界；
固定有限个归一化异组核的影响量和由平方核范数控制，
最大影响量则由算子范数趋零推出。
它因而是有限维异组替换的可用经典路线，
但不直接包含对角二次坐标 T_M、整个变化频率路径或实际后验转移。
本章的共同逆分布耦合同时承担这些额外义务。

Döbler–Peccati，*Quantitative de Jong theorems in any dimension*，
[arXiv:1603.00804v4](https://arxiv.org/abs/1603.00804v4)，2016-12-20，
Theorem 1.7，PDF 第 10 页，研究独立输入上固定阶数、
中心单位方差 Hoeffding 退化 U-statistic 的固定有限维向量。
条件包括协方差收敛、最大影响量趋零、四阶矩趋于三，
以及相同阶数坐标的混合平方条件。
所核 v4 原 PDF 在条件 (iv) 中将标准化 Gaussian 恒等式印为
E[N(j)²N(k)²]=1+Σ(j,k)²；正确式是 1+2Σ(j,k)²。
相同坐标的四阶矩为三而不是二，且该陈述允许半正定协方差。
这是此指定版本原页的公式缺项，不据此判断其他版本或整个 de Jong 机制。
本章不使用该印刷公式，而以中心 Gaussian 平方的特征函数
对所有混合线性组合直接证明联合 Gaussian 收敛。

de Jong 1987 的广义二次型定理、Nualart–Peccati 2005 的固定混沌定理
及前节已核的第二混沌谱表示是同一 Gaussian 极限机制的经典先例。
这里算子范数趋零与有界 Hilbert–Schmidt 范数使四阶收缩消失。
对角坐标的算子范数为 O(√δ)，与异组 Ci 核的 Hilbert–Schmidt 内积严格为零；
只有在联合 Gaussian 性已证后才从此推出独立性。
固定有限秩投影删除界再将新联合对象与整个旧 Gaussian 噪声分离。
先前所核 Tudor 2606.14812v1 的固定旧变量结论不能直接替代
对移动 T_M 的这个联合论证。

Döbler–Kasprzak–Peccati，*The multivariate functional de Jong CLT*，
[arXiv:2104.01858v3](https://arxiv.org/abs/2104.01858v3)，2022-03-17，
Theorem 1.4，PDF 第 3 页及 Conditions 1.1–1.3，
使用部分样本索引过程、极限方差时钟、加强的 Lindeberg 条件及末端四阶矩条件。
本章参数改变每一对上的 Ci 核，不是逐次纳入观测的索引。
因此该定理不直接给出所需过程紧性；
本章在离散网格上证明二阶增量 O(|t-v|)、四阶增量 O(|t-v|²)，
再使用经典 Kolmogorov 判据。

Hao–Barnett–Martinsson–Young，*High-order accurate methods for Nyström
discretization of integral equations on smooth curves in the plane*，
[arXiv:1112.6262v2](https://arxiv.org/abs/1112.6262v2)，2012-11-21，
§1，PDF 第 1–3 页，讨论光滑周期曲线上的对数奇异核及经过近对角修正的高阶求积。
arXiv 元数据的标题用语略有不同，为 *High-order accurate Nystrom
discretization of integral equations with weakly singular kernels on smooth curves in the plane*。
其设置不直接覆盖本章未作求积修正、同格置零、频率增长的 Ci 核。
本章将同格、邻格和远格分别估计，得到平方 Hilbert–Schmidt 误差
O(r(1+|log r|²))+O(exp(-cH_Q²))，r=exp(s_M)δ。
没有从该文移入某个未经核对的数值收敛阶。

所核来源没有直接给出本章原始补偿模型的完整联合结论；
这只是所查范围内的比较，不认证全局原创。
Fourier 乘子、Gaussian 谱展开、局部极限、概率耦合、格点求和和有限秩投影均为经典工具。
本章的 repo-derived 综合明确补上其与实际同一数据实现之间的误差及共同来源关系。
结论固定原幅度、beta 和 λ=Q³ 序列，紧区间保持固定；
不声明临界网格的实际定理、任意自适应频率、增长空间窗口或实际后验矩收敛。

## 临界谱网格的离散协方差、共振与尺度分离

归属：`repo-derived`。
对应 [谱边界卷第 57 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。
在原始两种实际实验中，exp(s_M)δ 趋于固定正数时，
放大余项的协方差保留整数距离上的 Ci 级数，得到非平稳 Gaussian 过程。
此结论继续使用同一完整标签向量及有限截距，并与旧噪声和移动二次坐标联合识别。
增长核心上的定量替换沿用第 56 章；新的临界协方差与调和行和估计
直接作用于采样核，不以连续谱协方差代替网格关系。
同一临界过程族还有小网格的函数 OU 极限及精确共振的方差降阶。
对同一实际数据同时取低于网格和临界网格两个尺度，
交叉协方差的 O(√r(1+|log r|²)) 界使两个极限相互独立；
这一联合断言以一个共同耦合证明，不由边缘极限拼接。

de Jong，*A Central Limit Theorem for Generalized Quadratic Forms*，
Probability Theory and Related Fields 75 (1987), 261–277，
[DOI 10.1007/BF00354037](https://doi.org/10.1007/BF00354037)，
Definition 2.1 和 Theorem 2.1，印刷第 263–264 页，定义独立输入上的 clean 二次型，
要求逐输入条件期望为零、最大归一化行方差消失、归一化四阶矩趋于三。
紧随定理的全一非对角矩阵例子说明：行方差小仍可留下一个大特征值及 chi-square 极限。
本章临界矩阵的算子范数至多 O(√δ log Q)，明确排除这个障碍。
该原文不处理实际观测行、固定基数后验、放大中心误差或临界 Ci 过程紧性。
Gaussian 二次型的联合特征函数是经典步骤，其所需模型估计在正文给出。

Peccati–Taqqu，*Stable convergence of multiple Wiener–Itô integrals*，
[arXiv:math/0604530v1](https://arxiv.org/abs/math/0604530v1)，
Definition IV 和 Theorem 7，PDF 第 7–8 页，给出稳定收敛定义及 Skorohod 积分判据。
该判据使用恒等分解所诱导的适应 integrand、消失的早期投影、
嵌套 sigma 域，以及范数平方趋于非负可测随机方差等条件。
适应空间在 §2.2 定义；不能由一个边缘 Gaussian 极限自动取得这些假设。
本章没有假设实际后验标签形成这种适应积分。
共同矩阵特征函数、有限秩删除及旧对数核逼近直接给出所需联合独立性。
mixing 表示与旧 sigma 域中有界测试的极限因子分解，
不表示给定全部旧噪声后的条件分布收敛。

Bai–Ginovyan–Taqqu，*Functional Limit Theorems for Toeplitz Quadratic Functionals
of Continuous Time Gaussian Stationary Processes*，
[arXiv:1501.05574v2](https://arxiv.org/abs/1501.05574v2)，
Theorems 2.1–2.2，PDF 第 2–3 页，研究一个平稳 Gaussian 输入的固定 Toeplitz 核，
过程参数扩大观测区间。
其基本条件有 f,g∈L1、fg∈L1∩L2 及所述方差极限；
函数结论还用协方差 r∈Lp、核 a∈Lq，1/p+1/q≥3/2。
Theorem 2.4，第 4 页，给出另一组正则变化及 Potter 条件下的非中心函数极限。
本章的参数改变每对上的频率核，且观测环境异质、标签来自固定基数后验，
所以这些结果是二次型函数极限的相关先例，不直接给出实际临界模型的结论。
指定 v2 的 arXiv 页戳是 2015-04-29，PDF 首页另印 2018-06-27；引用版本以 v2 为准。

前节 Nualart–Peccati 的固定混沌判据、Nourdin–Poly 的谱与累积量公式、
Döbler–Kasprzak–Peccati 的变化核紧性工作、Imai 的异质输入近似
及 Siripraparat–Neammanee 的方差局部近似，继续作为已知工具使用。
每个有限临界参数的微小时间增量由 min(|t-u|,1/k) 求和控制，
不是对非平方可和的余弦导数直接求和。
Fourier–Plancherel、Bernoulli 多项式的正弦平方级数和 Ci 的分部积分渐近式均为经典事实。
其组合在本章指定协方差族上给出非平稳性、相位依赖和精确共振的 z⁻³ 方差。
小网格 OU 极限的 mixing 则来自每个固定 Gaussian 级数坐标的系数趋零，
以及统一增量控制；不是将定理 57.2 的固定参数替换成另一个增长参数。

在已检查的原文中未找到完整实际后验模型、离散 Ci 协方差及上述共同实现结论的直接陈述。
这不排除未检查来源，也不认证全球原创性。
新增内容限于所给模型的综合推导及误差关系。
临界 Gaussian 过程族的大参数共振渐近不宣称实际数组在网格比例趋于无穷时也有同一极限；
任意数据自适应频率、增长时间区间、其它幅度及实际后验矩收敛均未包含。

## 超临界谱网格的微观桥（第 58 章）

`repo-derived`：第 58 章在原固定 Liouville 幅度、beta∈(1/2,1)、lambda=Q³ 的
两种实际实验中，推导谱网格 eta=exp(s)delta→∞ 的微观路径极限。
假设 s sqrt(delta)≤U/2，且确定性相位 omega eta mod 2pi 沿给定子列收敛。
结论在同一后验标签实现上保留旧截距、二次坐标及整个旧空间噪声。
新的连接是放大后的有限谱与精确中心控制、实际固定滞后联合极限，
以及对增长网格一致的滞后尾上确界估计。
它不从第 57 章固定网格弱极限代入增长参数。

Foster–Habermann，*Brownian bridge expansions for Lévy area approximations and
particular values of the Riemann zeta function*，
[arXiv:2102.10095v1](https://arxiv.org/abs/2102.10095v1)，
式 (1.2)，PDF 第 2 页；§2.1 与 Lemma 2.2，第 7–8 页，
给出标准 Brownian bridge 的 sine 本征函数 sqrt(2)sin(k pi t)
与本征值 1/(k²pi²)。余弦随机积分系数相互独立，方差为 1/2。
以 a=pi t 换元，正是第 58 章 sine 级数及桥协方差的经典归因。
该文 Theorem 1.1，第 3 页，研究已是 Gaussian 的桥展开之 sqrt(N) 放大尾，
所得是有限维极限；原文明确指出它们没有 C[0,1] 过程实现。
本章保留固定滞后并缩放谱相位，另证尾的路径范数界，不能直接使用那个尾极限。

Aletti–Ruffini，*Is the Brownian bridge a good noise model on the circle?*，
[arXiv:1210.8245v1](https://arxiv.org/abs/1210.8245v1)，
Definition 2.1、Theorem 2.2，第 3 页，及 Theorem 2.3，第 4 页，
针对中心平稳周期 Gaussian 过程，使用匹配的独立 sine、cosine 系数族。
其收敛陈述是逐时均方误差的一致性，不自动给出上确界范数中的收敛。
本章 sine-only 极限固定在 pi 整数倍处为零，协方差依赖时间和，属于非平稳的奇周期桥。
各反射区间由同一条桥生成；没有使用独立周期噪声假设。
本章的路径连续性与 L²(C) 收敛由第四矩和二分估计直接证明。

Formica–Ostrovsky–Sirota，*Modulus of continuity for superlacunar trigonometric
series and continuity of Gaussian stationary random processes*，
[arXiv:2110.01998v1](https://arxiv.org/abs/2110.01998v1)，
Definition 1.1、Proposition 2.1，PDF 第 2–3 页，以及 §3，第 4–5 页。
其确定性模连续界假设 Fourier 系数绝对可和，稀疏频率例子使用 lacunary/superlacunar 条件，
Gaussian 讨论限制于平稳周期模型。
本章具有全部整数谐波、1/k 系数及非平稳 sine-only 结构，不能直接套用这些条件。
平方可和本身也不替代路径论证；本章逐项控制 min(|theta-psi|,1/k)，再作概率求和。

Sykulski–Olhede–Lilly，*The de-biased Whittle likelihood for second-order
stationary stochastic processes*，
[arXiv:1605.06718v1](https://arxiv.org/abs/1605.06718v1)，
§2.2 式 (2.5)，PDF 第 6 页，是均匀采样下谱折叠的经典公式。
§2.1，第 5 页，给出 Fourier Gaussian 假设；Theorem 1，第 12 页，
在平稳性、谱有界且远离零、参数二次可微等条件下证明去偏 Whittle 估计的一致性。
这些条件与本章异质、条件后验组数组及谱相位二次型不同，
不能把该估计定理作为实际微观桥定理。
本章的 aliasing 指整个得分组间距的确定性相位折叠，不导入 Whittle 效率或一致性结论。

第 57 章所引 de Jong 的 clean quadratic form 条件及大特征值反例，
Nualart–Peccati 的固定阶混沌判据、Nourdin–Poly 的谱与累积量公式，
以及变化核 U-process 文献继续提供经典背景。
此处固定正滞后矩阵算子范数 O(sqrt(delta))，不同滞后没有共同无序对；
联合特征函数先证明包括移动二次坐标在内的 Gaussian 性，随后才得独立性。
与旧线性噪声的联合公式和旧 H 核的矩形逼近保留同一个随机截距。
Bernoulli 局部界、共同逆分布耦合、精确中心与全向量后验比较沿用已验证的适用条件。

在已检查的原文中未找到完整实际模型、放大误差与上述共同实现微观桥的直接陈述。
这是有限文献比较，不认证全球原创性。
Brownian bridge 的级数表示、Gaussian 谱极限、连续映射及二分方法均不作为新发现。
相位相差 pi 给出相同边缘过程律，所以本章的 2pi 相位收敛只宣告为充分条件。
未包含相位随机分布或必要性分类、独立的周期桥、数据自适应频率、增长参数区间、
其它幅度、实际后验矩收敛或去掉频率上界后的结论。

## 精确共振的反射 Brownian 律（第 59 章）

`repo-derived`：第 59 章在同一实际后验模型中处理 eta=2m→∞、
eta²delta→0 的全部精确共振范围，不加对数余量，也不要求 m 的奇偶子列。
窗口 s+theta/eta³ 与放大 eta^(3/2)exp(z/2) 使低滞后余弦项留下 Gaussian 偏移，
而 k 约为 eta² 的高滞后正弦项留下局部 Brownian 路径。
两侧路径由同一条 Brownian motion 奇反射得到；偏移、该路径与移动二次坐标相互独立，
并联合独立于整个旧空间 Gaussian 噪声。
新的连接包括实际放大误差、精确中心、增长滞后卷积与使用总质量的 Schur 估计。
旧弱极限中代入增长参数不能替代这些步骤。

Foster–Habermann，*Brownian bridge expansions for Lévy area approximations and
particular values of the Riemann zeta function*，
[arXiv:2102.10095v2](https://arxiv.org/abs/2102.10095v2)，
式 (1.1)–(1.2)，PDF 第 2 页，给出标准桥协方差 min(s,t)−st
及 sine Karhunen–Loève 展开。
本章用到的 Dirichlet Green 核级数与局部 Brownian 协方差归于这一经典结构。
该版本 Theorem 1.1，第 3 页，研究截断桥展开的 sqrt(N) 或 sqrt(2N) 放大余项；
它给出有限维 Gaussian 极限，并明确说明相应极限场没有连续路径实现。
这里移动的是趋近共振点的自变量，并保留低滞后偏移；
对实际数组的紧性须由精确 Ci 小增量另证，不能由那条余项定理推出。

Bai–Ginovyan–Taqqu，*Functional Limit Theorems for Toeplitz Quadratic Functionals
of Continuous time Gaussian Stationary Processes*，
[arXiv:1501.05574v2](https://arxiv.org/abs/1501.05574v2)，
Theorems 2.1–2.2，PDF 第 2–3 页。
其对象是在增长矩形 [0,Tt]² 上积分的固定 Toeplitz 核二次泛函，
输入是具有谱密度 f 的中心平稳 Gaussian 过程。
Theorem 2.1 要求 fg 同属 L¹、L²，且末端方差趋于指定常数；
Theorem 2.2 再以 r∈L^p、a∈L^q、1/p+1/q≥3/2 等条件给出 C[0,1] 收敛。
本章空间质量非平稳，时间参数改变全部格滞后系数，且同格方块被删去，
所以不直接满足该文的固定核增长观察区间结构。
该精确版本的 arXiv 标注为 2015-04-29，PDF 首页日期为 2018-06-27；二者分别保留。

de Jong 1987 Theorem 2.1，第 263–264 页，仍是独立 clean 二次型的经典背景：
最大行方差可忽略及标准化第四矩趋三是承重假设，不能由“配对很多”替代。
本章用方差加权算子的范数直接控制特征值，且先由混合特征函数证明联合 Gaussian 性。
Nourdin–Peccati–Reinert [arXiv:0904.1153v2](https://arxiv.org/abs/0904.1153v2)
Theorem 7.1，PDF 第 26 页，要求独立标准化输入的一致三阶绝对矩、
固定阶对称去对角核与小最大 influence；它是有限维替换工具，
不能单独处理本章移动对角坐标、非线性截距及全路径的共同实现。
共同逆分布耦合保留这些坐标在同一个标签向量上的关系。

Döbler–Kasprzak–Peccati [arXiv:2104.01858v3](https://arxiv.org/abs/2104.01858v3)
Theorem 1.4 与 Conditions 1.1–1.3，PDF 第 3 页，处理部分指标累积的退化 U-statistic，
要求方差时钟、加强的 Lindeberg 条件及末端第四矩条件。
本章参数改变的是振荡核，并有跨零点的负相关，不能只凭同属二次过程而套用。
Ci 的 min(d/eta,eta/k) 增量界对任意小的 d 成立，提供本章自己的紧性依据。
Nualart–Peccati 的固定阶混沌判据和谱特征函数均为经典工具；
有限柱面删除再作 L¹ 逼近，明确处理与整个旧噪声的 mixing。
Tudor [arXiv:2606.14812v1](https://arxiv.org/abs/2606.14812v1)
Theorem 1，PDF 第 7 页，所允许的固定旧变量不能直接代替这里随规模移动的二次坐标。
Siripraparat–Neammanee 的 Bernoulli 局部界继续只用于满足原假设的辅助独立和，
不宣称实际相邻观测行独立。

已检查的原始文献没有直接给出本章完整实际模型与共同实现的共振极限。
有限检索不认证全球原创性；桥级数、Schur 方法、Gaussian 谱公式、
Kolmogorov 紧性及有限柱面方法均不作为新发现。
本章未包含失谐、eta²delta 不趋零、增长区间、其它幅度、数据自适应频率或实际矩收敛。
精确有限截距的允许替换须满足 eta²delta^(−1/2) 倍截距误差趋零；
只有相同弱极限不满足这个速率要求。

## 临界共振中的旧场重现（第 60 章）

`repo-derived`：第 60 章在 eta=2m、eta²delta→zeta∈(0,infinity) 下，
把同一实际后验向量的放大谱残差分解为独立 Gaussian 偏移与 sinc 核的二阶混沌。
偶数 m 的混沌由旧 Fourier 场自身生成，奇数 m 由确定格点交替符号产生独立副本。
两个分支有相同边缘过程律，却有不同的旧端点平方协方差。
新内容是实际放大误差、符号调制的共同实现和移动对角坐标的联合控制，
不是将一般二次型定理改换符号。

Nourdin–Rosiński，*Asymptotic independence of multiple Wiener–Itô integrals
and the resulting limit laws*，
[arXiv:1112.5070v1](https://arxiv.org/abs/1112.5070v1)，
Theorem 3.1，PDF 第 7 页，针对已联合收敛的固定阶多重积分向量，
把极限矩独立、平方协方差趋零与交叉收缩趋零联系起来。
由矩独立推出分布独立还需各极限边缘由矩确定。
Corollary 3.2 与 Remark 3.3，第 8 页，分别给出从边缘收敛到联合收敛的条件，
以及不能随意删掉矩确定性要求的反例。
Theorem 4.5，第 17 页，要求阶数 p≥q、一侧为渐近标准 Gaussian，
另一侧极限矩确定及交叉协方差趋零，才得到独立联合极限。
这些是偏移与非 Gaussian sinc 混沌关系的经典工具，
不自动提供实际后验比较、放大中心误差或符号调制后的 Gram 极限。
本章以混合特征函数和共同矩形核逼近直接完成所需联合关系。

de Jong 1987 Definition 2.1 与 Theorem 2.1，第 263–264 页，
要求独立 clean 二次项、小最大行方差与标准化第四矩趋三。
紧随其后的大特征值反例说明小行方差不足。
本章 Gaussian 偏移的小算子范数与 sinc 部分的非零极限算子，正好区别这两种情形。
Nualart–Peccati [arXiv:math/0503598v1](https://arxiv.org/abs/math/0503598v1)
Theorem 1，PDF 第 3 页，给出固定混沌阶与归一化方差下的第四矩、收缩及 Gaussian 极限等价。
其假设在偏移和对角量成立，在固定正临界参数的非零时间 sinc 核不成立。

Nourdin–Poly [arXiv:1205.2684v3](https://arxiv.org/abs/1205.2684v3)，
Proposition 2.1 及累积量公式，PDF 第 4 页，给出对称平方可积核对应的
Hilbert–Schmidt 自伴算子谱表示。
第四累积量 48 sum(lambda_n^4) 和第二混沌第四矩上界均属于经典结构。
本章核在非零时间的对角邻域不为零，因此严格正的第四累积量有实际核依据。
旧对数核与新有界核使用同一有限矩形划分；异格扣除产生 Wick 常数，不能省略。

第 57、58 章所引顺序 U-process、异质独立输入 Gaussian 近似和桥展开文献，
各自的输入、收缩、参数化及紧性假设仍须保留。
这些文献没有使固定正临界参数下的非 Gaussian 部分变成 Gaussian。
Tudor [arXiv:2606.14812v1](https://arxiv.org/abs/2606.14812v1)
Theorem 1，PDF 第 7 页，对固定旧变量的结论不能代替本章同时移动的对角量和调制坐标；
本章直接核对两组坐标的全部 Gram 极限并使用混合特征函数。
此限定针对所引 Theorem 1，不将该论文其它联合定理一概描述成固定变量结果。

实际条件化继续使用 Siripraparat–Neammanee 的独立 Bernoulli 和局部界。
Arratia–Goldstein–Langholz [arXiv:math/0506300v1](https://arxiv.org/abs/math/0506300v1)
Condition 2.1 与 Theorem 2.1 的高阶展开要求总方差至少与 Bernoulli 项数成固定比例，
并处理有界偏离；这里 q=o(M)，不能据此引入更强的稀疏中心展开。
第 56 章密度比与加权中心界，以及第 59 章在有界 eta²delta 下仍成立的原始共振矩阵界，
足以处理本章的实际比较。

定理 60.4 只讨论已识别 sinc 混沌族在 zeta↓0 时的低参数边界；
sinc 的区间 Fourier 乘子、Plancherel、谱 Gaussian 极限与有限柱面方法均为经典工具。
它不把固定正 zeta 的实际弱极限直接代入移动 zeta。
第 59 章的实际反射 Brownian 律仍依赖其单独的数组估计。

已检查的原始文献未直接给出此固定 Liouville 模型、奇偶旧场关系及全部实际放大误差。
有限检索不认证全球原创性。没有声称两分支在有限后验中独立、
实际无界矩收敛、奇偶性随机分布、增长区间、其它幅度或不分奇偶的旧场联合极限。

## 超临界共振的端点平方（第 61 章）

`repo-derived`：第 61 章在精确 eta=2m、eta²delta→infinity、
s sqrt(delta)≤U/2 的完整范围内，证明实际谱残差的常 Gaussian 偏移与进一步锚定的端点平方律。
实际锚定量一致逼近同一标签向量的符号端点平方减实际对角平方和。
偶数 m 使用旧端点，奇数 m 使用独立副本；两者边缘律相同而旧场联合律不同。
新推导包括总放大 eta³ 后的有限 Fourier 误差、无附加对数间隔的加权导数界、
移动符号方向与对角量的共同独立性，以及实际后验的整向量转移。
未把第 60 章固定临界参数极限代入增长参数。

Nourdin–Peccati，*Noncentral convergence of multiple integrals*，
Annals of Probability 37 (2009), 1412–1426，
DOI [10.1214/08-AOP435](https://doi.org/10.1214/08-AOP435)，
[arXiv:0709.3903v3](https://arxiv.org/abs/0709.3903v3)，
Theorem 1.2，PDF 第 3 页，假设固定偶数混沌阶 n≥2、方差趋 2nu，
以矩或收缩条件刻画中心 Gamma 律 2Gamma(nu/2)-nu 的收敛。
其中矩条件是 E F_k^4 -12 E F_k^3 →12nu²-48nu。
Proposition 4.5，PDF 第 14 页，在二阶情况下再要求
每个固定旧方向 h 的收缩内积 <f_k contraction_1 f_k,h tensor h>→0，
才能得到与该方向独立的联合极限。
同页 Remark 4.3 以恒定秩一核明确反驳「二阶非中心收敛自动独立」的说法。
本章符号秩一核的这一内积正比于 (integral chi_Q h rho)²；
奇数支因交替符号消失，偶数支在 h=1 时不消失。
这个经典判据不含实际观测行、有限谱放大、后验中心或移动方向的联合比较。

Nourdin–Poly，*Convergence in law in the second Wiener/Wigner chaos*，
[arXiv:1205.2684v3](https://arxiv.org/abs/1205.2684v3)，
Proposition 2.1 与紧随的累积量公式，PDF 第 4 页，
给出 Hilbert–Schmidt 对称核对应的独立中心正态平方谱展开。
Theorem 3.1，PDF 第 5 页，刻画二阶 Wiener 积分弱极限的分布，
它可表示为独立 Gaussian 加二阶积分。
该分布存在性不识别极限与给定旧噪声的共同实现。
本章以有限秩投影删除直接证明偏移、对角量与移动符号方向的联合关系。
第四累积量和秩一中心平方结构属于经典工具，不列为新的一般混沌理论。

Peligrad–Wu，*Central limit theorem for Fourier transforms of stationary processes*，
Annals of Probability 38 (2010), 2009–2022，
DOI [10.1214/10-AOP530](https://doi.org/10.1214/10-AOP530)，
[arXiv:0910.3451v3](https://arxiv.org/abs/0910.3451v3)，
Theorem 2.1，PDF 第 3 页，要求中心、二阶可积、平稳遍历及远过去条件均值为零，
结论针对 Lebesgue 几乎处处的固定频率。
它不能直接覆盖本章精确零频或 Nyquist 交替频率，以及异质的移动格质量。
本章以周期交替函数的有界原函数证明精确频率下的 Gram 极限。

Bernoulli 局部界仍使用 Siripraparat–Neammanee 2021 Theorem 2；
第 56 章已将其用于整选择向量比较、Hilbert 中心界和核心逆分布耦合。
de Jong 的 clean 二次型 Gaussian 条件、Nualart–Peccati 的第四矩条件
适用于小算子偏移机制，不能把锚定秩一项判为 Gaussian。
Tudor 2606.14812v1 Theorem 1 对固定旧变量的结论不能代替本章移动符号方向；
这里的投影空间明确同时包含固定和移动方向。

已检查的原始文献未直接给出这个实际 Liouville 后验模型的完整超临界结论；
有限检索不认证全球原创性。Gaussian 谱展开、交替 Gram 极限、有限秩删除和连续映射均为成熟方法。
本文没有声称实际无界矩收敛、固定支持的条件后验定理、
不分奇偶的旧场联合极限、非精确共振、增长空间窗口或超出原频率上界的结论。

## 非共振载波与圆对称能量（第 62 章）

`repo-derived`：第 62 章证明原始实际 pair/path 后验在 eta²delta→zeta>0，
dist(omega eta,pi Z)/delta→infinity 下的锚定谱极限，允许相位任意缓慢地靠近共振。
一个有限实标签向量产生的调制场趋于独立于旧实场的圆对称复 Gaussian 测度；
新能量过程保留 Wick 扣除，并与移动对角量、旧非线性截距联合收敛。
新增的实际比较包括放大有限 Fourier 误差、有界锚定导数、
相位一致的伪协方差及旧场交叉 Gram 消失和单向量后验转移。

Campese，*Fourth Moment Theorems for complex Gaussian approximation*，
[arXiv:1511.00547v1](https://arxiv.org/abs/1511.00547v1)，
Definition 2.1 与 Remark 2.2，PDF 第 4–5 页，给出圆对称复 Gaussian 的密度、
Hermitian 协方差与零 relation/pseudo-covariance。
本章用其密度与特征函数中的 1/4 因子固定实虚部方差各为一半，
不以该版本文字中的 “standard” 一词另行指定实分量方差。
Theorem 4.6，第 16 页，在 Markov diffusion 的 chaotic complex vector 框架、
正定目标协方差及显式二阶和四阶误差下给出 Wasserstein 界。
这里场的 Gaussian 阶段由共同耦合与完整 Gram 极限直接处理，未假设那些定量误差。
固定 zeta 的能量仍有严格正第四累积量，不能借该定理改判为 Gaussian。

`literature-attested`：已识别族的单侧普通 Brownian 弱极限属于连续 Breuer–Major 定理的应用。
Campese–Nourdin–Nualart，*Continuous Breuer–Major theorem: tightness and non-stationarity*，
[arXiv:1807.09740v1](https://arxiv.org/abs/1807.09740v1)，
Theorem 1.1，PDF 第 2 页，要求中心平稳单位方差实 Gaussian 场、Hermite rank d、
相关函数的 d 次绝对幂可积，以及 f 属于某个 p>2 的 Gaussian Lp。
本章圆对称 Fourier 场的归一化实虚部为两个独立平稳实场，
相关为 exp(-omega²v²/(2kappa))，函数 H2=x²-1 满足所有这些条件。
二者相加给出正半轴的方差常数 16g0；此族结果不作为新的一般功能极限定理。
正文的共同 Hermitian 频带还核对两侧联合关系及对整个固定场的混合，
并明确这仍不同于实际数组同时移动 zeta 的结论。

Tilva，*Continuous Breuer–Major theorem for vector valued fields*，
[arXiv:1901.02317v1](https://arxiv.org/abs/1901.02317v1)，
C0/C1，PDF 第 3 页，要求联合平稳 Gaussian 向量场、同点协方差归一化及协方差衰减和可积。
Theorems 3.2–3.4，第 5–6 页，采用扩张对称立方体平均；
功能版本还有关于 G^(p/2) 的 rank 与相关函数分数幂可积的条件。
此处不借它直接识别有向两侧积分或与旧场的混合关系。

Mansanarez–Poly–Zheng，*Breuer–Major–Donsker invariance principle*，
[arXiv:2607.11469v1](https://arxiv.org/abs/2607.11469v1)，
Theorems 1.3–1.4，PDF 第 4–5 页，分别处理满足非确定性或存在非确定抽稀子列的情形。
Corollary 1.5 允许绝对可和相关；同页 Remark 1.6 指出仅平方可和不保证每种抽稀产生创新。
本章离散采样的 Gaussian 相关绝对可和，但从采样和到连续积分仍需单独比较。
正文直接使用连续场谱结构，没有把该近作描述为无条件解决全部平方可和情形。

Hermitian 中心 Gaussian 二次型的方差 sum(lambda²)、第四累积量 6sum(lambda⁴)
来自单位指数变量的经典谱展开；等价实混沌算子把每个特征值除以二并重复两次。
Nourdin–Poly 1205.2684v3 Proposition 2.1 及实混沌累积量公式是同一经典机制。
保留复核的虚部决定单侧频带；只取其实部会改变正负时间的联合律。
Nourdin–Rosiński 的矩独立与分布独立条件、de Jong 的大特征值障碍仍按前章范围使用。
Siripraparat–Neammanee 的异质 Bernoulli 局部界继续支持辅助耦合；
实际观测行与固定总量标签未被假设独立。

有限原始文献检索未发现直接给出本章完整实际后验与相位一致结论的定理，
这不认证全球原创性。圆对称性、Gaussian 谱论及单侧 Breuer–Major 结论均有上述归属。
定理 62.3 的必要性只针对本模型标量载波的圆对称极限，依赖 Gaussian 轮廓 Fourier 变换严格为正；
不声称非线性能量的充要分类、未锚定量紧性、实际无界矩收敛、增长区间或其它幅度。


Yang–Guan，*Fourier analysis of spatial point processes*，
[arXiv:2401.06403v1](https://arxiv.org/abs/2401.06403v1)，
Theorems 3.1–3.2，PDF 第 9–12 页，是最接近的移动频率先例。
其平稳简单空间点过程具有递增可比矩形窗口、相应阶数的可积累积量密度及非负连续紧支撑 taper；
联合 CLT 另需多项式强混合。频率到零以及两两和、差都在有效窗口尺度上分离，
允许其极限重合或等于零。Lemma C.2，第 49–50 页，以 Riemann–Lebesgue 消去振荡，
不要求对数余量。这里的两个别名谐波与其机制对应；
有界变差 Abel 估计本身不是新增的一般理论。
异质条件 score 组、固定总量标签、放大 Ci 比较和旧非线性截距的共同转移不在该定理假设内。
本章先按绝对质量处理环境误差，得到 delta/d_M+epsilon_env，避免人为的 epsilon_env/d_M 损失。

Panaretos–Tavakoli，*Fourier analysis of stationary time series in function space*，
[arXiv:1305.2073v1](https://arxiv.org/abs/1305.2073v1)，
Theorem 2.2 与 Remark 2.3，PDF 第 7–9 页，处理平稳实 L² 函数值序列，
要求各阶矩、累积量核可和及协方差算子的核范数可和。
精确零频率与 pi 频率产生实 Gaussian；不同正 Fourier 格频率产生独立复 Gaussian，
即使这些频率的极限重合或趋于端点。定理 62.3 证明内的矩形权重几何和是这一经典边界，
不是本实际 Gaussian 方差轮廓的反例，也不把本模型必要条件提升为普遍 Fourier 法则。

Björklund，*Completely Positive Entropy and Fourier Central Limit Theorems for Stationary Random Measures*，
[arXiv:2608.22342v1](https://arxiv.org/abs/2608.22342v1)，
Theorems A–B，PDF 第 3–5 页。
Theorem A 对局部二阶矩有限、平移作用本质自由且完全正熵的平稳随机测度，
给出几乎处处固定频率的 Fourier CLT；它不覆盖任意给定的三角移动频率。
Theorem B 的零熵平稳遍历反例具有有界连续、几乎处处正的 Bartlett 密度，
但沿扩张窗口 Fourier CLT 失败；良好二阶谱本身不是充分假设。
本章不假设实际条件数组满足这些熵条件，也不以几乎处处定理替代相位尺度证明。

## 多载波的共同别名关系（第 63 章）

`repo-derived`：第 63 章在同一实际 pair/path 后验标签向量上，联合识别有限多个临界载波的锚定谱过程。
相位差与相位和在 delta 尺度上的极限共同决定 Hermitian Gram 与伪 Gram；
这些极限来自同一组相位，必须满足加法与反射相容性。
零相位类保留旧实场，pi 相位类保留一份共同独立实场，其余每个带符号别名类使用一份共同 proper 复场。
类内成员通过有限调制或共轭相连，不得分别重抽。
对本模型 Gaussian 方差轮廓，任意两个非零时间极限能量独立当且仅当属于不同类；
严格正的 Fourier 变换使同类能量的 Wick 交叉协方差非零，其符号由时间方向决定。
这是共同实现与实际后验比较的结论，未断言有限后验的独立性或实际无界矩收敛。

Yang–Guan，*Fourier analysis of spatial point processes*，
[arXiv:2401.06403v1](https://arxiv.org/abs/2401.06403v1)，
Theorems 3.1–3.2，PDF 第 9–12 页；Lemma C.2，第 49–50 页。
其平稳简单点过程、可比扩张矩形窗口、累积量密度可积、连续紧支撑 taper 和多项式混合条件，
给出在有效窗口尺度上到零及两两和、差分离的移动 Fourier 频率的联合复 Gaussian 极限。
允许频率极限重合或到零，分离机制不要求对数余量。
这是两套交叉关系及移动频率消振的直接先例；
第 63 章还保留未分离时的共同调制/共轭，处理异质实际环境、固定总量标签及旧非线性截距。
不把 Abel 求和、调制和 Gaussian Gram 收敛称作新的一般定理。

Panaretos–Tavakoli，*Fourier analysis of stationary time series in function space*，
[arXiv:1305.2073v1](https://arxiv.org/abs/1305.2073v1)，
Theorem 2.2 与 Remark 2.3，PDF 第 7–9 页。
输入为平稳实 L² 函数值序列，要求各阶矩与可和累积量核及协方差算子核范数可和。
精确零与 pi 频率为实 Gaussian；不同正 Fourier 格频率为独立复 Gaussian，
即使极限频率重合或到端点。
本章实类与复类的区分属于这个经典谱背景；Gaussian 方差轮廓的连续调制 Gram
不同于矩形窗口在离散 Fourier 格上的精确正交，不能交换二者的必要条件。

Peligrad–Wu，*Central limit theorem for Fourier transforms of stationary processes*，
[arXiv:0910.3451v3](https://arxiv.org/abs/0910.3451v3)，
Theorem 2.1，PDF 第 1–4 页及第 4 页的频率对独立性说明，
要求平稳遍历平方可积输入及对远过去的正则性条件。
结论是几乎处处固定频率及几乎处处频率对的结论，
不能直接用于指定的例外频率或相互逼近的三角载波。

Chen–Chen–Liu，*An improved complex fourth moment theorem*，
[arXiv:2304.08088v1](https://arxiv.org/abs/2304.08088v1)，
PDF 第 7–8 页的 proper 复 Gaussian 定义及第 11–12 页 Theorem 3.8。
其向量第四矩定理要求前极限的联合圆对称性。
本章的实共振类及含共同共轭成员的向量一般不满足该前提，不能直接借用该定理。
正文在一个实 Gaussian 向量上计算完整实虚 Gram，并以联合特征函数/有限秩删除处理移动对角量。
复方差为 gamma 时实虚方差各为 gamma/2 的约定沿用这些经典定义。

Wick 配对式 Cov(|X|²,|Y|²)=|E X conjugate(Y)|²+|E XY|²、Gaussian 独立性判据、
有限秩投影和连续映射均为经典工具。
仅报告各载波的边缘分布不会保留同类之间的两项关系。
有限失谐单窗口还能由第 60 章作精确有限参数重定位后直接取得，因而不另建重复的边缘定理章节。
本章新增承重面是同一个实际实验的联合别名类、相容实现及极限能量独立性的精确判据。

Brillinger，*Asymptotic Normality of Finite Fourier Transforms of Stationary Generalized Processes*，
Journal of Multivariate Analysis 12 (1982), 64–71，
[作者原始 PDF](https://www.stat.berkeley.edu/~brill/Papers/generalizedprocess.pdf)，印刷第 66–68 页。
Assumptions I–II 要求实平稳广义过程的相应累积量谱局部界及在零点集中的归一化 taper；
定理另要求指定频率处二阶谱连续且非零。
这提供固定频率 Fourier 正态极限的经典背景，不给出本章 delta 尺度的相位合并与后验比较。
实输入和实 taper 在相反频率上的变换互为共轭，因此不能仅凭“频率不同”推断独立；
正文保留完整伪 Gram，不借未区分相反频率的独立性措辞跳过这一检查。

Ben Hariz–Bui–Esstafa，*Quantitative central limit theorem for an integrated periodogram via the fourth moment theorem*，
[arXiv:2604.00642v2](https://arxiv.org/abs/2604.00642v2)，Theorem 2.1，PDF 第 2 页，
对中心实平稳 Gaussian 序列与固定偶权重，要求谱密度及权重具有给定正则变差指数，
两指数各在 (-1,1)，和小于 1/2；定量 Wasserstein 速率另要求 (2.3) 的局部 Lipschitz 界。
其固定权重积分周期图在 sqrt(n) 尺度上为 Gaussian，
不替代这里保留非 Gaussian 二次能量的临界窗口联合律。

Ghosh–McElroy–Lahiri，*Polyspectral Mean Estimation of General Nonlinear Processes*，
[arXiv:2410.15187v2](https://arxiv.org/abs/2410.15187v2)，
Assumption A[k]，PDF 第 7 页；Theorem 1 与 Corollary 2，第 11–12 页。
在各阶加权累积量可和、所需矩存在、对称可积权重及指定 Riemann 逼近速率下，
给出固定权重多谱均值及有限多个同阶权重的 sqrt(T) Gaussian 极限。
所阅版本 Corollary 2 的另一分支仍有未解析的 “Theorem ??” 引用；这里仅比较明确的 Theorem 1 分支。
该固定权重均值结论不识别本章的合并载波、共同共轭与实际固定总量后验。

有限原始文献核对未命中完整实际后验联合陈述；这不认证全球原创性。
结论限于固定有限载波数、固定参数紧区间、原幅度与 beta、临界 eta_a²delta→zeta_a>0。
不声称载波数增长、随机或适应性相位、实际矩收敛、无限族统一结论或未锚定谱的紧性。

## 亚临界移动谱窗的共同白噪声（第 64 章）

`repo-derived`：第 64 章处理同一实际固定总量后验中的有限多个可比亚临界载波。
相位的和、差在 eta² 的倒数尺度上决定共同别名类，保留同一实现上的联合极限。
零与 pi 类分别产生奇延拓 Brownian 噪声；一般类产生两侧 Brownian 噪声，
共轭方向与有限偏移在同一份噪声上实现。整个新噪声族与旧 Gaussian 场和移动对角量联合独立。
这个独立性来自新二次型的趋零算子范数和共同有限秩删除，不能仅从与旧场零协方差推出。
正文对放大后的有限 Fourier/Ci 恒等式、精确中心、公共耦合、确定性单元质量替换、
任意小增量及一次完整后验向量比较逐项给界；没有把第 60 章固定参数定理代入移动参数。

Dahlhaus–Polonik，*Empirical spectral processes for locally stationary time series*，
[arXiv:0902.1448v1](https://arxiv.org/abs/0902.1448v1)，
Assumption 2.1，PDF 第 3 页；Theorem 2.5，第 6 页；Theorem 2.11，第 10 页；
Examples 3.3–3.4，第 13–14 页；Theorem 5.3 及其讨论，第 19–20 页。
其数据本身是局部平稳线性三角阵：iid 标准化创新、给定衰减率的系数、
极限时间系数的有界变差和统一求和逼近条件均须保留。
Theorem 2.5 对固定的双变量有界变差测试函数给出 Gaussian 极限；
协方差同时包含频率 lambda 与 -lambda 的配对，以及创新的四阶累积量项。
这为本章同时保留相位和与相位差提供直接的经典谱背景。
Theorem 2.11 还要求该版本的创新矩条件、测试类上一致变差界和平方熵积分。
Example 3.4 明确区分随样本量变化的局部估计测试函数，其分布结论不能直接从 Theorem 2.5 取得；
该处转用最大不等式给出速率。Theorem 5.3 的 taper 在该陈述中也不随样本量变化。
因此不能把论文误称为只研究固定数据，也不能把其固定测试函数结果直接用于本章放大的收缩窗口。

Fasen-Hartmann–Mayer，*Empirical spectral processes for stationary state space models*，
[arXiv:2202.12589v2](https://arxiv.org/abs/2202.12589v2)，
Assumption A 及离散表示，PDF 第 4–5 页；Assumption B 与 Theorem 3.2，第 7–9 页。
输入是固定采样间隔下的稳定连续时间状态空间模型，驱动 Lévy 过程具有有限四阶矩，
并保留所列输出规范化条件。离散表示为 iid 创新的平稳移动平均，系数指数衰减。
Assumption B 对测试函数类的全有界性之外，分支要求正则指数大于 1/2、
或零指数情形的累积量与熵条件、或固定函数乘区间指示函数的特定类。
Theorem 3.2 还要求相应 Phi,s 范数在类上一致有界。
这包含函数型积分谱过程及区间索引的经典机制；
本次核对没有建立放大并收缩的测试函数族满足这些一致界，
也没有把异质后验标签阵识别为该平稳状态空间输入。
本章用精确 Ci 增量与小算子谱展开单独证明所需桥梁，不借同名的函数型极限定理省略条件。

余弦级数的分段二次表达、Brownian 白噪声表示、Gaussian Gram 独立性判据、
第二混沌的谱展开及 Kolmogorov 紧性均是经典工具。
新联合表述中的可见区别是：属于同一噪声类不等于每一对指定读数都相关。
一般类的单增量由有向区间表示，实类由区间及其反射的正折叠表示；
两个单增量的函数在各自支持上符号恒定，故正测度交叠不能靠抵消变为独立。
只有带符号的多个读数对比才可能抵消。整个限制过程的独立性要求其生成的闭子空间正交。
这些是已识别共同极限中的关系，不是有限后验独立性的声明。

单载波的带符号失谐参数在整条有向时间轴上可由极限律识别，
但在固定双向观察区间内，所有位于该区间反射范围之外的参数具有同一个两侧 Brownian 律。
第 64 章给出精确局部距离判据、全局一点紧化判据及原合法算术内的交替参数实现。
不含零的观察区间还须保留零点锚定的共同关系；只检查区间不经过反射中心不足以判 Brownian 律。
这里的局部不可识别是限制观察映射合并了不同全局律，不把术语或单点方差相同当作过程等价。

先前关于 de Jong、Nourdin–Poly、Nourdin–Rosiński 与 Bernoulli 局部比较的条件继续按各原始版本使用。
Arratia–Goldstein–Langholz 的全标签方差正比于输入数前提仍不成立，未借用该更强展开。
有限原始文献核对未得到完整的实际后验移动别名联合定理；这只是已查范围的结论，
不认证全球原创性。Rosenblatt 的窄带来源及部分积分周期图来源的全文取得失败，
未用这些未检正文判断直接包含关系。

范围限于固定有限载波数、正且有限的尺度比率、确定性相位、固定时间紧区间、
原幅度与 beta 及完整后验向量。条件 BL 收敛在先验数据概率中成立，
固定支持结论为一致无条件收敛，未知方向使用共同事件。
不声称载波数增长、适应性相位、实际无界矩收敛、有限后验独立，
也不由锚定过程的结论推断未锚定谱的紧性。

## 未锚定谱的统一失谐紧性（第 65 章）

`repo-derived`：第 65 章在原 pair/path 实验、完整固定总量后验及精确有限截距下，
证明未锚定谱紧性等价于 eta²d²/(delta+|d|) 有界。
该单一判据不要求尺度比或相位收敛；分别沿亚临界、临界、超临界子列，
它产生平移的奇延拓 Brownian 过程、平移的实 Gaussian Fourier 能量，以及含端点平方的常数路径。
超临界常数与更细的锚定增量共享同一个端点平方。
这些关系来自同一实际向量的联合比较，不由三条边缘极限定理拼接。

必要性使用离散正弦方差的统一两侧界、归一化 Gaussian 二次型的四阶矩界和 Paley–Zygmund 不等式，
得到实际后验的固定正逃逸概率。方差发散本身不足以证明实际不紧。
归一化先于精确中心和核心比较，消除了任意大 eta 带来的原始矩阵范数障碍；
有限 Fourier 误差和缩放增量误差分别在自己的最终尺度上估计。
正文保留随机环境方差，不把旧的未量化误差再次放大，也不要求额外对数余量。

de Jong，*A Central Limit Theorem for Generalized Quadratic Forms*，
[DOI:10.1007/BF00354037](https://doi.org/10.1007/BF00354037)，
Definition 2.1，印刷第 263 页；Theorem 2.1 及其后例子，第 264 页。
该定理要求独立输入、逐变量条件均值为零的 clean 二次型、可忽略的归一化行方差和趋于三的归一化四阶矩。
其全一非对角矩阵例子具有可忽略行影响，却收敛到中心平方量。
本章超临界核的秩一极限正是这类障碍：小行影响不能把保留的端点平方改判为 Gaussian。
实际观测行及固定总量标签不满足该独立输入假设，正文另证后验和耦合桥梁。

Nualart–Peccati，*Central limit theorems for sequences of multiple stochastic integrals*，
[arXiv:math/0503598v1](https://arxiv.org/abs/math/0503598v1)，Theorem 1，PDF 第 3 页；
Nourdin–Poly 的第二混沌谱表示及累积量公式继续按前述版本使用。
固定阶混沌、趋于单位的方差以及相应四阶矩或收缩条件是经典 Gaussian 极限机制。
正文仅对小算子块应用这一机制；临界核和超临界秩一核保留非 Gaussian 性。
联合二次型—线性型特征函数负责移动符号方向与移动对角量，
随后共同矩形逼近保留旧非线性截距，不能仅靠不同混沌阶的正交性宣称独立。

Bai–Ginovyan–Taqqu，*Functional Limit Theorems for Toeplitz Quadratic Functionals of Continuous time Gaussian Stationary Processes*，
[arXiv:1501.05574v2](https://arxiv.org/abs/1501.05574v2)，Theorems 2.1、2.2、2.4，PDF 第 2–4 页。
其输入为平稳 Gaussian 过程，具有固定差分核，积分域为增长的时间前缀。
中心有限维定理要求 fg 的可积与平方可积性及所列方差极限；
函数型结论另要求协方差和生成核的 Lp/Lq 条件。
非中心定理要求指定的零频正则变差指数、指数和大于 1/2、可积性及全局 Potter 界。
这些是中心与非中心二次过程的原始先例；改变谱相位的异质后验三角阵尚须核对另一组实际桥梁，
不能直接替换其增长时间前缀参数。

Choudhary–Kuchibhotla，*On the Lévy concentration function of Gaussian quadratic forms with applications to second order U-statistics*，
[arXiv:2606.25441v1](https://arxiv.org/abs/2606.25441v1)，Section 3，PDF 第 7 页；Theorems 1–2，第 8–9 页。
其对象是独立标准正态上的 sum lambda_k(Z_k²−1)+mu_k Z_k，系数平方可和，
允许有符号特征值，所列浓集界区分由少量特征值主导的情形。
这是 Gaussian 与中心平方量之间统一反浓集估计的近期背景。
本章只需要固定正概率逃逸，直接证明的四阶矩与 Paley–Zygmund 界已足够；
未借用该文更强小球估计，也未从该辅助 Gaussian 结果跳过实际后验比较。
所阅版本第 9 页例 S1 将纯 Gaussian 浓集函数写成精确线性式；
对标准差 sigma 的非退化 Gaussian，精确式为 2Phi(epsilon/(2sigma))−1，
该线性式只给出上界及小 epsilon 的首项。本文不采用这个示例等号。

Dette–Kühnert，*Self-normalization for Spectral Density Integrals*，
[arXiv:2608.30018v1](https://arxiv.org/abs/2608.30018v1)，
model (2.1)，PDF 第 2 页；Theorem 2.1、Remark 2.1，第 3 页；Proposition 2.1，第 4 页。
其模型为系数满足所列加权可和条件的平稳 Gaussian 线性过程，正则指数在 (1/2,1]，
序贯样本比例在 [1/2,1]。线性谱权重定理要求偶对称、Hölder 指数大于 1/2 且几乎处处非零。
平方谱密度积分的极限还保留一份具有不同协方差时钟的 Brownian 分量，
其序贯中心本身也需修正。该结果说明谱量的边缘替换可能遗漏联合贡献；
它没有给出本章的失谐紧性充要条件，固定谱权重和样本前缀也不是这里的移动共振参数。

Ben Hariz–Bui–Esstafa 的 2604.00642v2 固定偶权重积分周期图定理，
以及前述 Nourdin–Rosiński、Tudor、函数型 U 过程和 Bernoulli 局部比较来源，
继续保留其确切输入、矩、收缩、确定性和路径条件。
Arratia–Goldstein–Langholz 的全人口方差与人数同比例前提仍不适用于 q=o(M)。
本章只使用按总方差给出的局部界和完整向量条件化比较。

Klöppelberg–Mikosch 的 DOI 10.1214/aoap/1034968236 原文端点返回 HTML；
Terrin–Taqqu 的 DOI 10.1007/BF01061262 仅取得摘要及访问页。
这两处未取得全文的来源不承担精确定理条件或不包含关系的判断。
有限原始文献核对支持上述工具归属，未检得完整的本模型后验紧性与同一噪声分类陈述；
该未命中不认证全球原创性。

结论限于原幅度和 beta、确定性频率、原外层频率范围及固定紧时间区间。
先验条件紧性在数据概率中成立，固定支持结论为一致无条件紧性；
二者不等于每个固定支持下的条件后验声明。
不声称实际无界矩收敛、几乎处处后验紧性、有限标签独立或无范围限制的超临界结论。

## 多尺度的共同静态对与 Gaussian／混沌联合律（第 66 章）

`repo-derived`：第 66 章把亚临界、临界和超临界的有限载波族置于同一个实际后验实现上。
低余弦静态部分只产生两维 Gaussian 噪声，两个奇偶类的相关系数为 −7/8；
同奇偶载波在任何尺度都共用同一个静态分量。
亚临界动态部分按相对尺度和奇偶分块，临界能量及超临界平方则共用两份实 Gaussian 场。
不同尺度的动态部分独立不意味着其未锚定过程独立。
静态对的和、差分别对应偶滞后和奇滞后，独立极限的方差比为 1:15；
有限线性组合消去静态部分，当且仅当两个奇偶类内的权重和分别为零。

实际推导统一控制全部有限 Fourier 放大、精确中心、核心耦合和确定质量替换。
不同亚临界尺度的交叉系数和受 q(1+|log q|) 控制，其中 q 是较小载波与较大载波之比，
所以尺度分离无需对数余量。联合小算子 Gaussian 极限先于独立性结论；
删去共同的移动有限维方向后，再逼近临界积分及旧对数截距。
这个共同实现步骤不能由单载波边缘定理或普通零协方差代替。
文中另给出相对尺度交替的合法序列：各边缘极限不变，两个联合子列律不同。

Nourdin–Rosiński，*Asymptotic independence of multiple Wiener–Itô integrals and the resulting limit laws*，
Annals of Probability 42(2)，2014，497–526，
[DOI:10.1214/12-AOP826](https://doi.org/10.1214/12-AOP826)，
本章另核对 [arXiv:1112.5070v4](https://arxiv.org/abs/1112.5070v4)。
Theorem 3.4，PDF 第 11–12 页，在固定有限个固定阶多重积分、逐坐标一致二阶矩界及指定分块下，
把块间渐近矩独立、平方的交叉协方差消失、各阶交叉收缩消失联系起来。
Corollary 3.6，第 15–16 页，再要求各块边缘收敛及各极限坐标的矩确定性，得到独立块的联合分布极限。
这是本章参考 Gaussian 阵的抽象独立性步骤的直接经典覆盖。
小算子与有界 Hilbert–Schmidt 算子的乘积收缩消失，
完全收缩则仍须由交叉协方差及共同有限秩逼近核验。
固定二阶混沌极限在零附近有有限矩母函数，满足这里所需的矩确定性。
该定理不提供实际后验的算术隔离、精确中心及放大误差预算。

Nourdin–Nualart–Peccati，*Strong asymptotic independence on Wiener chaos*，
[arXiv:1401.2247v1](https://arxiv.org/abs/1401.2247v1)，
Theorems 1.3–1.4，PDF 第 4 页；Propositions 1.5–1.6，第 5 页。
其固定有限向量由固定阶、单位方差的多重积分构成；交叉收缩或平方协方差消失给出有界光滑乘积测试的分解，
再由边缘收敛取得联合独立极限，不另要求极限矩确定性。
块版本要求块内固定阶。非零方差坐标可归一化，零方差方向另按 L² 消失处理。
本章两个静态分量的完全收缩不为零，同奇偶临界能量也不能由该定理误判为独立。
所取得版本的 arXiv 页眉日期为 2014-01-10，内部首页日期为 2021-01-18；
引用限于该确切文件的陈述，不据此推断修订历史。

Tudor，*Multidimensional Stein method and quantitative asymptotic independence*，
[arXiv:2302.09946v3](https://arxiv.org/abs/2302.09946v3)，
Theorem 3，PDF 第 13 页；Proposition 4，第 24–25 页。
主定理的伴随向量要求 L² 收敛、一致混沌尾界及交叉均值消失。
Proposition 4 在伴随向量属于不高于主 Gaussian 极限分量阶数的有限混沌和时，允许仅有弱收敛。
取主阶数为二，已核实共同弱极限与交叉协方差的旧线性、临界二次及移动符号坐标可直接使用此结论。
这确实覆盖本章参考阵的一部分移动向量独立性，不能描述成文献完全没有这类工具。
正文保留共同投影证明以交代场的共同实现及函数型近似；
该来源不替代实际观测到辅助 Gaussian 阵的比较。
第 25 页高阶反例也说明不能删除阶数限制而仍从边缘弱收敛推独立。

Bai–Taqqu，*Multivariate limit theorems in the context of long-range dependence*，
[arXiv:1211.0576v2](https://arxiv.org/abs/1211.0576v2)，
Theorem 3.6，PDF 第 7 页；Theorem 3.11，第 8 页。
输入为单位方差平稳 Gaussian 序列，协方差具有指定的正则变差形式；
固定变换的 Hermite 秩与记忆指数须满足分离不等式，长记忆部分的秩限制为一或二。
所列标准化部分和产生 Gaussian 与 Hermite 过程块的独立联合有限维极限。
函数型结论另要求短记忆变换的 Hermite 系数满足 (21) 的加强可和条件。
这是混合 Gaussian／非 Gaussian 过程结构的经典先例，
但固定变换部分和不是本章异质后验单元上的移动谱核。
所阅文件 arXiv 页眉为 2013-04-11，内部首页为 2018-09-04；
其任意秩混合情形猜想未被作为定理使用。

原 Bernoulli 局部定理、de Jong 的第四矩条件、Nourdin–Poly 的第二混沌谱结构，
以及 Dahlhaus–Polonik、Fasen-Hartmann–Mayer、Peligrad–Wu 的平稳性、输入、频率和测试类限制继续保留。
Fourier 尖点恒等式、交替 zeta 和、有限秩删除与 Gaussian 谱分解均是经典工具。
有限原始文献核对已找到上述抽象步骤的直接覆盖，未取得一个同时提供本模型实际后验、多尺度共同静态对及完整放大比较的定理；
未命中不认证全球原创性。早先 Rosenblatt、Brillinger 的访问限制及仅元数据候选不承担精确条件判断。

结论仅针对原固定参数、有限载波族、给定奇偶及相对尺度子列、固定紧区间和所列有界失谐。
后验结论在先验数据概率中成立，固定支持结论为无条件；
不声称有限后验独立、实际无界矩收敛、增长载波族或振荡相对尺度下的全序列联合收敛。

## 任意相位的超临界能量分类（第 67 章）

`repo-derived`：在原固定幅度、完整固定总量后验和两种实际平稳实验下，
第 67 章先从有限 Ci 导数证明任意相位的精细锚定量一致接近同一标签向量的载波能量。
导数核的有界性使精确中心误差不承受静态核的放大；
相位误差在辅助均方中由 eta^(-2)+r_M^(-2) 控制，再以有界事件转移。
由此得到模型特定的完整序列分类：边缘能量只需缩放绝对失谐收敛，
与旧场联合时，有限失谐还要求载波奇偶性最终固定。
带符号失谐的翻转不改变实场 Fourier 能量，但奇偶性改变它与旧端点平方的关系。
有限个临界和超临界窗口仍由同一实际相位和、差的两类 Gram 联合决定；
强度相差指数级也不保证能量独立。

`literature-attested`：复 Gaussian 标量的能量是两个独立实平方的加权和，
圆对称时退化为指数分布，实端点时退化为一个平方。
这属于经典 Gaussian 二次型谱分解，不是新的一般概率定理。
Campese 1511.00547v1 的 Definition 2.1、Remark 2.2 及特征函数固定圆对称归一化；
本章有限失谐的两个特征值由 covariance 与 pseudo-covariance 同时计算。
其 Theorem 4.6 的正定目标和 chaotic-vector 矩误差条件不能用来宣称能量 Gaussian，
也没有被用于零失谐的退化端点。
de Jong 的小行影响加第四矩条件及秩一反例、Nualart–Peccati 的固定混沌阶条件、
Nourdin–Rosiński 的跨收缩与矩确定性边界，均保留前章的归属与适用范围。

Ould Haye–Philippe，*From nonstationarity to stationarity via 1/f noise:
discrete Fourier transforms and sample mean asymptotics for testing*，
[arXiv:2605.28339v1](https://arxiv.org/abs/2605.28339v1)。
Section 2，PDF 第 3–4 页，研究独立同分布、中心且四阶矩有限的创新驱动的线性过程，
滤波系数具有所列幂律；平稳记忆参数属于 [-1/2,1/2)，积分情形另由平稳差分定义。
Theorem 2.1，第 6 页，给出有限个首 Fourier 格频率 2pi j/n 的实虚部联合 Gaussian 极限；
第 4–5 页的协方差矩阵不要求实虚块相同，相关加权卡方律已有明确先例。
其中记忆参数 d 不是本章确定性失谐，线性滤波与独立创新假设也不是实际固定总量 score 数组的假设。
这篇论文为低频非圆对称能量提供先例，没有直接给出本章精细锚定的实际误差比较、
与旧非线性截距的共同实现或完整序列的两种不同充要条件。

Rademacher–Kreiss–Paparoditis，*Frequency Domain Bootstrap for Functional Time Series*，
[arXiv:2608.25765v1](https://arxiv.org/abs/2608.25765v1)。
Section 2，第 4–7 页，同时保留复 Gaussian 极限的 covariance 与 relation 算子。
Assumptions 1–4，第 13–14 页，要求中心严格平稳、八阶矩、核范数意义的自协方差可和、
加权四阶累积量可和、指定八阶张量累积量可和、有界变差谱权重，
以及核范数一致的谱估计、非退化性和 b³/n→0 的子采样宽度条件。
Lemma 4.1 在这些条件下处理 bootstrap Gaussian 量的协方差与 relation。
Theorem 4.5，第 18 页，另加 Assumption 5 的特征间隙控制与投影维数增长条件；
其分布一致性结论还保留此前明列的原谱均值 CLT 前提。
第 7 页说明跨频率的小协方差可在积分统计中累积，不能在最终尺度之前仅因逐项小就删除。
这些是平稳函数值数据与谱均值 bootstrap 的结果，不是固定总量后验的微观锚定极限定理；
本章没有调用其 bootstrap 一致性或把 covariance 当作完整的复 Gaussian 描述。

Yang–Guan 2401.06403v1 Theorems 3.1–3.2、Lemma C.2 的有效窗口频率和、差分离，
Panaretos–Tavakoli 1305.2073v1 Theorem 2.2 的精确端点与 Fourier 格频率区分，
是本章载波分类的成熟先例，适用假设按第 62、63 章条目。
矩形格频率可有精确正交，因此本章使用 Gaussian 方差轮廓严格正 Fourier 变换的充要性，
不能推广为任意窗口的普遍失谐定律。
Peligrad–Wu 的几乎处处固定频率 CLT 不替代规定三角频率的两类 Gram 检验。
Björklund 2608.22342v1 Theorems A–B 的完全正熵假设和正谱反例仍说明二阶谱本身不足。

Siripraparat–Neammanee 的 Bernoulli 局部界和 Arratia–Goldstein–Langholz 的条件采样框架，
继续提供辅助局部比较的先例；高阶 rejective 展开并未越过其方差与增长条件直接套用。
实际观测行保持原有依赖，后验总量约束由一次完整选择向量比较处理。
Gaussian Gram、Wick 公式、有限秩投影及连续映射都是已知工具，
新增内容在于其共同实际实现、最终放大尺度下的误差控制及模型特定分类。

此次有限检索与原文条件核对未找到直接包含完整实际结论的定理，
不构成全球原创性认证。Klöppelberg–Mikosch 的原文下载仍只得到 HTML，
Terrin–Taqqu 的相关原文仍只有摘要与访问材料；未据元数据断言其精确定理不能包含某个子结论。
本章不声称实际无界矩收敛、未锚定过程紧性、增长载波数或区间、适应性频率，
也不把有限联合场的充分相位条件说成任意非线性能量元组的必要条件。

### 第 68 章：精确后验中心的算术分离与单标量恢复

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)第 68 章证明：
原始数据加同一潜在标签实现的一个精确总组能量，或等价的精确对角坐标 T_M，
在高概率数据事件上同时决定全部可行的组计数和组电荷。
本模型固定振幅的超越性、完整固定大小后验的有理函数中心，以及实际低计数储备共同承担结论。
储备使各所选组的后验中心在形式端点具有不同正整数消失阶，排除所有有理仿射关系。
不要求独立的一般位置中心、不需要偶部测量，也不恢复组内并列站点身份。

A. Baker、G. Wüstholz，*Logarithmic forms and group varieties*，
Journal für die reine und angewandte Mathematik 442 (1993), 19–62，
[DOI 10.1515/crll.1993.442.19](https://doi.org/10.1515/crll.1993.442.19)，
[Göttingen 原始扫描](https://gdz.sub.uni-goettingen.de/download/pdf/PPN243919689_0442/LOG_0005.pdf)。
原文第 19 页定义代数高度与对数支，第 20 页无编号主定理及其紧后系数高度界为实际调用处。
它要求固定非零、非一代数数、固定复对数支，以及非零整数线性对数形式；
给出的下界为固定代数高度和域次数常数乘系数高度，后者至多 log B。
本章反证中取代数候选 1+r、1-r 的实自然对数，系数 Q、P，
正十进制尾保证线性形式严格为正；不需要另加乘法独立假设。
超 Liouville 尾给 exp(-c Q^5) 级上界，与该固定常数的多项式下界矛盾。
这是该成熟定理在本库固定振幅上的应用，不把对数形式下界或一般超越性方法据为新内容。
Baker 1966 与 Matveev 2000 原始定理未在此次取得；未借它们的元数据补充证明。

Tamir Bendory、Dan Edidin、Ivan Gonzalez，*Finite Alphabet Phase Retrieval*，
[arXiv:2301.10647v2](https://arxiv.org/abs/2301.10647v2)。
版本戳 2023-04-07，正文内部日期 2023-04-10，两者区分。
Remark 3.2，第 5 页，说明一般位置排除非零多项式零集。
Proposition 4.2，第 5–6 页，以一般位置的共同有限字母表和周期自相关，
将相同自相关刻画为字母分区的 homometry；Theorem 4.3 允许其中一个字母固定为零，
其余字母仍须一般位置。其多项式系数比较是本章离散代数消歧的经典邻近机制。
本章的各组平移中心却都来自同一固定 r 的数据依赖有理函数，不能视为独立的一般位置字母。
原文不提供实际后验中心的不同端点消失阶，或依赖观测行的低计数储备事件。
本章使用无周期混叠的功率多项式，其零滞后总能量已足够；不替换为原文的周期问题。

Ziyang Yuan、Hongxia Wang，*Phase retrieval with background information*，
[arXiv:1802.01256v1](https://arxiv.org/abs/1802.01256v1)，2018-02-05。
第 2 节在实向量 z=(x;y) 中给定连续背景块 y，并观测整个向量的 Fourier 模长。
第 3 页显示的 Theorem 1 要求解集非空、m≥2(n+k)-2、k≥n、y_k≠0；
该版本周围散文称它 Theorem 2.1，保留此编号差异。
第 5 页 Theorem 3 改用独立 Gaussian 背景及关于 n、k、p 的指定长度条件，给出几乎必然唯一性。
本章不提供偶部或追加背景块；精确偏移来自完整后验，故这些侧信息定理不直接适用。
本章未调用原文算法、数值表现或任何抗噪保证。

Simon Ruetz、Karin Schnass，*Bounds for matrices of inclusion probabilities in rejective sampling*，
[arXiv:2212.09391v2](https://arxiv.org/abs/2212.09391v2)，2026-08-20。
第 1 节及 1.1 节把 rejective law 定义为独立 Bernoulli 开关条件于精确总数，
并给出相应支持概率和包含概率。共同 odds 倾斜在固定大小条件下消去，
所以正权重的支持乘积律及初等对称多项式归一化属于经典有限代数。
第 1 页 Featured Theorem A 的包含概率矩阵半正定界与 Hadamard 算子界是非渐近结果；
本章未调用它们。标签的固定总数依赖与原始平稳路径行之间的依赖不同，
本章低计数储备由实际一行生成函数与计数 Markov 界控制，不能从 rejective 标签定理取得。

Bing Gao、Qiyu Sun、Yang Wang、Zhiqiang Xu，*Phase Retrieval From the Magnitudes of Affine Linear Measurements*，
[arXiv:1608.06117v1](https://arxiv.org/abs/1608.06117v1)，2016-08-22。
原文第 4–5 页 Theorem 2.1 在整个实向量空间上刻画仿射模长测量的单射性，
等价条件含差平方的双线性分离及处处满秩 Jacobian。
Theorem 2.2 给出 m≤2d-1 时不能恢复全部实向量，Theorem 2.3 给出 m≥2d 的一般位置充分性。
本章的可行域是精确中心平移的整数格，单个总平方范数也不同于逐项仿射模长读数；
不能把连续域样本数下界套到这个离散域，也不能用一般位置设计替代固定后验中心的证明。
差平方消去中心平方项是经典工具，新增义务在于证明这个实际中心族的有理仿射独立性。

Pulak Sarangi、Ryoma Hattori、Takaki Komiyama、Piya Pal，*Super-resolution with Binary Priors: Theory and Algorithms*，
[arXiv:2301.01724v2](https://arxiv.org/abs/2301.01724v2)，2023-03-03。
这篇原文研究二元先验下的线性超分辨，不是相位恢复。
第 3–4 页式 (8)–(10)、Theorem 1 及第 13 页 Appendix A 用已知幅值二元输入、
初始静止 AR(1) 滤波器和整数均匀降采样，把每个长度 D 的块化为一个精确加权标量。
不同二元块之差给出系数在 {-1,0,1} 的非零多项式，固定 D 的坏参数集合有限，所有 D 的并可数。
所以一个精确实数区分整个离散向量是已有的代数编码机制，不是新的一般信息论结论。
本章固定频率压缩也使用经典有限候选解析分离；其承重实际结论是固定振幅下的后验中心函数不发生恒等碰撞，
以及依赖路径观测满足所需储备的概率界。原文线性 AR 权重、自由一般位置参数和算法结果不提供这两步。
本章不调用其噪声或算法保证。

David Pollard，*Some thoughts on Le Cam's statistical decision theory*，
[arXiv:1107.3811v1](https://arxiv.org/abs/1107.3811v1)，正文内部日期 2000 年 5 月。
第 1–2 节 Lemma <1> 用有限被支配实验的密度向量弱收敛构造随机化比较；
它比若干后验统计量的弱收敛强，不能用后者替代以转移任意解码器。
原文 TV 采用 L1 归一化，本章采用事件上确界；未使用该版本第 2 页一处对称距离的 minimum 字样。
本章实际反射联合律距离趋一由成功图像与原偶极反集中直接证明，
与既有 T_M 的 Gaussian 极限独立于旧场的结论并存，不声称完整实验等价。
第 68.5 条进一步给出完整组计数条件离散熵的 Q^5 主阶及正积分系数；
精确单标量在好数据上有相同原子概率表，因此具有同一熵率。
承重步骤是实际一、二行系数比较在整条宏观计数线上的统一对数占据数估计，
以及共同计数字母表的对数大小为 O(Q^5)，使一次完整后验 TV 比较足以传递归一化熵。
零计数端点、稀有空组和阈值区域均包含在证明中；没有从 Gaussian 微分熵或固定维数 CLT 推断该速率。

José A. Adell、Alberto Lekuona、Yaming Yu，*Sharp Bounds on the Entropy of the Poisson Law and Related Quantities*，
[arXiv:1001.2897v1](https://arxiv.org/abs/1001.2897v1)，2010-01-17。
原文第 3 页 Theorem 4、第 4 页 Corollary 1 及式 (7)，第 6 页相应证明，使用自然对数。
对 n,m≥1、p∈(0,1)，其显式二项熵上下界在 p 的任意内部紧区间上统一给出
H(Bin(n,p))=(1/2)log(2pi np(1-p))+1/2+O(1/n)。
这直接涵盖本章所需较弱的统一 (1/2)log(1+n)+O(1) 界；n=0 单独处理。
本章亦给出最大原子与离散 Gaussian 比较律的短证明，未把此经典半对数增长据为新结论。
该文不提供实际相依观测的占据数、宏观率函数或后验计数向量的熵。

Koenraad M. R. Audenaert，*A Sharp Fannes-type Inequality for the von Neumann Entropy*，
[arXiv:quant-ph/0610146v1](https://arxiv.org/abs/quant-ph/0610146v1)，版本戳 2006-10-18，
取得的排印正文内部日期为 2018-11-06，两者区分。
第 2 页 Theorem 1 及第 3 页经典概率向量归约、式 (11)，给同一 d 点字母表上
|H(P)-H(Q)|≤T log2(d-1)+h2(T)，T 为半 l1 距离。
它直接涵盖每份原数据纤维上的熵连续性；允许维数增长还需要本章独立给出的 log d 界。
本章用最大耦合和链式法则重述这一经典特例，没有把 TV 自动传递无界熵当作前提。

Chen、Ma、Nikoufar、Fei，*Sharp Continuity Bounds for Entropy and Conditional Entropy*，
[arXiv:1701.02398v1](https://arxiv.org/abs/1701.02398v1)，2017-01-10。
其式 (4) 在引用上述界时把二元熵项写成减号；该版本原始 TeX 源也确认此符号。
取两点概率向量 (1,0)、(1-T,T)，0<T<1，熵差为正 h2(T)，该右侧却为负 h2(T)，
故不能按展示式使用。本章使用 Audenaert 的正确加号及直接耦合证明，不调用此误写，
也不把该版本的单一展示式缺陷外推为其余结论或后续版本的结论。

Hervé Cardot、Camelia Goga、Pauline Lardin，
*Variance estimation and asymptotic confidence bands for the mean estimator of sampled functional data with high entropy unequal probability sampling designs*，
[arXiv:1209.6503v3](https://arxiv.org/abs/1209.6503v3)，版本戳 2013-06-28，正文内部日期 2018-10-30。
第 3.1 节的 n/N→pi∈(0,1)、一二阶包含概率共同正下界、函数轨道矩与正则性、四单位条件
属于其抽样设计方差及置信带设置。Proposition 3.1 比较同一包含概率的设计与 rejective 设计，
以 d(pi)^(-1) 与 KL 距离平方根控制四单位差异。
本模型 q/M 指数趋零，且所求为所选组计数这一压缩向量的熵；其高熵设计背景不提供本章熵率。

Haoran Wang，*Sharp High-Entropy Bounds for Sums of Independent Discrete Random Variables*，
[arXiv:2609.21459v1](https://arxiv.org/abs/2609.21459v1)，2026-09-18。
第 2 页 Theorem 1.1 对无挠阿贝尔群上两个独立离散变量、有限熵及最大熵 M>1，
给和的熵相对两输入平均熵的定量半比特增益；素数域版本另需奇素数及熵缺额 K≥9。
第 3 页 Corollary 1.2 与二项分布例子保留这些范围。
本章在给定数据后相加的是各独立二项坐标的熵，不是把坐标相加后取一个熵，
故未调用该和熵定理，也未核验其全部证明或借其自身原创性声明作为本章新意依据。

有限检索未发现直接涵盖上述完整实际后验结论的原文，不构成全球原创性认证。
新增综合的范围是固定参数、两种实际实验、完整精确中心和同一标签实现。
全部恢复读数均为潜在标签的精确增广；没有规模一致分离下界、有限位数、抗噪或计算效率结论。


### 完整组计数的最小熵与条件化最大原子

定理 68.6 使用的“最小熵”是每个原始数据纤维上 $-\log_2\max_n p_x(n)$。
Geoffrey Smith，*On the Foundations of Quantitative Information Flow*，FOSSACS 2009，
LNCS 5504，288–302，[DOI:10.1007/978-3-642-00596-1_21](https://doi.org/10.1007/978-3-642-00596-1_21)，
§5、定义 1–4，区分最大原子、其负对数与对输出平均后的猜测成功概率。
后两种操作不能交换；本章未把纤维最小熵等同于平均成功概率的负对数。
二项模态距均值至多一、紧参数区间的最大原子为 $(1+n)^{-1/2}$ 阶，均是成熟有限分布工具。
正文分别用相邻概率比、Fourier 上界与 Chebyshev 下界给出所需版本，包括空组。

新增推导在于实际固定 $q$ 后验的相对原子比较。
完整窗口有 $O(Q^2)$ 个组，乘积模态的总数偏移因而为 $O(Q^2)=o(\sqrt q)$。
将它代入补集 Bernoulli 中心原子的精确密度比，得到实际最大原子与乘积最大原子之比趋一；
再接全行对数占据数估计，得到与 Shannon 熵相同的 $Q^5$ 主系数。
加性 $O_{\mathbb P}(Q^{-5/2})$ TV 误差不能控制 $2^{-cQ^5}$ 量级的原子，
所以本结论不由第 68.5 条的有限字母表熵连续性直接推出。
这不是新的抽象最小熵定义或一般二项定理，也不声称数据平均最大原子的同阶指数。

### 完整后验的熵差与中心化信息量

定理 68.7 将完整组计数的 Shannon 熵与最小熵相减，得到
$Q^2\ell(r,\beta)/(2\log2)$ 的次阶系数。
每个大二项坐标贡献半 nat 是经典事实：上述 Adell–Lekuona–Yu
[arXiv:1001.2897v1](https://arxiv.org/abs/1001.2897v1) 的 Theorem 4、Corollary 1
与式 (7)，结合二项模态的 Stirling 界，直接涵盖该步。
新增综合是完整实际后验的绝对熵比较，以及实际占据区域的测度系数。
补集中心原子的密度比具有 $O_{\mathbb P}(Q^{-5/2})$ 的 $L^2$ 误差，
乘积信息量的方差只有 $O(Q^2)$；先消去均值再用 Cauchy–Schwarz，
将实际 Shannon 熵误差压到 $O_{\mathbb P}(Q^{-3/2})$。
模态处同一密度比使最小熵误差为 $O_{\mathbb P}(Q^{-5/2})$。
这不同于以完整字母表大小乘 TV 的一阶界。

James Melbourne、Gerardo Palafox-Castillo，*A discrete complement of Lyapunov's inequality and its information theoretic consequences*，
[arXiv:2111.06997v1](https://arxiv.org/abs/2111.06997v1)。
原始 TeX 的 Theorem 1.1 要求单调且 log-concave 的序列；
Theorem 2.5 在同样单调条件下给离散 varentropy 严格小于一。
一般二项概率序列并非单调，且实际 $p_j$ 只是趋近 $1/2$，不是恰等于 $1/2$，
故不能用 原文的精确对称扩展代替本章的统一二项信息量矩界。
正文从全部二项原子的上下界和四阶矩证明所需版本。

Matthieu Fradelizi、Mokshay Madiman、Liyao Wang，*Optimal concentration of information content for log-concave densities*，
[arXiv:1508.04093v2](https://arxiv.org/abs/1508.04093v2)。
原始 TeX 的 Theorem 2.3 对 $\mathbb R^n$ 上具有 log-concave Lebesgue 密度的向量给
varentropy 不超过 $n$，并注明此前 Nguyen 与 Wang 的证明。
它的测度与连续密度条件不覆盖这里的离散计数分布；本章未将其直接离散化。

Jonathan Hermon、Xiangying Huang、Francesco Pedrotti、Justin Salez，*Concentration of information on discrete groups*，
[arXiv:2409.16869v1](https://arxiv.org/abs/2409.16869v1)。
原始 TeX 的 Assumption 1 与 Theorem 1 要求有限支持跳率、可逆性和共轭不变性，
研究从群单位元出发的连续时间随机游走。
其 varentropy 与自由 Abelian 游走比较不提供本章后验计数的所需表示。
这里仅以该文定位离散信息量集中这一邻近问题，不调用其界。

本章的正区域、负区域和固定过渡条带划分保留零计数左端点；
在相减后取极限，因此无需分别取得两个 $Q^5$ 阶熵的次阶展开。
结论仍是固定参数下的数据概率极限，不是期望熵、全局新颖性或有限规模解码保证。


### 完整后验的信息谱、方差密度与固定误差覆盖

定理 68.8 的信息量在 $Q$ 尺度上有正态波动，中心为每份数据的精确 Shannon 熵。
其方差系数为 $\ell(r,\beta)/(2(\log2)^2)$：
每个指数占据的二项组贡献半 nat 平方，宏观正占据区域贡献 $\ell Q^2$ 个组。
这与一阶熵所积分的率函数高度不同，也不是将 $Q^5\mathscr H$ 当成足够精确的中心。
新增承重步骤是完整实际占据区域、统一二项信息量四阶矩、
条件化密度的 $L^2$ 控制与中心化熵比较共同连接到同一后验计数向量。
实际信息量方差另由密度加权的四阶矩估计传递，不从弱收敛推断矩收敛。

Ioannis Kontoyiannis、Sergio Verdú，*Lossless Data Compression at Finite Blocklengths*，
[arXiv:1212.2668v1](https://arxiv.org/abs/1212.2668v1)。
原文第 9 页 Theorem 2 及第 10 页 Theorem 3 对一般有限离散源给信息量与最优码长的上下比较；
其小原子集合论证直接涵盖正文所用的覆盖不等式，正 slack 的余项为 $2^{-t}$。
第 10 页还说明直接界可以扩展到可数字母表。
本章采用有限集合大小的写法，以免码长约定带来一位偏移；不把此经典信息谱论证据为新内容。

同文第 23–26 页 Theorems 16–17 的更精确正态编码近似使用固定分布的有限字母表无记忆源、
正 varentropy 及其矩条件；展示的直接界限定 $0<\varepsilon\le1/2$。
第 27–29 页 Theorems 18–20 则对有限状态、不可约、非周期的固定阶 Markov 源施加条件。
这里给定数据后的组计数是增长维数、非同分布二项坐标再条件于总数的分布，
其原始数据来自路径并不使后验组序列变成该有限状态 Markov 源。
正文独立证明辅助三角阵极限，随后只对完整计数向量使用一次实际密度比较。

上述 Melbourne–Palafox-Castillo 原文的单调或精确对称假设仍不直接覆盖全部校准二项组。
全原子二项下界与 Bernoulli 八阶中心矩保证统一信息量四阶矩，
中心区域的 Stirling 展开与普通二项 CLT 再识别单组方差极限为 $1/2$。
Boistard–Lopuhaä–Ruiz-Gazen
[arXiv:1207.5654v1](https://arxiv.org/abs/1207.5654v1) 的式 (2.1)、(2.5)
涵盖经典固定总数条件化及 Bayes 原子比；Lemma 1 和 Theorem 1 的包含概率展开是固定阶，
不提供随完整窗口增长的熵或信息量结论。正文使用自行给出的全计数密度估计。

Hayashi 的 *Second order asymptotics in fixed-length source coding and intrinsic randomness*
在此次文献检索中定位到 [arXiv:cs/0503089v2](https://arxiv.org/abs/cs/0503089v2)，
但原文下载返回失败，未以其定理作为已核实前提。
Hájek 1964 的原始文献地址返回 HTML challenge，也未当作已读论文。
这些来源获取边界不由元数据补足。
精确标量的覆盖结论只使用定理 68.2 已证明的原子重标记及已核对的 Baker–Wüstholz 前提，
不提供噪声稳定性、消失误差参数的一致性、期望覆盖数或有效算法。

### 第 69 章：有限反射比较、核心平方和与原标量噪声

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)第 69 章在原实际模型中，
向精确组电荷的对数半径核心加入不另行揭示的独立 Gaussian 测量噪声，再计算平方和。
多项式噪声 Q^(-2) 和指定指数噪声 exp(-c_q lambda/100) 均使新对角标量与原 T_M 的差趋零，
保留同一旧组束的联合弱极限；同时，均匀支持先验下任意可测规则的原偶极符号成功率趋于一半。
新增桥梁是实际完整后验的一次向量比较、精确中心的反射加权误差、增长核心维数的累计控制，
以及被删平方质量在对角尺度上的速度。以下经典结果提供工具和比较边界。

Yury Polyanskiy、Yihong Wu，*Dissipation of information in channels with input constraints*，
[arXiv:1405.3629v1](https://arxiv.org/abs/1405.3629v1)。
所请求的版本摘要标识为 2014 年 5 月，取得的原作者 PDF 封面却标 2021-11-26；此版本日期差异未解决。
实际核对的是该 PDF 第 11 页 Section 2.3、Theorem 4 证明中的式 (40)：
输入任意耦合经相同加性噪声后，输出 TV 由平移噪声律的 TV 的耦合期望控制。
该式不要求输入有密度。第 13 页 Proposition 7 进一步要求一维噪声密度对称、在正半轴单调不增，
并把平滑 TV 与 Wasserstein 距离联系起来。第 14 页式 (59) 针对有有限第三绝对矩的
独立同分布标准化标量和；它不直接给异质增长维数后验核心的误差。
本章仅用式 (40) 所属的经典混合凸性及等协方差 Gaussian 平移公式，直接写出任意有限维界。
分组 Bernoulli 到 Gaussian 的误差及其相对指数噪声的剩余指数在实际模型中另行证明。

Luc Devroye、Abbas Mehrabian、Tommy Reddad，*The total variation distance between high-dimensional Gaussians*，
[arXiv:1810.08693v1](https://arxiv.org/abs/1810.08693v1)，版本戳 2018-10-19，取得的 PDF 内部日期为 2021-11-01。
第 4–5 页给正定 Gaussian 亲和度公式和 Proposition 2.2 的 Hellinger—TV 比较。
本章参考协方差的对角元为 v_j+sigma²>0，满足该公式条件；独立坐标亲和度相乘。
真正需要控制的是随核心维数增长的方差比平方和与反射均值的 Mahalanobis 平方和，
不能把逐坐标误差小当成整个向量 TV 小。
该版本第 4 页另一个仿射变换协方差展示式包含平移项且遗漏末尾转置，另有 KL 标号方向问题；
两者均未调用。本章使用的亲和度可由 Gaussian 积分独立核对，不从这些附带展示式推导。

Lawrence D. Brown、Andrew V. Carter、Mark G. Low、Cun-Hui Zhang，
*Equivalence theory for density estimation, Poisson processes and Gaussian white noise with drift*，
Annals of Statistics 32 (2004), 2074–2097，
[DOI 10.1214/009053604000000012](https://doi.org/10.1214/009053604000000012)，
[原刊重印 arXiv:math/0503674v1](https://arxiv.org/abs/math/0503674v1)。
PDF 第 5 页 Theorem 1 要求密度类有共同严格正下界，并在 B(1/2,2,2) 与 B(1/2,4,4) 中紧。
第 14 页 Theorem 4 用 Poisson 计数加均匀抖动后作带符号平方根变换，
给与 N(2sqrt(lambda),1) 比较的平方 Hellinger 展开，首项为 7/(96lambda)。
它们是离散平滑与实验比较的原始先例；其变换、密度类及统一假设不同于本章的精确后验电荷。
本章没有从弱极限或单个噪声通道的 TV 比较推断 Le Cam 实验等价。
Carter 2002 多项式—多元正态缺损距离文章的取得响应不是 PDF，故未借其标题承载原始定理。

Vlad Bally、Lucia Caramellino、Guillaume Poly，*Regularization lemmas and convergence in total variation*，
[arXiv:1907.12328v1](https://arxiv.org/abs/1907.12328v1)。
PDF 第 12 页 Lemma 3.6 显式缩放卷积核并给平滑距离界；
第 14–15 页 Lemmas 3.8、3.10 还需控制其平滑性和逆 Malliavin 协方差量或行列式。
这些条件不能从离散 Bernoulli 电荷自动取得，也不是增长维数中免费的统一常数。
本章的定量分位数耦合与 Gaussian 平移界已经足够，未调用这些更强条件的定理。

相关比较包括 Frédéric Ouimet 的
[arXiv:2001.08512v1](https://arxiv.org/abs/2001.08512v1) 中多项式局部展开，
以及 Kolyan Ray、Johannes Schmidt-Hieber 的
[arXiv:1608.01824v1](https://arxiv.org/abs/1608.01824v1) 中密度估计与 Gaussian 白噪声的缺损距离研究。
前者所核对的第 1–3 页版本没有替本章解决增长维数应用；后者第 7 页 Theorem 2
保留平滑密度与低强度条件，不能仅凭平滑动作迁移到原后验实验。
本章直接推导 Bernoulli 和的局部 CLT 误差、四阶尾控制和耦合精度，未引用这些模型的实验等价结论。

Yiguo Liang、Yanjun Han，*Sharp mean-field analysis of permutation mixtures and permutation-invariant decisions*，
[arXiv:2509.12584v1](https://arxiv.org/abs/2509.12584v1)。
第 24 页 Section 3.1 讨论置换不变决策的均匀置换 Bayes 表示；
第 9 页 Theorem 1.9 是独立 Gaussian 位置观测及平方误差遗憾结果，需其有界、次 Gaussian 或弱 l^p 参数条件。
本章没有调用该遗憾定理，只直接使用支持置换的传递性，
把先验平均符号风险转成置换不变规则类中的一致确定支持风险。
不受限制的规则可写死某一支持，在该支持下恒正确，故不可能有不受限制的逐支持一半成功率结论。

噪声施加的位置也与 holographic phase retrieval 不同。
Barmherzig、Sun、Candès、Lane、Li 的
[arXiv:1901.06453v1](https://arxiv.org/abs/1901.06453v1) 使用已知空间参考及 Fourier 强度观测；
该请求版本的 PDF 封面日期与版本标识不一致，未据此作年代判断。
第 8、10–11 页被核对的互相关构造与 Poisson 噪声方差比较保留其指定重建器范围，
不提供电荷域平滑下任意解码器的 Bayes 风险。
其关于带噪最小二乘的无条件宽读有一个解析反例：取一个像素、参考 R=1、m≥3，
未知标量 x 的强度为 |x+exp(2pi i l/m)|²。若各频率的噪声数据均为 1+c、c>1，
非零滞后互相关为零，反卷积返回 x=0；而令 t=|x|²，完整强度最小二乘目标除去正重复因子为
(t-c)²+2t，极小点在 t=c-1>0。这不推翻其正确的互相关反演或指定线性映射的误差恒等式，
只排除由它们推出一般非线性带噪最优性的宽读。本章不使用该最优性声明。
Li、Hu、Xu、Shen、Fessler 的
[arXiv:2305.07712v1](https://arxiv.org/abs/2305.07712v1) 第 4–5 页使用强度域
Poisson/Gaussian 噪声似然与算法；已知参考、噪声域和算法范围均不是本章的任意解码器实验。

本章不把 Gaussian 平滑、亲和度比较、Slutsky、二次展开或反射成功集论证单独据为新理论。
新增实际关系是：隐藏噪声后重新计算的标量保持原对角尺度，而精确反射 TV 与符号耦合控制了
所有可测规则；第 68 章的原精确标量则保留全部组计数。
对原 T_M 直接加入任意固定 c Q^(-p) Gaussian 噪声的结论由第 69.5 条另行证明。
它把已知偏差扣除后的核心平方和与原加噪标量作有限通道比较，并在混合中保留同一完整标签，
所以原目标符号的耦合仍在，能控制所有可测解码规则。
对每个固定 p,c>0 分别成立，不包含增长指数、指数尺度直接噪声、任意量化、计算效率或完整实验等价。
有限文献核对不构成全球原创性认证。

Frédéric Ouimet，*Refined normal approximations for the central and noncentral chi-square distributions and some applications*，
[arXiv:2201.07407v1](https://arxiv.org/abs/2201.07407v1)，版本戳 2022-01-19，PDF 封面 2022-01-20；
后续期刊 DOI 10.1080/02331888.2022.2084544 未替代本次核对的版本。
原文第 1–2 页定义非中心卡方及同均值方差正态比较；第 6 页 Lemma 3.1、
第 7 页 Theorem 3.2、第 9 页 Theorem 4.1 均保留非中心参数 Lambda=o(sqrt(m))。
Theorem 4.1 的 TV 等距离界为 C/sqrt(m)。本章核心条件于实际电荷的非中心参数
Lambda=E_c/sigma²，主例为 Q^4，维数仅为 O(Q^(1/2)sqrt(log Q))，故不满足其非中心性范围。
本章直接沿实际电荷向量旋转独立测量噪声，再用截断微分同胚的密度换元，
给已扣偏差二次扰动 C sigma(1+sqrt(m)) 的 TV 界。
旋转、正态密度计算与混合凸性都是经典机制；新增义务是整个实际窗口被删平方质量在噪声尺度下趋零，
并让通道比较附带同一原标签及符号。局部精确中心尾界使每个固定多项式尺度均可处理。
未把“小耦合误差”单独当成 TV 保证，也未声称发现新的通用非中心卡方定理。
原文引用的 Horgan–Murphy、Seri、Temme 是后续检索线索；本次未取得其可用原始定理，
不以二手 CDF 描述或未命中的搜索断言不存在更一般的大非中心参数 TV 结果。


### 实际后验矩与标量 Gaussian 通道的信息界

定理 69.6 的信息不等式属于经典 Gaussian 通道理论。
Guo、Shamai、Verdú，*Mutual Information and Minimum Mean-square Error in Gaussian Channels*，
[arXiv:cs/0412108v1](https://arxiv.org/abs/cs/0412108v1)，§II-A、定理 1、式 (15)，
假定实输入具有有限二阶矩、标准 Gaussian 噪声独立，证明以自然对数计的
$\mathrm d I/\mathrm d\mathrm{snr}=\mathrm{mmse}/2$。
用线性估计器的 $\mathrm{mmse}(s)\le v/(1+sv)$ 积分可直接得到
$I(T;T+\sigma G)\le\tfrac12\log(1+v/\sigma^2)$。
本章也在有限混合上给出相对熵分解证明，因此无需借用信道编码定理或假定输入 Gaussian。
Shannon 1948 年原文 §24–25、定理 16–17 给出独立加性噪声与功率约束容量的历史来源，
但不负责当前实际后验方差的渐近控制。

Arratia、Goldstein、Langholz 的
[arXiv:math/0506300v1](https://arxiv.org/abs/math/0506300v1)
条件 2.1 要求 $\sum_{j\le n}p_j(1-p_j)\ge\varepsilon n$，定理 2.1 的高阶局部展开承接该条件。
当前全体标签数为 $M$、方差仅为 $\asymp q=o(M)$，所以不能直接引用该版高阶定理。
本章使用特征函数模界与三阶余项，直接证明仅依赖总方差趋无穷的
$O(d^{-1})$ 绝对局部误差；它足以控制校准中心原子与补集最大原子。

Boistard、Lopuhaä、Ruiz-Gazen，*Approximation of rejective sampling inclusion probabilities
and application to high order correlations*，
[arXiv:1207.5654v1](https://arxiv.org/abs/1207.5654v1)，§2 的固定总数条件化与
定理 1 的固定阶包含概率展开是相关成熟工具；§3 部分抽样率推论另用总体大小除以方差有界，
不满足当前稀疏总体的范围。固定阶展开也不能不经求和估计就承担增长组数的平方统计量矩界。
该版命题 1 对任意正整数幂声称中心乘积为 $O(d^{-2})$，不能使用：
平衡简单随机抽样中 $p_i=\pi_i=1/2$、$d=N/4\to\infty$，三个不同指标均取二次幂，
乘积却恒为 $1/64$。原版 TeX 与 PDF 均含“任意正整数”条件；此处只排除这一版本的这一断言，
不推断其余定理或后续版本错误。

本仓新增推导是：对两种实际平稳实验，完整计数线的一、二行相对概率估计给出
$\sum_jv_j^2=O_{\mathbb P}(\delta)$；固定总数后验相对校准乘积律的统一密度上界，
连同精确中心的 Hilbert 范数估计，进一步给出实际条件二阶矩
$\mathbb E_xT_M^2=O_{\mathbb P}(1)$。这一步不由弱收敛或 TV 接近直接推出。
随后经典信息界与第 68 章熵率合成直接噪声的剩余熵结论。
它不等同于单个符号的风险界，不把坏数据上的有限矩当作一致可积，
也不提供平均于原数据的期望信息极限。所查来源未直接给出这条完整实际模型结论；
有限文献范围内未命中不构成全局原创性认证。


### 连续噪声通道的猜测包络及其实际模型范围

定理 69.7 的条件 Bayes 公式是猜测成功率的经典表示。
Smith 2009 的 §5、定义 3–4 及其离散输出公式给出相应有限字母表解释；
对 Gaussian 连续输出，正文直接证明有限最大值的可测性与最优积分公式。

Issa、Wagner、Kamath，*An Operational Approach to Information Leakage*，
[arXiv:1807.07878v1](https://arxiv.org/abs/1807.07878v1)，
定理 7 和引理 7 将最大泄漏写为条件密度本质上确界的积分。
其条件包括乘积 sigma 代数、$P_{XY}\ll P_X\times P_Y$ 与可数生成的输入 sigma 代数。
当前每份数据的可行计数输入有限，输出是严格正的有限 Gaussian 混合，故条件逐一满足；
本质上确界变成有限最大值。其操作含义直接控制最优猜测成功率的乘法增益。
若把有限标量均值集合扩大为一个长度 $L$ 的区间，Gaussian 包络积分为
$1+L/(\sqrt{2\pi}\sigma)$；这是有限通道泄漏的上界，不声称有限通道恰等于连续区间包络。
该原文例 10 展示全实线输入支撑时加性连续噪声的最大泄漏可为无穷，
所以不能仅凭噪声为 Gaussian 就略去输入范围条件。

Saeidian、Cervia、Oechtering、Skoglund，*Pointwise Maximal Leakage*，
[arXiv:2205.04935v1](https://arxiv.org/abs/2205.04935v1)，§II-A 的定义 1 与定理 1
以有限输入输出字母表讨论单个输出上的后验／先验比。
它不等于本章对连续噪声输出积分的 Bayes 成功率，亦不能据此把本章结论改成逐输出断言。
本章没有调用该版有限输出结论来处理连续输出。

本仓新增组合保留原完整计数和精确后验中心：所有原 $T_M$ 值所在区间的长度
至多 $4qQ^{11/4}$，其对数仅为 $c_qQ^3+O(\log Q)$。
将这一确定范围与定理 68.6 的实际最大原子指数连接，得到任意
$\log^+(1/\sigma_M)=o(Q^5)$ 下完整计数恢复的条件 $Q^5$ 指数。
它不需要把电荷域平滑结果移到更小的标量噪声，也不依赖实际后验矩界。
例如 $e^{-Q^4}$ 噪声已覆盖，但这不延伸固定多项式噪声的偶极符号定理。
先验平均成功概率只能据此断言趋零；坏数据概率与共同判向错误没有所需的 $Q^5$ 指数控制。
一般猜测包络属于已有信息论，本章新内容是完整实际后验原子和原标量范围之间的连接。
所查原始来源没有直接给出这一平稳对／路径、固定基数后验的完整结论；不据此宣称全局原创。

### 第 70 章：实际 Rényi 熵谱、计数幂倾斜与支持极限

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)第 70 章
保留第 68 章同一完整窗口、组计数和精确固定基数后验。
每个固定正阶的主系数相同，而零阶支持熵的主系数是它的两倍；
当阶数按 exp(-sQ³) 缩小时，完整闭域上的截断积分给出两者之间的过渡。
这里的对象始终是组计数元组，未把一个计数拆成多个标签排列再计算熵。
下列原始结果承担成熟工具的归属，不把 Gaussian Rényi 公式或一般极限不交换据为新发现。

James Melbourne、Tomasz Tkocz，*Reversals of Rényi Entropy Inequalities under Log-Concavity*，
[arXiv:2005.10930v1](https://arxiv.org/abs/2005.10930v1)，原始 TeX `Journal.tex`，
引言主定理 `thm: infinity comparison` 及其同名证明节。
原文对整数上的对数凹概率质量函数，要求正支撑为连续整数区间，给出自然对数单位下
$H_\nu-H_\infty<\log\nu/(\nu-1)$，$0<\nu<\infty$，阶数一取连续延拓。
此定理不要求质量序列单调；其证明用同最大质量的双边几何律、majorization 与 Rényi 熵的 Schur 凹性。
二项计数律满足这些条件，所以该结果直接覆盖 (70.17) 所需的固定阶有界差。
它不提供本模型每组半倍 Gaussian 的极限常数、指数缩小阶数的截断过渡，
也没有承担实际固定总数条件化的误差。
这与 Melbourne、Palafox-Castillo 的
[arXiv:2111.06997v1](https://arxiv.org/abs/2111.06997v1)
中要求单调对数凹序列的尖锐比较与 varentropy 定理有不同适用范围。
一般二项序列先升后降，近似对称也不等于其另列的精确对称假设。

Joseph B. Kadane，*Sums of Possibly Associated Bernoulli Variables: The Conway-Maxwell-Binomial Distribution*，
[arXiv:1404.1856v1](https://arxiv.org/abs/1404.1856v1)，原始 TeX `comMAR2014.tex`，
§2 式 `eq:one` 定义有限支撑质量
$P(W=k)\propto p^k(1-p)^{m-k}\binom mk^\nu$；§3 给指数族表示，§4 给生成函数。
本章二项计数质量的幂倾斜恰属此族，但 Kadane 的成功参数须取
$\operatorname{logistic}(\nu\operatorname{logit}p)$，不是原二项成功参数 $p$。
取幂作用于组合因子与概率因子两者，不能用独立标签幂倾斜后的二项计数替代。
所核对原文的共轭先验适当性定理与当前估计不同，未被调用；
其可交换 Bernoulli 表示也不把本章的实际固定大小标签改成另一抽样模型。
本章直接以两个独立计数条件于和，比较折叠离散 Gaussian，证明
$\operatorname{Var}_\nu R\le Cn/\nu$ 及近半参数下的均值偏移界。
这些估计在 $\nu\downarrow0$、占据数增长的共同范围内使用。

Hervé Bergeron、Evaldo M. F. Curado、Jean-Pierre Gazeau、Ligia M. C. S. Rodrigues，
*Entropies of deformed binomial distributions*，
[arXiv:1412.0581v1](https://arxiv.org/abs/1412.0581v1)，原始 TeX `gbin_entrop_vf.tex`，
引言式 `renyiq` 的熵幂和为
$\sum_k\binom nk(\mathfrak p_k^{(n)}/\binom nk)^\nu$。
它将每个计数质量均分给其微观排列，研究 q-exponential、修正 Abel 多项式与 Hermite 多项式产生的变形。
这个对象与本章 $\sum_k f_{n,p}(k)^\nu$ 不同，
因此其关于 extensive Rényi entropy 的系数不能迁入本章。
该来源只用于明确聚合层次的边界，未作为本章渐近系数的前提。

固定阶二项熵的中心展开、Stirling、Gaussian 幂积分和 Rényi 单调性都是经典工具。
Adell、Lekuona、Yu 的
[arXiv:1001.2897v1](https://arxiv.org/abs/1001.2897v1)
定理 4、推论 1 与式 (7) 提供 Shannon 二项熵修正；其紧参数区间上的系数支持第 68 章的阶数一比较。
固定阶展开不能直接代入随规模指数缩小的阶数。
本章从覆盖全部二项原子的双边 Gaussian 指数界推出统一幂和估计，
同时控制宽度 sqrt((n+1)/nu) 与完整支撑长度 n+1，包含二者相等的过渡区。

固定总数条件化、补集指数倾斜与 Fourier 局部估计也属于成熟概率方法。
Arratia、Goldstein、Langholz 的
[arXiv:math/0506300v1](https://arxiv.org/abs/math/0506300v1)
条件 2.1 要求总方差至少为标签总数的固定正比例；这里总标签数 M、方差约 q/2=o(M)，不满足此条件。
正文使用只需总方差趋无穷的局部估计，并对每个补集倾斜律重新在其整数均值处应用。
Boistard、Lopuhaä、Ruiz-Gazen 的
[arXiv:1207.5654v1](https://arxiv.org/abs/1207.5654v1)
中 rejective sampling 与固定阶包含概率是相关原始工具，未直接给出增长计数向量的幂倾斜比较。
第 69 章已列的该版任意正整数幂命题反例仍限定于那条原文断言，本章不使用它。

本仓新增连接是：实际计数线的得分接近阈值达到 q^(-1/2) 精度，
补集的完整盒对数密度比由倾斜控制，计数幂倾斜的平方偏移再乘阶数抵消其方差增长。
由此，实际后验与独立计数律的 Rényi 熵差对全部 0<nu≤1/2 一致为 O_P(Q^(-5/2))，
极端元组本身很小的密度比不妨碍完整幂和。
这条桥梁与实际全域占据数相接，才产生本模型的移动阶数过渡。
结果限于两种实际实验的数据概率极限，以及同一先验后验函数的一致确定支持评价；
不含期望熵、负阶、变化的 beta、增长正阶、效率或噪声解码结论。
所核对原始文献没有直接给出这条完整实际模型陈述；有限检索范围不构成全球原创性认证。

### 第 71 章：带噪条件信息谱与列表恢复

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)第 71 章
连接定理 68.8 的实际后验信息谱和定理 69.6 的实际标量矩界。
直接 Gaussian 噪声满足 logplus(1/sigma)=o(Q) 时，输出后验的惊奇量在联合纤维律中
保留同一 Q 尺度正态极限，最优输出平均列表成功率及固定误差列表大小随之确定。
原标量、完整计数和精确后验中心保持一致；没有将旧弱极限当作信息论实验的替身。

Kontoyiannis、Verdú，*Lossless Data Compression at Finite Blocklengths*，
[arXiv:1212.2668v1](https://arxiv.org/abs/1212.2668v1)，PDF 第 9–10 页、Section II、定理 2–3，
给一次信息随机变量的可达／逆向阈值及正松弛惩罚。
其有限字母表计数论证直接覆盖 (71.15)，亦可逐输出用于有限后验后再积分。
该版定理 16–20 的后续正态近似分别保留固定有限字母表无记忆或有限状态 Markov 源假设；
它们不能仅凭原观测是一条平稳路径就代替这里增长组数、随机环境和固定总数后验的 CLT。

Gavalakis、Kontoyiannis，*Sharp Second-Order Pointwise Asymptotics for Lossless Compression with Side Information*，
[arXiv:2005.10823v1](https://arxiv.org/abs/2005.10823v1)，PDF 第 4 页定义 2.1
以条件原子概率排序描述最优条件压缩，定义 2.2 与定理 2.3 给条件信息和码长的比较。
第 6 页 Assumption (M) 要求固定有限字母表源与侧信息对平稳，并满足三种条件之一：
严格正转移的 Markov 对；对与侧信息均为有限阶不可约非周期 Markov 链；
或联合遍历并有文中 alpha(d)=O(d^(-336))、两项 gamma(d)=O(d^(-48)) 的混合界。
第 8 页 Section 2.5、定理 2.10 在这些条件及正条件 varentropy 下给精确熵中心的条件信息 CLT。
这是相关经典结果；本章单个 Gaussian 侧通道随 M 改变，计数字母表与后验环境也改变，
未调用其固定过程条件 CLT。

Tan、Moulin，*Fixed Error Probability Asymptotics For Erasure and List Decoding*，
[arXiv:1402.4881v2](https://arxiv.org/abs/1402.4881v2)，PDF 第 8 页定理 2
研究固定 DMC 的二阶列表容量及多项式列表的第三阶界。
同页命题 3 给平均错误列表码的假设检验逆界，核心比值为消息数除以列表大小；
Section IV 接着讨论带编码器和擦除选项的 Slepian–Wolf 侧信息问题。
这些结果表明列表预算和次阶信息谱逆界是成熟工具。
本章没有消息编码器，输入为数据依赖的非均匀后验，原熵中心随机，
因而没有从固定 DMC 的容量公式直接取得当前成功率曲线。

Issa、Wagner、Kamath，*An Operational Approach to Information Leakage*，
[arXiv:1807.07878v1](https://arxiv.org/abs/1807.07878v1)，
PDF 第 14 页 Section C “Multiple Guesses”、定义 4 与定理 4
在输入和输出均有限时证明 k-maximal leakage 等于 maximal leakage。
其第 17 页定理 7、引理 7 的一般字母表密度表达要求联合律相对乘积律绝对连续，
且输入 sigma 代数可数生成。本章有限正质量输入与严格正 Gaussian 混合输出满足这些条件。
多次猜测的乘法包络原理已有来源；正文直接对连续密度证明 (71.17)，
没有把有限输出定理 4 原样迁到实输出。
该版第 18 页例 10 的全实线正密度输入可有无穷全局泄漏，
因此 Gaussian 噪声本身不保证一个可用的有限范围包络。
本章用已证实际二阶矩截断上界中的输入集合，取得 Q 尺度所需的多项式半径。

A. R. Esposito，*Minimax Quantile Bounds via Information Measures*，
[arXiv:2608.20857v2](https://arxiv.org/abs/2608.20857v2)，版本戳 2026-08-26、PDF 封面 2026-08-27。
第 6 页定义 2.3、2.5 给先验小球质量和最大泄漏的支配密度表达；
第 8 页定理 3.1 给任意估计器、辅助先验和通道的损失适配 Neyman–Pearson 逆界，
第 13 页推论 3.12 给成功概率不超过先验小球质量乘泄漏指数。
将动作取为大小至多 K 的列表、损失取为目标未在列表中，即有一般列表成功原理；
正文的直接有限求和证明明确处理该动作空间及连续输出。
该原文将框架归于既有信息论方法，不能作为本章发明通用列表逆界的依据。
它也不承担当前实际计数线、精确中心矩界或 Q 尺度条件信息谱。

Saeidian、Pinzón、Palamidessi，*Information Leakage Envelopes*，
[arXiv:2605.21185v1](https://arxiv.org/abs/2605.21185v1)，PDF 第 2 页 Section II.A 明定所有集合有限。
第 6 页定理 2、第 7 页定理 3 的 envelope 是对后处理取上确界的逐输出泄漏分位保证，
并由最大泄漏加 log(1/delta) 与最坏输出界控制。
它与 (71.17) 积分的 Gaussian 位置密度包络不是同一对象；
没有凭名称相同就把有限输出、后处理或逐输出保证转给本章。

Gaussian 最大熵、链式法则和信息密度的负尾界均为经典机制。
正文由严格正通道直接计算 E exp(-i)=1，得到 E|i|≤I+2；
这一步连同已证原信息谱，才将 o(Q) 互信息转成输出后验惊奇量的 o(Q) 扰动。
一个平均熵数本身不能确定分位曲线；加入原信息谱后可以，故没有宣称 Shannon 界绝对不能用于列表问题。
新增组合在原实际模型中保留固定基数、依赖路径、完整窗口和中心项，并将这些条件接到可测最优列表。
置换不变随机策略核的确定支持风险由群传递性证明：对可测最优列表作独立均匀群对称化，
每次保留相同大小与最优后验质量；碰撞时不要求字典序破平局本身等变。
成功率也对这项独立随机性平均，不包含能写死支持的不受限制规则。
结果对噪声输出平均；未声称每个输出后验的逐点 CLT、期望熵展开、变化误差水平或效率。
所查原始来源没有直接给出这条完整模型结论，有限文献检索不构成全局原创认证。

### 第 72 章：确定熵中心与格点边缘残差

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)第 72 章
将实际后验 Shannon 熵减去完整得分组的平均占据数中心，证明其为 O_P(1)。
至多两个多项式过渡组承担全部渐近残差；任一正有限均值子序列产生实际行占据数的独立 Poisson 极限。
正文进一步以原 M 的取整区间构造一个固定合法 beta，使残差有非退化子序列极限。
这给出不能普遍加强为 o_P(1) 的实际模型反例，同时允许在既有 Q 尺度信息谱中使用确定中心。

Hillion、Johnson，*A proof of the Shepp–Olkin entropy concavity conjecture*，
[arXiv:1503.01570v1](https://arxiv.org/abs/1503.01570v1)，
原文引言定义独立 Bernoulli 和及其有限质量函数，Shepp–Olkin Theorem
（原始 TeX 标签 th:SO）对每个固定 n≥1 证明熵关于整个成功参数向量凹。
它直接覆盖固定试验次数、改变参数时的凹性；结合对称性给公平参数处的最大值。
此结论不直接给改变整数试验次数的倒数增量率，也不控制依赖实际行数上的熵波动。
正文 (72.13) 由链式法则、交换性和二元相对熵的卡方上界直接推得所需增量，
这些信息论工具为经典工具，不作为新独立理论归属。

Ioan Raşa，*Complete monotonicity of some entropies*，
[arXiv:1606.05520v2](https://arxiv.org/abs/1606.05520v2)，
Section 1 定义 $p_{n,k}^{[c]}(x)$，在 c<0 时要求 n=-cl、l 为正整数且 x∈[0,-1/c]；
c=-1 对应 Bin(n,x)。Section 2 第一条定理给关于 x 的正偶阶导数非正，
以及奇阶导数在 -1/(2c) 两侧的符号。
这里变化的是成功参数，不能把导数改名为关于整数 n 的增量，
也不能据此宣称随机占据数的浓缩。正文的参数扰动界另由二项 varentropy
和得分协方差给出，所需 O_P(Q^(-1/4)) 总误差保留实际近半校准率。

Adell、Lekuona、Yu，*Sharp bounds on the entropy of the Poisson law and related quantities*，
[arXiv:1001.2897v1](https://arxiv.org/abs/1001.2897v1)，
原文定理 4、推论 1 和式 (7) 的二项熵界要求整数 n,m≥1、p∈(0,1)，
系数在成功参数紧区间上有界。其公平参数特例直接给
H(Bin(n,1/2))=log(pi e n/2)/(2 log 2)+O(1/n)。
第 72 章只在高占据组上使用这一成熟展开；零组单独定义，有限均值过渡组保留精确二项熵。
原均值的阶乘、M 与 q 的下取整及补偿参数均未以粗率函数替代。
实际均值与显式均值即使相差 o(1)，跨过整数时仍可留下一个熵增量，
因此正文只给两个中心相差 O(1)，没有把它冒报为 o(1)。

Barbour、Gnedin，*Small counts in the infinite occupancy scheme*，
[arXiv:0809.4387v1](https://arxiv.org/abs/0809.4387v1)，
引言的模型将球独立投向固定概率 p_1≥p_2≥⋯>0、总和为 1 的无限盒子；
X[n,r] 是恰含 r 个球的盒数。命题 2.2 要求 k(n)→∞、
k(n)exp(-np[k(n)]/10)→0，并取 m(n)≤np[k(n)]/2，
以 TV 比较小计数向量与其 Poisson 化版本。
Section 3 定理（原始 TeX 标签 approximation）要求各选定计数方差发散，
得到随规模改变协方差的多元正态近似；收敛到固定正态律还要求协方差矩阵收敛。
该文关于指数衰减频率的振荡说明格点效应有成熟背景。
这些变量与假设并不直接对应本章的依赖路径行、移动二计数标记或有限均值边缘组。
正文用原有限秩 PGF 的任意固定多行系数比较和混合下降阶乘矩，
单独证明实际两种实验的有限均值 Poisson 极限，未假定原行独立。

Gnedin、Hansen、Pitman，*Notes on the occupancy problem with infinitely many boxes:
general asymptotics and power laws*，
[arXiv:math/0701718v2](https://arxiv.org/abs/math/0701718v2)，属于相关背景检索。
该版本 PDF 可取得，原始源文件请求返回 HTTP 403；本章没有从它导入未核对的定理条件。
已有 Arratia–Goldstein–Langholz 的总方差占比条件与本模型不合，
以及既有 rejective-sampling 版本中未使用的高幂矩表述边界，均维持先前归属；
本章的后验熵比较使用方差参数本身的 Fourier 局部估计与密度范数。

新增组合的实质在于同一实际模型内的定量连接：
完整窗口的近半参数替换为 o_P(1)，高占据组的倒数增量误差求和为 o_P(1)，
严格凸率函数的至多两个阈值邻域比原格距更窄，
留下的实际行占据数再由原 PGF 得到 Poisson 极限。
嵌套原取整区间证明有限均值边缘可以由一个固定合法 beta 实现，
不需要让 beta 随规模改变或假定算术等分布。
上述经典熵、占据数和矩方法本身没有被改称原创；
所查来源未直接提供这条完整实际后验定理，有限检索不构成全局原创认证。
结果不包括 h-Eh、期望后验熵、坏数据上的一致可积、任意指定 beta 的非退化子序列、
或计算显式中心的数值效率与稳定性。纯理论正文未进入消化或 Lean 冻结链。

### 第 73 章：典型输出条件信息谱的空间分离

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)第 73 章
把第 71 章的输出平均联合信息谱提升为典型输出的条件 CDF 结论。
在 logplus(1/sigma)=o(Q³) 下，原惊奇量给定带噪精确标量后保留原正态极限；
在更窄的 o(Q) 范围内，输出后验惊奇量自身保留同一 Q 尺度极限，
并决定逐输出最优列表质量与输出依赖的固定误差覆盖大小。
两条噪声范围分别陈述，较宽范围没有被当作信息密度可忽略的保证。

Magda Peligrad，*Conditional central limit theorem via martingale approximation*，
[arXiv:1101.0174v2](https://arxiv.org/abs/1101.0174v2)，
PDF 第 3 页式 (3) 在固定过去滤子条件下，以条件期望的 L1 距离描述条件 CLT。
第 3–4 页定理 1 对平稳有限二阶矩序列刻画平稳差分鞅近似
S_n=M_n+R_n、E R_n²/n→0；条件为平均条件投影收敛及二阶矩率趋于鞅差分方差。
第 4 页定理 2 给对应的 plus-norm 等价条件。
通过受控误差传递条件极限是成熟方法；本章所给定的是随规模改变的带噪非线性统计量，
没有将固定过去滤子的结论直接移用，也不将该文测试函数措辞解释为离散到连续的 TV 极限。

Dey、Terlov，*Stein's method for Conditional Central Limit Theorem*，
[arXiv:2109.09274v3](https://arxiv.org/abs/2109.09274v3)，
PDF 第 9–10 页 Assumptions I–IV 要求交换对、中心化不相关坐标、
格点条件变量 Y∈zeta+Z、其增量属于 {-1,0,1}，
以及指定的转移概率、回归与条件二阶增量误差。
第 12 页定理 2.1 给 W|Y=k 的 Wasserstein 界，
第 13 页定理 2.4 用相邻条件原子的质量比改进该界。
本章实值 Gaussian 通道未建立这些交换对假设，故没有直接应用该条件正态定理。
第 3 页 Section 1.1 的混合反例说明弱联合 Gaussian 极限与渐近独立不足以控制某个条件输出。
其异常输出概率趋零，不能用该例单独否定典型输出结论；
正文注记 73.4 另用一位惊奇量符号说明小平均信息不够推出典型输出的原惊奇量 CLT。

Ma、Yao、Yuan、Zhang，*Entropic Conditional Central Limit Theorem and Hadamard Compression*，
[arXiv:2401.11383v2](https://arxiv.org/abs/2401.11383v2)，
PDF 第 9 页主定理 3.1 要求几乎处处绝对连续的条件密度、条件方差统一正下界、
平均 Fisher 信息统一上界、条件二阶矩的统一尾控制、平均条件微分熵收敛，
以及式 (34) 的独立副本卷积熵跳跃递推。
它给条件 Gaussian 的 KL 距离依概率趋零和条件方差集中；
再有条件微分熵的一致可积，才识别平均方差与熵极限。
第 18 页定理 4.1 与推论 4.2 对 iid 成对变量的归一化和、给定完整侧信息向量，
保留有限方差、条件绝对连续、有限平均 Fisher 信息、有限下界微分熵及条件方差正下界。
这些结论在其光滑 iid 设置下使用更强距离。
本章计数惊奇量即使给定实值噪声输出仍为有限离散分布，不满足其密度条件；
平滑输出不等于平滑惊奇量。本章没有从该文的 Pinsker 推论借来离散到连续的 TV 结论。

Kuzuoka、Watanabe，*An Information-Spectrum Approach to Weak Variable-Length Source Coding with Side-Information*，
[arXiv:1401.3809v2](https://arxiv.org/abs/1401.3809v2)，
版本戳为 2014-04-08，所取得 PDF 页脚日期为 2018-07-21，二者不混作版次推断。
PDF 第 4 页 Section II.A 采用有限或可数离散字母表，并为渐近结论规定归一化条件惊奇量的一致可积。
第 6–7 页定理 1 用误差截断条件熵刻画一次共同侧信息下的平均变长码长；
第 9 页定理 3–4 给 Slepian–Wolf 一次编码的条件惊奇量分位直接界／逆界。
第 13 页定理 7 使用一致可积，定理 9 另加条件强逆性质以识别固定误差渐近式。
这些结果给信息谱与侧信息编码的成熟背景，但其编码器、平均变长目标与离散侧信息
不等于本章的实输出后验列表；正文单独证明所用有限选择器与逐输出计数界。

Kontoyiannis–Verdú [arXiv:1212.2668v1](https://arxiv.org/abs/1212.2668v1)
PDF 第 9–10 页 Section II、定理 2–3 直接覆盖一次有限原子数阈值论证，沿用第 71 章归属。
Gavalakis–Kontoyiannis [arXiv:2005.10823v1](https://arxiv.org/abs/2005.10823v1)
第 4 页定义 2.1 的条件概率排序与第 8 页定理 2.10 的条件信息 CLT 同样相关；
后者仍保留第 6 页固定平稳有限字母表 Assumption (M) 及正条件 varentropy，
没有替代本章增长计数向量的三角阵证明。

Aldous–Eagleson，*On Mixing and Stability of Limit Theorems*，
[DOI:10.1214/aop/1176995577](https://doi.org/10.1214/aop/1176995577)，
本次原始 Euclid 文档入口以 HTTP 200 返回 HTML，未取得原始 PDF；
另一次 Dedecker–Merlevède 元数据请求为 HTTP 429。
这些检索边界没有被当作已核对的原始定理条件，正文也不以其未检查陈述为前提。

Gaussian 平移 TV 界、核收缩、同边缘联合 TV 与平均条件 TV 的等式、
独立和的可忽略方差删除、Gaussian 最大熵、信息负尾界及有限列表计数均属经典工具。
新连接是原实际模型在真实 1/sigma 精度下的空间局部化：
仅 o(Q²) 个核心组即可承载带噪精确标量，而外围计数保留惊奇量的主要方差。
原路径行依赖由实际 PGF 处理，精确尾中心项保留在核心标量中，
随后同一个后验向量的联合律比较才控制典型输出条件 CDF。
没有从零协方差、弱联合收敛或小互信息直接推断条件独立。
所查原始来源不直接给出这一完整桥梁；有限检索不认证全局原创。
本章不声称每个输出保证、零噪声结果、临界噪声锐利性、期望对数覆盖、变化误差水平或计算效率。
第 72 章确定中心的替换仅使用已量化的 o_P(Q) 误差，纯理论文本未进入 Lean 冻结或消化链。

## 原 floor 网格上的熵例外集与经典质量转移（第 74 章）

`repo-derived`：第 74 章分类第 72 章确定均值中心下不发生 o_P(1) 熵集中的参数。
原平稳对与连续路径实验给出相同的 Borel 例外集；它的 Lebesgue 测度为零，
却包含稠密 Gδ 集，在每个非空开参数区间内的 Hausdorff 维数均为 2/3。
所以参数测度意义的典型性与 Baire 类别意义的典型性在这里不同。
它们都不改变先固定参数、再取实际数据概率极限的统计量词。

关键实际连接是 beta 无关的因子 χ=2 exp(−z₀)f_j，以及
m_j=2^floor(φQ³/(beta log2)) χ (1+o(1)) 的紧参数区间上一致相对比较。
该比较保留 q 的原 floor、补偿与完整得分组。
正根产生间距 Q^-2、宽度 Q^-3 的实际参数区间；整段区间的实际均值均有正的有限上下界。
有限均值的子序列判据和实际行 PGF 的联合 Poisson 极限，使这些区间对应真正的后验熵障碍。
跨过负根出现的阈值仍可使用同一正根网格，第二个独立 Poisson 项不会消去第一项的非退化性。
两种例外集相同不意味着两种精确 floor 中心相差 o(1)。

Beresnevich–Velani，*A Mass Transference Principle and the Duffin–Schaeffer conjecture for Hausdorff measures*，
原版本 [arXiv:math/0412141v1](https://arxiv.org/abs/math/0412141v1)。
原文 “A Mass Transference Principle” 节的主定理要求球的直径趋零、维数函数 f，
以及 x^-k f(x) 单调；放大球的 limsup 在每个球中具有完整 k 维测度，
则原球的 limsup 在每个球中具有完整 f-Hausdorff 测度。
末部 “A general Mass Transference Principle” 将环境扩展到局部紧度量空间，
要求 doubling 维数函数 g、H^g(B) 与 g(diam B) 的统一可比性、f/g 单调，
并使用半径 g^-1(f(r)) 的放大球。

该一般版本直接覆盖本章的度量下界步骤：取紧参数区间、g(r)=r、f(r)=r^s、0<s<2/3，
以目标区间内部的 Q^-3 小球为原球，放大半径 Q^(-3s) 超过最大网格间隔 Q^-2。
故放大球最终覆盖每个内点；相对端点球也满足统一的一维测度条件。
这核实了局部紧区间的适用范围，不把局部网格误说成覆盖整个实轴。
正文的全尺度质量证明另明确写出子区间宽度与中点间距之间的估计。

Beresnevich–Dickinson–Velani，*Measure theoretic laws for lim sup sets*，
原版本 [arXiv:math/0401118v3](https://arxiv.org/abs/math/0401118v3)。
原文条件 (M2) 要求紧度量空间中小球的测度与半径 δ 次幂统一可比。
局部 m-ubiquity 要求每个球在所有充分晚的权重块中，有固定正比例的测度被共振邻域覆盖；
点共振的两项交叠条件自动以 γ=0 满足。
原文主 Hausdorff 定理（TeX 标签 THM3）要求 r^-δ f(r) 随 r 递减且在零处趋无穷，
r^-γ f(r) 递增，并定义 g(t)=f(ψ(t)) ψ(t)^(-γ) ρ(t)^(γ−δ)。
其第 (ii) 项在 limsup g(u_n)>0 时给无限 f-Hausdorff 测度。
第 (i) 项在该上极限为零时另有正则性与发散和条件，本章不使用该分支。

对本章取 δ=1、γ=0、权重 Q_n、块端点 Q_(n−1),Q_n，
ρ(t)=At^-2 的常数 A 足够大，ψ(t)=κt^-3 的 κ 足够小。
实际网格上下间距给局部覆盖，有限权重内的共振点有限，紧区间端点满足 (M2)。
对 0<s<2/3，g(Q_n) 与 Q_n^(2−3s) 同阶并趋无穷，故该定理也直接给所用下界。
原超稀疏序列与这里的权重条件相容，不另假定连续分母或等分布。

Borel–Cantelli、Baire、Hausdorff 覆盖、质量分布原理、质量转移和 ubiquity 都是经典内容。
本章不把 Q^-2 网格以 Q^-3 加厚所得的 2/3 指数称为独立的新度量定理。
新增综合在于完整实际实验到原 floor 区间的对应、共同例外集、两个根区间上的一致构造与统计后果。
有限文献核对没有取得直接提供这一整套实际后验/floor 结论的原定理；这不认证全球原创性。
检索未返回条目或接口超时不作为不存在定理的证据。

原实际行比较、方差型局部 Bernoulli 证明、二项熵增量及 Poisson 矩判据的来源边界继续沿用第 72 章。
不把 Barbour–Gnedin 的独立球盒模型当成原路径行的独立性定理，
也不把固定试验数的熵参数凹性当成试验数增量估计。
第 74 章另排除临界负端点的正有限均值障碍，但不判定指定 beta_* 的正根算术是否例外。
结论不包含期望熵、参数上一致收敛速率、任意指定 Poisson 均值的可达性、有限精度恢复或效率保证。

## 低噪声信息增益与 Gaussian 二次型密度（第 75 章）

`repo-derived`：第 75 章把原实际标量的噪声范围扩展到
L=ln(1/σ)→∞、L=o(Q³)，证明实际信息密度为 L+o_P(Q)。
其输出后验信息谱的中心相应为精确原熵 h_x−L/ln2，
并给典型输出的最优列表曲线与输出依赖最小覆盖数。
在 L=aQ+o(Q) 时，对数列表基数的 Q 尺度收益精确为 a/ln2，且由可测后验排序达到。
这些是概率结论，不是平均互信息或平均后验 Shannon 熵的展开。

实质桥梁在于原模型的移动核心：半径平方
R²=√[Q³(L+ln Q+1)] 为 o(Q³)，但足以在真实噪声精度压低尾部。
原一、二行 PGF 比较与局部 Poisson 率下界使其中每个未归一化二项方差至少为 exp(c_q Q³/2)。
粗单调耦合速率 E|X−Z|²≤Cd^−1/6 已足以控制标量位移除以 σ 后的误差。
所有精确非中心项及尾部确定截距均保留，原完整二项计数向量始终附在联合通道上。
只有标量位移支付 σ^−1，完整选定后验的多项式 TV 误差由核收缩进入，不乘该因子。

Friedrich Götze、Alexey Naumov、Vladimir Spokoiny、Vladimir Ulyanov，
*Large ball probabilities, Gaussian comparison and anti-concentration*，
原版本 [arXiv:1708.08663v2](https://arxiv.org/abs/1708.08663v2)，2018-03-07，27 页 PDF。
式 (2.1)（PDF 第 10 页）以协方差特征值 λ_j、尾平方和 Λ_k² 定义分段量 κ(Σ)。
定理 2.6（第 13 页）对中心 Gaussian Hilbert 空间元 ξ 和任意确定平移 a，
给 ||ξ−a||² 的密度上界 Cκ(Σ)；定理 2.7 给对应区间反集中界。
第 15–16 页证明使用卷积收缩及式 (3.2) 的非中心平方特征函数模。

该原定理直接覆盖第 75 章参考密度步骤。
在固定中心小核心取 ξ_j=√w_j Z_j、a_j=√w_j c_j，
其中 w_j 与 √δ 同阶，组数与 δ^−1 同阶。
于是 Σ=diag(w_j) 的平方 Frobenius 范数有正下界，而最大特征值平方为 O(δ)；
最终 3λ_1²≤Λ_1²，κ(Σ)=Λ_1^−1 有界。
独立其余平方项及测量噪声的卷积保持密度上界。
正文短特征函数证明仅明确所需一致性与非中心项，不将这个通用密度界申报为新定理。
原文不提供实际行占据数、固定 q 后验或本模型指数小噪声下的通道比较。

Andrew Carter、David Pollard，*Tusnády’s inequality revisited*，
Annals of Statistics 32(6), 2731–2741 (2004)，DOI 10.1214/009053604000000733；
核对的原电子重印本为 [arXiv:math/0508606v1](https://arxiv.org/abs/math/0508606v1)，
2005-08-30，12 页 PDF。重印本注明分页与原印本不同。
第 1–2 页定义 Bin(n,1/2) 与 N(n/2,n/4) 的单调耦合。
定理 1（第 3–4 页）在 n≥28、n/2<k≤n−1 下给上尾近似；
定理 2（第 4 页）控制相应正态分位切点，第 5 页讨论耦合后果。
该文也明确 KMT、Hungarian 与 Tusnády 的经典谱系。

本库校准 p 随数据变化，并非严格 1/2，故不把上述对称结论原样当作任意 p 的一致估计。
第 67、75 章使用方差型局部 Bernoulli 界、单调层饼恒等式、四阶矩与插值，
得到足够的非最优 d^−1/6 平方误差。耦合机制本身是经典内容；
新增用途是原移动核心的实际指数大方差使该粗速率仍能支付指数小噪声。
没有未平滑离散／连续 TV 近似，也没有整个过程的 KMT 耦合主张。

Yury Polyanskiy、Yihong Wu，*Wasserstein continuity of entropy and outer bounds for interference channels*，
原版本 [arXiv:1504.04419v2](https://arxiv.org/abs/1504.04419v2)，
版本戳 2016-02-02、标题日期 2016-02-03，22 页 PDF。
第 3 页的正则密度定义要求 ||∇log p(x)||≤c_1||x||+c_2；
命题 1 在二阶矩与该正则性下以二阶 Wasserstein 距离控制熵及密度比量。
第 4 页命题 2 对独立 Gaussian 平滑 B+Z、E||B||<∞ 给正则常数，
其中 c_1=3 log e/σ²、c_2=4 log e E||B||/σ²。
第 5 页推论 4 的熵／互信息比较保留 σ^−2 量级因子与所列矩条件。
第 2 页反例也说明小散度本身不足以保证微分熵接近。

这些条件是本章边界核查，未充当证明前提。
普通 o(1) TV 不能自动提供其 Wasserstein 精度或控制随噪声退化的常数。
第 75 章改用实际密度集合：{f_x>exp(bQ)} 的 Lebesgue 测度至多 exp(−bQ)，
由有界参考密度与 TV 控制其实际概率；低密度事件由实际二阶矩与空间截断控制。
因此 |ln f_x(Y)|=o_P(Q)，再用精确信息密度恒等式得到所需概率增益。
这个论证不推出密度上确界或熵的一致可积性。

第 71、73 章已核对的 Kontoyiannis–Verdú、Gavalakis–Kontoyiannis、
Kuzuoka–Watanabe 保留其有限信息阈值、后验排序及各自条件／一般源假设。
典型输出结论还使用第 73 章在整个 ln⁺(1/σ)=o(Q³) 范围的原惊奇量条件 CDF 定理，
不能从边缘 CLT 与少量信息单独推得。
本章的有限输入／实输出 Bayes 核、阈值界及可测选择直接按原实验证明。

有界置换不变事件通过原支持对称移到实际确定支持的联合数据／输出律；
先验预测混合密度仍不等于固定支持给定数据后的真实单个 Gaussian 密度。
第 72 章确定中心的 o_P(Q) 精度可继承，Q⁵ 主项不能单独承担该中心。
没有实际无界矩转移、每个输出保证、期望覆盖展开、零噪声或 Q³ 必要阈值结论。
所核对经典原文直接承担其抽象步骤，未找到直接提供这套实际后验／移动核心连接的完整原定理；
有限检索及接口失败均不构成全球原创性认证。

## 临界规范测度、packing 类别与固定分母同步（第 76 章）

`repo-derived`：第 76 章在原实际熵例外集上给完整规范零／无穷律，
其级数为 Σ Q_n² f(Q_n^−3)，规范满足 f 递增、f(t)/t 非增且在零处趋无穷。
因此每个非空开参数区间的 H^(2/3) 测度无穷，packing 维数为 1；
正对数修正 t^(2/3)/(ln(1/t))^a、a>0 的测度却为零。
类别／packing 推导使用稠密 Gδ 子集，单纯稠密不足以推出该结论。

Beresnevich–Dickinson–Velani 的原文
[arXiv:math/0401118v3](https://arxiv.org/abs/math/0401118v3)，
*Measure theoretic laws for lim sup sets*，主 Hausdorff 定理（TeX 标签 THM3）
直接承担规范测度的发散侧。除第 74 章已经使用的 G>0 分支外，
第 (i) 项在 G=0 时还允许：ρ 对块上端点 u 正则，且 Σ g(u_n)=∞。
该正则性定义为 ρ(u_(n+1))≤cρ(u_n) 最终成立于某个固定 c<1。
它不要求 g(u_n) 单调，也不另要求规范沿 n 满足对数正则性。

映射为紧 Euclidean 参数区间、Lebesgue 测度、M2 指数 d=1、点共振 γ=0，
原正根 floor 区间中点的权重 Q_n，块 (Q_(n−1),Q_n]，
ρ(t)=At^−2、ψ(t)=κt^−3。原网格最大间隙给逐块局部覆盖，
原目标小球完整处于实际均值有正有限界的 floor 区间内。
超稀疏原序列给 ρ(Q_(n+1))/ρ(Q_n)→0。
因此两个分支覆盖全部发散级数情形；收敛侧由完整 E 的直径覆盖直接证明。
这是经典度量定理在实际网格上的应用，不申报独立新规范定理。

同步集合 E2 要求同一固定 beta、同一合法子序列上的正、负两组实际均值均趋于正有限值。
第 76 章保留共同整数 L，使 L ln2+lnχ_j 与 L ln2+lnχ_k 同时有界，
并将精确阶乘比化为固定分母 N=Q² 的曲线条件
|k−NΨ(j/N)|≤C N^−1/2。
两个 Stirling 展开中的 lnλ 前因子抵消，剩余原初始计数 floor 的光滑修正仍保留。
根交换曲线的曲率不是未经核对的假设：解析展开证明其不恒零，
内部零点因而孤立，参数例外至多可数。

Jing-Jing Huang，*Rational points near planar curves and Diophantine approximation*，
原版本 [arXiv:1403.7388v1](https://arxiv.org/abs/1403.7388v1)。
正文原定义的曲率类要求固定紧区间上的 C² 函数与 0<c1≤|f″|≤c2。
第一定理和第六定理（TeX 标签 t1、t6）另要求二阶导数 Lipschitz。
第六定理计数的是所有 1≤q≤R 的和：
N_f(R,η)=Σ_(q≤R) #{a:a/q∈I, ||qf(a/q)||<η}，
并在 0<η≤1/2、整数 R>1 下给
|I|ηR²+O(η^(1/2)log(1/η)R^(3/2)+R^(1+ε))。
原始互素版本带 1/ζ(3) 系数；第二定理对曲率类的一致闭包给较弱的 R^(4/3) 误差项。
常数范围含区间、曲率界及所列 Lipschitz／ε 条件。

本库曲线在局部满足这些光滑性要求，但所需分母固定为 Q_n²，不能换成所有 q≤R。
在 η=N^−1/2 尺度，累计误差项含 N^(5/4)log N，
大于单个分母预期的 N^(1/2) 主增量；取相邻 R 的差并不能得到正下界。
原文也没有给本库的同阶前因子平移、共享 M-floor 整数交集或稀疏层嵌套。
本章实际使用经典二阶导数指数和界与非负 Fejér 核，在固定分母上直接得 O(N^(2/3)) 上计数，
再以原 floor 宽 Q^−3 得 dim_H E2≤4/9。
抽象指数和估计不是新内容；新增连接是原双根均值到该固定分母、精度和 floor 条件的归约。

同作者的 [arXiv:1403.8038v1](https://arxiv.org/abs/1403.8038v1)，
*Hausdorff theory of dual approximation on planar curves*，是另一篇原文。
其主定理处理整数向量的对偶不等式与递减逼近函数，曲线在零 H^s 集之外非退化；
其 Huxley 计数引理按整个分母块求和。没有未经证明的对偶／同步迁移可把它用于本库固定分母下界。
该版本所印 Hausdorff–Cantelli 引理将 |H_i| 称为高维体积却使用 Σ|H_i|^s，
字面高维表述的指数与直径不匹配；正文使用直径覆盖，未采用这一印刷表述。
这项局部警示不裁决该文主定理或其它版本。

Claude Tricot Jr.，*Two definitions of fractional dimension*，
Mathematical Proceedings of the Cambridge Philosophical Society (1982)，
DOI [10.1017/S0305004100059119](https://doi.org/10.1017/S0305004100059119)，
为 packing／维数框架的经典来源。此处取得了出版元数据，未取得通过 PDF 身份核验的原文；
Taylor–Tricot 原文路线也返回访问拒绝，故不冒称其具体原定理已核对。
第 76 章从 packing 外测度的可数覆盖定义直接证明所需类别推论，未依赖未读原定理或上 box 维数替代。

E2 的上界使其 H^(2/3) 测度为零，而实际正根目标 limsup 的该测度无穷，
因此在两根区域仍得到大量只留下单 Poisson 熵项的固定参数。
这不证明同步双 Poisson 实例存在，不推出 dim_H E2=1/3，
不把两个边缘稠密／余贫事件的交集当作同层同步命中。
所有实际均值、精确中心和概率范围沿用第 72、74 章；参数测度不充当新实验先验。
有限原文核对未关闭固定分母同步可达性；接口失败及不同分母范围都保留，
未给全球原创性、期望熵或计算效率认证。

## 低噪声平均信息的常数项与熵连续性（第 77 章）

`repo-derived`：第 77 章保持原完整计数目标、精确后验中心及 Gaussian 标量通道。
在 L=ln(1/σ)→∞、L=o(Q³) 的整个确定序列范围内，实际输出密度的上确界在原数据概率下有界，
且其 L¹ 距离收敛到方差 2g₀ 的中心 Gaussian 密度。
实际纤维二阶矩与这两个密度控制共同给微分熵的常数极限，进而
I_x=L+½ln(2g₀)+o_P(1)，平均输出后验 Shannon 熵为精确 h_x−I_x/ln2。
外层收敛一致于确定支持，两种实际平稳实验分别成立。
这些平均量均在指定先验纤维内定义，不是点质量支持先验下的信息，也不是全原始数据期望。

Hamid Ghourchian、Amin Gohari、Arash Amini，
*Existence and Continuity of Differential Entropy for a Class of Distributions*，
核对原版本 [arXiv:1703.09518v1](https://arxiv.org/abs/1703.09518v1)，
2017-03-28，4 页 PDF；DOI 10.1109/LCOMM.2017.2689770。
定义 3（PDF 第 2 页）规定 (α,v,m)–AC_n 类：绝对连续、α 阶绝对矩严格小于 v，
且密度本质上确界严格小于 m。
同页定理 1 给熵存在性，并在 d=||p−q||₁≤m 时给
|h(p)−h(q)|≤c₁d+c₂d ln(1/d)，c₁,c₂ 由上述固定类参数控制。
文中称此 L¹ 距离为 total variation，使用时不与半 L¹ 约定混用。
第 3–4 页 IV.A–B 给存在性与连续性证明。

该定理直接覆盖本章通用熵连续性步骤。
取 n=1、α=2，先在实际数据的高概率事件固定密度界 B 和二阶矩界 K，
稍放大参数以满足严格不等式，并将 Gaussian 极限纳入同一类。
实际 L¹ 收敛给定理所需距离；最后令外层失败容差趋零。
正文 (77.16)–(77.17) 给出所需一维尾部和紧区间证明，
用于明确随机环境量词及实际矩的作用，不将这个连续性原理申报为新内容。
弱收敛与密度有界不足以排除密度振荡；L¹ 收敛本身也不足以承担熵尾控制。

Simon Becker、Nilanjana Datta、Michael G. Jabbour，
*From Classical to Quantum: Uniform Continuity bounds on entropies in Infinite Dimensions*，
核对原版本 [arXiv:2104.02019v3](https://arxiv.org/abs/2104.02019v3)，
2024-11-19，18 页 PDF；期刊 DOI 10.1109/TIT.2023.3248228。
PDF 第 6–7 页定理 3 针对非负整数上的均值约束 Shannon 熵，不能直接套给连续密度。
与本章直接相关的是第 11 页命题 III.5：
对 D 上密度 p,q、有界密度取值范围上的 α-Hölder 函数 F、正权 w，
若 β<α、w^(−β/(1−α)) 可积、wp,wq 可积，则
||F(p)−F(q)||₁≤|F|_{C^α}||p−q||_{L¹(w)}^β
||p−q||₁^(α−β)(∫w^(−β/(1−α)))^(1−α)。

在固定密度界 B 下，取 F(t)=−t ln t、α=3/4、β=1/2、w(y)=1+y²，
则 ||p−q||_{L¹(w)}≤2+2K，且 ∫(1+y²)^−2dy 有限。
故该命题也直接提供 C_B(2+2K)^½||p−q||₁^¼ 的熵连续模。
其连续密度讨论以参考文献 [29] 引用 Ghourchian–Gohari–Amini。
第 2 页修订注记 Remark 1 说明定理 2、4、6 的能量阈值须加限制，
并指向后续全范围结果；本章不使用这些定理，也不把 v3 当作未经改变的旧版。
这里采用命题 III.5 的具体加权假设，不借用任意量子熵或 Rényi 参数极限。

Murali Godavarti、Alfred Hero，*Convergence of Differential Entropies*，
IEEE Transactions on Information Theory 50(1), 171–176 (2004)，
DOI 10.1109/TIT.2003.821979，是上述 2017 原文的参考文献 [8]。
书目信息已核对；IEEE 原文路线返回 HTTP 418，另一路元数据没有开放 PDF。
因此未核对其原定理假设，不以二手摘要承担本章的连续性前提。

第 75 章核对的 Polyanskiy–Wu 原版本 arXiv:1504.04419v2，
命题 1–2 与推论 4 保留二阶矩、正则密度和随 σ^−2 退化的常数。
这些经典 Gaussian 平滑结果说明必须支付真实噪声尺度的代价。
本章直接使用 Gaussian 核的导数范数：上确界为 e^−½/(√(2π)σ²)，L¹ 范数为 √(2/π)/σ。
先对保留全部精确非中心项与尾部截距的乘积标量耦合证明 D_M/σ²→0，
再由完整选定密度 L_x≤1+η_x 得 f_x≤(1+η_x)f_x^{prod}。
实际后验的多项式 L²/TV 误差不除以 σ 或 σ²，故没有以无界放大偷换核收缩。

Götze–Naumov–Spokoiny–Ulyanov 原版本 arXiv:1708.08663v2 定理 2.6
直接承担含任意非中心项的参考 Gaussian 二次型密度界，具体参数对应见第 75 章归属。
第 77 章另以实际平方质量和 δ^−1Σv_j²→g₀、最大权趋零及一致可积的特征函数，
证明该参考密度的 L¹ Gaussian 极限；不由对角弱 CLT 单独推出局部密度结论。
Carter–Pollard 的对称二项强耦合原文仍只作为经典谱系：
实际校准 p_j 非严格 1/2，正文使用第 67、75 章已给的粗一致分位估计。
固定总和条件化属于经典 rejective sampling；其完整向量密度式的本模型估计
仍不能由固定阶 inclusion 展开替代。

有限输入 Gaussian 通道的 I=h(Y)−h(σG)、有限 Bayes 熵链式公式、
Fourier 反演、卷积收缩及 Scheffé 密度论证均为经典步骤。
新内容的范围是上述条件在原实际行占据、精确固定 q 后验及整个 L=o(Q³) 范围的同时实现。
输出后验熵的输出平均与典型输出 CDF／列表定理是不同结论；
没有由前者推出每个输出的常数精度熵集中或期望对数覆盖。
没有全数据无界期望转移、零噪声结果、Q³ 必要阈值、向量／适应性通道或计算效率结论。
所查原文直接覆盖各通用工具；有界检索未找到完整实际模型连接的直接前例，
这不是全球原创性、优先权、正式发表或 Lean 真值认证。

## 通用正 Poisson 均值、精确相位与参数集维数（第 78 章）

`repo-derived`：第 78 章构造同一个稠密 Gδ 参数集 U₀。
其中每个固定 β 都能沿原合法规模子序列实现每个实 θ>0 的正根实际占据均值，
并能在正整数目标处选择严格从上／下侧趋近。
同一参数、层数和计数线索引同时给两种实际实验的确定均值极限；
不同实验的原始数据并未因此被耦合。
U₀ 及完整通用集 U 在每个参数开区间的 Hausdorff 维数均为 2/3，
Lebesgue 测度为零、类别为余贫，局部 packing 维数为一。

新增解析输入是 β 无关的精确阶乘相位 Φ_Q(j)=log₂χ_{Q,j}。
对其 Gamma 延伸求导，在固定正根紧区间严格得到 −Φ_Q″ 与 Q⁻¹ 同阶；
不对粗 Stirling 式的未知余项求导，也不丢弃原 k₀,l₀,P。
经典指数和估计随后给任何固定圆弧在长索引区间内的正比例下计数。
这些索引各选择原 M-floor 区间；内带余量及实际相对误差使两个实际均值
在整个原区间上进入目标带，保留 q 的取整、补偿与完整得分组。

Hermann Weyl，*Über die Gleichverteilung von Zahlen mod. Eins*，
Mathematische Annalen 77 (1916), 313–352，DOI 10.1007/BF01475864。
核对的原始 40 页扫描来自
[Zenodo 原文](https://zenodo.org/api/records/2425535/files/article.pdf/content)。
印刷第 313–315 页给均匀分布定义、Riemann 可积测试函数与三角多项式夹逼。
Satz 1（第 315 页）要求一个序列的前 n 项对每个非零整数频率的指数和均为 o(n)，
由此推出模一均匀分布。
扫描文本有历史字体 OCR 错误；使用的是可辨读的量词与夹逼论证，
正文的有限相位估计及公式独立写全。

Weyl 原判据直接说明这里的经典解析机制，但本章的数组随 Q 与索引区间改变，
未把它们当作同一无限序列的前缀。
正文先选支撑于目标弧的连续非负函数，再取固定阶 Fejér 多项式 P，
使 P−ε 成为真正的下小函数；对有限个非零频率使用二阶导数检验，
得到 p_A N−C_A(N/√Q+√Q) 的计数下界。
每个合法 Q 上的横向分布也不自动证明固定 β 沿超稀疏层数的点态分布。
后者由原区间命中、Baire 交及确定嵌套构造承担。

Jing-Jing Huang，*Rational points near planar curves and Diophantine approximation*，
原版本 [arXiv:1403.7388v1](https://arxiv.org/abs/1403.7388v1)，
核对 PDF 与 [原 TeX](https://arxiv.org/e-print/1403.7388v1)。
Theorem 3 证明开头的 Lemma 1（源码标签 l1）针对任意有限实数序列 u₁,…,u_N，
定义弧 (α,β) 的 discrepancy D=N_hit−(β−α)N，且 β−α<1。
对任意正整数 K，其绝对误差满足
|D|≤N/(K+1)+2Σ_{k≤K}[1/(K+1)+min(β−α,1/(πk))]|Σ_ne(ku_n)|。
原文将证明归于 Montgomery 第 1 章，并讨论 Fejér 与精细 Fourier 权重的差别。

该有限序列不等式直接覆盖本章所需的上下区间计数。
固定弧后先取 K 大，再用有限频率指数和估计，即得所需下界。
该文主定理按不超过 Q 的分母平均；本章没有拿它们替代每个指定合法分母上的下计数，
也不据此声称双根同步可达。
原文不提供本库的完整后验、实际依赖路径占据或 M/q-floor 对应。

Karl-Goswin Grosse-Erdmann，*Universal families and hypercyclic operators*，
Bulletin of the AMS 36 (1999), 345–381，DOI 10.1090/S0273-0979-99-00788-0。
定向检索核对了书目，出版社 PDF 返回 HTTP 403；独立机构库链接重定向到申请表 HTML。
未核对其原定理假设，也未发送获取文件的请求。
因此不把未读的连续通用族定理直接套给本章分段常值且有跳跃的精确均值映射。
正文通过每个目标带的原开放区间直接证明稠密 Gδ，包含从可数基到所有实目标的递增层选择。
这个 Baire 机制是经典内容，不申报为新原理。

维数下界使用经典质量分布法，但必须补上筛选后网格的实际条件。
固定带只给长区间内下计数与最小间距，没有证明 Q⁻² 最大空隙。
正文允许第 s 个带的密度常数 a_s 任意趋零，并在选择本层前纳入已知下一常数 a_{s+1}。
由此同时控制柱集质量 M_s≤C_dℓ_s^d 与父质量
M_{s−1}≤C_d(a_sℓ_{s−1})^d，覆盖所有中间尺度。
这一步不能用只在柱集宽度上的估计替代。
临界 d=2/3 时负主项消失，正文没有宣称临界 Hausdorff 测度已确定。

第 76 章已核对的 Beresnevich–Dickinson–Velani 原版本 math/0401118v3，
THM3 保留 Ahlfors 球测度、局部 ubiquity、交叠指数、规范单调性，
以及相应的 G>0 或 G=0 加发散／u-regular 条件。
它对一个满足条件的 limsup 集给测度结论，不能自动升级为不同窄均值带的可数交。
Beresnevich–Velani 质量转移也不能省去扩大球的全测度前提。
本章采用直接构造证明维数，不声称这些未核实的交集前提已具备。
较大 E 的临界无穷测度不沿包含关系传到 U；收敛规范的零测度可以传递。

两根区域中，已有 dim_H E₂≤4/9 允许从 U₀ 删除 E₂ 后仍保留局部维数 2/3。
这只给维数结论，不给类别结论，因为小维数不蕴含贫性。
在所得参数上，第 72 章的实际过渡组 Poisson 定理给所有非整数 θ 的
b(P_θ)−b(floor θ) 及整数 m 的两种单侧 floor 熵极限。
整个 U₀ 上的右根通用性仍可能伴随左侧项；E₂ 非空性、锐利维数及同步指定均值仍未解决。
指定 β_* 是否通用亦未判定。

原文检索保留 Weyl 出版社 HTML、缺少 pdftotext 后的成功 PDF 提取替代，
Crossref HTTP 429 及通用族原文不可得的边界；未重复未变的失败接口。
经典原文直接覆盖各抽象步骤；所核查范围未找到完整原 floor／实际均值通用构造的直接前例，
不据此认证全球原创性。统计结论为固定参数后的实际弱极限及支持上一致的概率结论，
不含参数先验、全数据熵期望、无界矩、解码或有限精度恢复主张。

## 第 79 章归属：Gaussian 信息密度、乘积正态与条件核转移

第 79 章研究同一真实计数／测量实现的信息密度 i_x(R,Y)，
在 L=ln(1/σ)→∞、L=o(Q³) 下证明 i_x−L 的常数量级联合极限及全部固定信息矩。
目标分布 c+(Z²−G²)/2 本身是经典 Gaussian 信息密度的低噪声极限；
实际离散固定 q 后验、原路径行依赖和最终噪声尺度的连接须另行证明。

Jonathan Huffmann、Martin Mittelbach，
*On the Distribution of the Information Density of Gaussian Random Vectors: Explicit Formulas and Tight Approximations*，
核对原版本 [arXiv:2105.03925v3](https://arxiv.org/abs/2105.03925v3)，
2021-11-04。后续期刊书目信息为 Entropy 24(7), 924 (2022)，
DOI 10.3390/e24070924；出版商 PDF 路线返回 HTTP 403，未据此声称与 arXiv v3 逐字相同。
PDF 第 2–3 页的设置是联合 Gaussian 实向量、非奇异边缘协方差与正典型相关系数。
式 (1)–(2) 把信息密度写成均值加独立半正态平方差的加权和；
第 4 页定理 3 给全部整数中心矩，第 7 页给单个典型相关系数的化简，
第 12 页引理 1 给中心信息特征函数 Π_j(1+ρ_j²t²)^−½。

对严格正噪声的 Gaussian 输入 T₀∼N(0,ν)、Y₀=T₀+σG，
ρ_σ=√[ν/(ν+σ²)]、I_σ=½ln(1+ν/σ²)，该原文直接给
(i_σ−I_σ) 的分布等于 ρ_σUV，其中 U,V 为独立标准正态。
因此本章极限标量形状及矩公式不是新结果。
该分布等式不自动识别与原测量残差 G 的联合关系，
也不把原实际后验变为 Gaussian 输入。
原文将正典型相关表示归于 Pinsker 等早期来源；未独立取得那些原文，
故此处仅转述作者的历史归属，不把未核对书页作为额外定理前提。

Robert E. Gaunt，*A note on the distribution of the product of zero mean correlated normal random variables*，
核对原版本 [arXiv:1807.03981v1](https://arxiv.org/abs/1807.03981v1)，2018-07-11。
PDF 第 3 页定理 3.1 假设零均值二元正态、正方差及非退化相关系数，
识别乘积为该文参数化的 variance-gamma 分布。
相关系数为零、两方差为一时，密度为 K₀(|z|)/π；
第 2–3 页的独立正态表示直接覆盖本章的乘积识别。
正文只需正交旋转与条件 Gaussian 积分，即得特征函数 (1+t²)^−½、
偶矩 [(2m−1)!!]² 和绝对矩 2^pΓ((p+1)/2)²/π。
方差 1 与四阶中心矩 9 指随机输入信息密度，不能混同有功率约束 Gaussian 编码的操作色散。
Craig 1936 原论文 DOI 10.1214/aoms/1177732541 的书目信息已定位，
ProjectEuclid 路线返回 HTML 而非 PDF，未核对其原定理条件，不据此主张历史优先权。

第 77 章已核对的 Becker–Datta–Jabbour 原版本
[arXiv:2104.02019v3](https://arxiv.org/abs/2104.02019v3)
PDF 第 11 页命题 III.5 还有直接相关的范围。
其条件为密度值域上的 α-Hölder 函数 F、β<α 的正权
w 满足 w^(−β/(1−α)) 可积，以及加权密度可积。
每个固定整数 k 的 F_k(t)=t(ln t)^k 在 t=0 连续补零后，
在有界密度值域上属于任意 α<1 的 Hölder 类。
取 α=3/4、β=1/2、w(y)=1+y²，便从共同密度上界、二阶矩上界和 L¹ 收敛
直接获得各自对数密度矩的连续性，包括相应的标量微分 varentropy。
所以这类通用矩连续性也不作为新原则。
其假设本身不保留测量残差，不能单靠边缘连续性推导 G² 与 ln f_x(Y) 的交叉矩。

正文为实际矩转移给出独立可核对的尾界：若 ||f||∞≤B、E Y²≤K，
则 P{−ln f(Y)>r}≤(2+K)e^(−2r/3)，由区间长度与二阶矩 Markov 界得到。
它与精确 Gaussian 残差矩共同控制全部固定阶信息矩；
异常原数据仅以概率排除，不把无界量乘其失败概率。
对数密度替换使用实际输出加权的
P_f{|ln(f/p)|>u}≤||f−p||₁/(1−e^(−u))，不要求全域密度比一致收敛。

典型输出结论还用第 75、77 章保留完整计数向量的分位耦合。
先比较实际 (R,Y) 与参考 (R,T^G+σG₀)，付出 a_x/2+D_M/(√(2π)σ)，
再比较参考连续残差／输出的联合密度，最后以条件核三角不等式和位移界传回实际残差 CDF。
这里分母 σ 仅作用于已证指数精度的标量位移，不作用于多项式后验 TV 误差。
有限纤维给定输出后的实际残差仍为离散分布，与标准正态的 TV 距离恰为 1；
所证对象是先验预测输出加权的条件 Kolmogorov 距离。
这些条件核与平移不等式是经典步骤，原实际模型的共同实现与精度条件是本章承担的连接。

未增加逐输出后验 Shannon 熵集中、全原数据无界矩、任意 T/Y 高阶混合矩、
实际指数矩、零噪声或 Q³ 边界定理；原精确熵中心和方向范围不变。
所核对原文直接覆盖通用分布与连续性工具；有界检索未给出完整实际连接的直接前例，
不构成全球原创性、形式验证或正式发表认证。

## 第 80 章归属：多层质量构造与可数交集的临界测度

第 80 章固定第 78 章已有的均值带、内带、原 floor 中三分之一区间与通用集合，
证明每个非空参数开区间内 H^(2/3)(U₀)=H^(2/3)(U)=∞。
这不由维数等于 2/3、更大 E 集的临界无穷测度，或每个单带 limsup 的无穷测度推出。

V. Beresnevich、S. Velani，
*A Mass Transference Principle and the Duffin–Schaeffer conjecture for Hausdorff measures*，
沿用并核对原版本 [arXiv:math/0412141v1](https://arxiv.org/abs/math/0412141v1)。
原 TeX 的定理标签 thm3 假设球半径趋零、规范与环境体积之比单调，
以及相应放大球 limsup 在每个球内具有满 Lebesgue 测度，
推出原目标球 limsup 的 Hausdorff 规范测度结论。
它是单个 limsup 的定理，不直接断言当前可数带交集的临界测度。

其原证明明确固定任意大参数 η，构造携带 μ(A)≲f(A)/η 的紧子集，
再令 η 增大得到无穷测度。原构造 P0–P5 使用局部子层、两两不交的三倍目标球、
每子层固定的放大体积下界、层间递减的单球规范体积，以及足够多子层的累积。
任意球估计按第一次触及两个子球的树层分类。
第 80 章使用这一经典机制，不把多层构造或任意小 Frostman 常数作为新方法。

本模型需核对的额外连接是：引理 78.3 在每个已固定有限开集上的下计数，
保证删除早层五倍区间后仍可选更晚的原合法层；
每层子区间总普通长度为 O(r/Q)，总临界内容却至少为 η_B r。
每个父区间可取任意有限多层，使临界内容增加而普通长度仍小。
固定均值带序列的 η_k 可以任意趋零，构造提前在父质量中支付下一带 η_(k+1)，
从而任意区间估计中的 1/η_k 被消去。
层内上计数 C(1+tQ²) 与跨层几何衰减给 C(t^(2/3)+mt)，
不借用筛选中点网格尚未证明的最大空隙界。

第 76 章核对的 Beresnevich–Dickinson–Velani，
*Measure theoretic laws for lim sup sets*，
[arXiv:math/0401118v3](https://arxiv.org/abs/math/0401118v3)，原 TeX 定理 THM3，
也直接覆盖每个单带的临界结论。
这里环境指数为 1、点共振交叠指数为 0，放大半径约 Q^−2、目标半径约 Q^−3，
f(t)=t^(2/3) 给其 g(Q) 正常数。固定带的正比例下计数和分离使放大球局部占据正比例，
正是局部 ubiquity；不要求每层覆盖整个区间。
原定理的 G>0 分支给单带无穷测度，仍不替代本章交集证明。

Arnaud Durand，*Sets with large intersection and ubiquity*，
Math. Proc. Cambridge Philos. Soc. 144 (2008), 119–144，
DOI 10.1017/S0305004107000746。
核对[作者托管原稿](https://www.imo.universite-paris-saclay.fr/~arnaud.durand/files/sets_with_large_intersection_and_ubiquity.pdf)
的定义及定理 1、2。取得版本是 26 页、带 “Under consideration for publication”
页眉且 received 日期空白的作者稿；没有把它标作期刊版逐字副本。
其 D_d 规范类要求 h(r)/r^d 近零正且非增，关系 g≺h 表示 g/h 单调趋于无穷。
G^h(V) 的定义要求对每个这样的严格更大 g，在开放子集上有满外 net 测度。
定理 1 给可数交稳定性、双 Lipschitz 原像稳定性，以及 g≺h 时 H^g 无穷；
不能取 g=h。

其定理 2 要求近似球族半径有界、每个有界区间内超过任意固定半径阈值的球只有有限多个，
并且原球 limsup 局部满 Lebesgue 测度；以 h^(1/d) 的近零伪逆缩球后得到 G^h(V) 成员身份。
第 78 章固定带放大球的正比例下界，在每个固定区间成立，
用 limsup 的测度下界和 Lebesgue 密度定理可推出满测度。
因此这些经典 large-intersection 条件可以核对，但交集性质仍只给严格规范的结论，
不能省略第 80 章的临界构造。
Falconer 1994 原论文 DOI 10.1112/jlms/49.2.267 的书目信息已定位，
出版商原 PDF 返回 HTTP 403；不以未读原文中的端点表述承担证明。

对数规范 a>0 的零测度来自更大 E 的原层覆盖，
因为 Σ_n(ln Q_n)^−a 收敛；a=0 由新临界构造，a<0 由规范比较。
E₂ 的维数上界 4/9 只用来删除临界零测度部分，未用来推断类别或非空性。
实际 Poisson 熵子序列律保持原统计证明、精确中心与概率量词，未由参数测度构造引入新先验。
这里的新增综合是经典多层方法在原精确均值带交集上的完整适用性与所有尺度估计，
不主张新质量传递原理、任意规范发散律、全球原创性或形式验证。

## 第 81 章归属：精确 Gamma 曲线的同步单元与固定分母边界

第 81 章在原双根模型上证明负根交换处处严格凸、精确 Gamma 等系数曲线具有相同曲率，
并在每个固定内部参数区间、每个充分大的原合法层构造共享一个整数规模 floor 的双根单元。
实际双均值的正有限上下界允许依赖区间；结论没有被升级为固定参数的无限次同步。
固定参数的双相位判据保留 3 ln Q、计数 floor 和共同规模 floor，
给出有理根参数的排除及有理切线截距的必要条件。

Gamma 的 polygamma 级数、Binet 余项与平滑 Stirling 展开是经典工具。
递减曲率势函数的等值支求导、有理切线后的格点同余采样、紧嵌套和子序列抽取
也不作为新的一般方法。新增综合是它们对原精确系数、两种实际实验的相对均值桥、
同一个整数规模及完整窗口的共同适用；归属为 repo-derived。
以下原文比较没有发现直接给出完整模型结论的定理，不构成全球原创性证明。

Victor Beresnevich、Evgeniy Zorin，
*Explicit bounds for rational points near planar curves and metric Diophantine approximation*，
[arXiv:1002.2803v1](https://arxiv.org/abs/1002.2803v1)。
原 TeX 的 t:01、t:02 采用曲率绝对值介于两个正数之间的 C² 曲线类及其一致闭包。
计数 N_f(R,δ,J) 包含所有 0<q≤R 的既约有理点，垂直误差至多 δ/R。
局部下界要求 |J|≤1/2、δ≤1、δR²|J|≥8C₁、Rδ≥C₂，
并满足其显式的 R 与 |J|、δ 的附加关系；结论为至少 δR²|J|/(4C₁) 个点。
覆盖定理使用 c₀R<q≤R 的整个分母块，半径 C₁/(δR²)，覆盖 J 的至少一半。
本模型在紧根区间满足曲率条件，R=N=Q²、δ 与 N^−1/2 同阶也满足固定 J 的尺度条件。
但这些定理不将分母固定为 N；没有 q|N 的保证，清分母或取整不能保留 N^−3/2 的精度。
原引言一处 δ>Q^(2/3) 与相邻 δ<1/2 的范围不相容，未用该未参与证明的字面比较。

Damaris Schindler、Rajula Srivastava、Niclas Technau，
*Rational Points Near Manifolds, Homogeneous Dynamics, and Oscillatory Integrals*，
[arXiv:2310.03867v1](https://arxiv.org/abs/2310.03867v1)。
原 Lower Bounds 定理要求 l-nondegeneracy、至少 ceil((n+1)/η) 阶光滑性、
0<η≤1/8，且 δ>R^(−3/(2n−1)+a_nη)，a_n=(2n+12)/(2n−1)。
其主项为 c_t δ^m R^(d+1)，误差具有正的幂次节省。
平面曲线 n=2、d=m=1，固定充分小 η 时，本模型满足光滑性、非退化及所需 δ 范围。
然而原平滑计数带有支撑于 [1/2,1] 的固定权重 ω(q/R)，仍对分母求和。
将权重缩至单个 q=N 会改变其导数控制；该定理未给这种变动权重的一致结论。

Alexander Smith，*Lattice points in thickened parabolas and rational points near hypersurfaces*，
[arXiv:2512.00202v1](https://arxiv.org/abs/2512.00202v1)。
原 intro.tex 的 thm:hypersurface_qual、thm:planarcurves、thm:main
讨论有界分母的有理点及有理二次曲面障碍，未固定分母为原 Q_n²。
thm:parabola 则要求 SL_n(R) 的一参数幂零流满足 rank(u−Id)=2、(u−Id)²≠0，
并且不保留任何非零有理二次型，才断言每个非空开放加厚区域含无穷格点。
DaMa.tex 的一致版本使用这一可用生成元类的紧子集与固定正横向厚度；
其几何表述引入 T₀ 后未在相应位置写 T>T₀，函数版本明确保留该限制。

直接将平面仿射抛物线嵌入三维的流
U_t(x,y,z)=(x+tz,y+2κtx+(κt²+ℓt)z,z) 保留非零整数二次型 z²，
所以不满足上述假设；固定 z=N 也不是开放横截面。
保格点线性共轭保留“存在有理不变二次型”这一障碍。
这排除该直接套用方式，不证明原同步集为空，也不否定其它可能的迁移方式。

Yanqiu Guo、Michael Ilyin，*Sparse distribution of lattice points in annular regions*，
[arXiv:2309.10971v1](https://arxiv.org/abs/2309.10971v1)。
原 thm2D 对 0<s<1/4、d>0 给任意大的 λ 及 κ≥Cλ^s，
使 λ≤|x|²≤λ+κ 内任意两格点距离大于 d。
紧接的注释明确允许零点、一个点或多个点，因此这不是空环带结论。
其径向位置可选择、曲线为圆，不给原指定 Q_n² 上等系数曲线的无点结论。

第 76 章已有 Huang 原版本 1403.7388v1 的固定分母上估计仍只提供上界。
第 78 章固定宽度的一维相位下计数也不能用于此处宽度 O(Q^−1) 的双根目标。
第 81 章的新逐层构造直接在精确 G_Q 上进行，未借用这些结论作为同步下界。
一个固定区间内的全部晚期单元存在，与一个固定参数落入无穷多个单元有不同量词；
当前 H_J 的区间依赖正是尚未跨过的边界。
没有新增 E₂ 的维数下界、类别结论、指定双均值实现、有限精度恢复或形式验证声明。

## 第 82 章归属：带权输出密度与后验熵响应

第 82 章证明原实际后验在整个 L=ln(1/σ)→∞、L=o(Q³) 范围的输出积分熵回归：
√δ(H_post−h_nat+L)−(γ/ν)Y 的输出积分绝对值趋零。
平均信息的常数项与典型输出熵的 Q^(1/4) 波动属于不同尺度。
新增综合是全计数中心信息的带权实际／乘积比较、最终噪声尺度的同一量化耦合，
以及独立核心块对带权密度导数余项的控制；归属为 repo-derived。
Bayes 熵恒等式、Gaussian 分部积分、Stirling 与一般光滑密度收敛都是既有工具。

Ivan Nourdin、Giovanni Peccati，*Stein's method on Wiener chaos*，
DOI 10.1007/s00440-008-0162-x，核对 [arXiv:0712.2940v5](https://arxiv.org/abs/0712.2940v5)
及其原 TeX。Section 1.2 的 clef 式在等正态过程与中心 Y∈D^(1,2) 上使用
E[Yf(Y)]=E[〈DY,−DL^−1Y〉f′(Y)]；Section 2 的 ipp 是导数／散度对偶。
对二阶 chaos 的 F，−DL^−1F=DF/2。
本章 F=√δ Σ(Z_j²−1)/2 与光滑函数 h(T^G) 的交叉分部积分，
直接得到 K_M=Σv_jZ_j(Z_j−c_j)。该恒等式及一半系数不作为新发现。
原文也指出 Stein 因子一般不必对 Y 可测；条件化步骤不能被无条件协方差替代。

Ivan Nourdin、Frederi G. Viens，*Density formula and concentration inequalities with Malliavin calculus*，
DOI 10.1214/EJP.v14-707，核对 [arXiv:0808.2088v2](https://arxiv.org/abs/0808.2088v2)
的原 TeX Section 3、key-thm。
对中心 Z∈D^(1,2)，它定义 g(z)=E[〈DZ,−DL^−1Z〉|Z=z]，
并额外要求 g(Z)≥σ_min²>0 几乎处处，才给满实数支撑及显式密度公式。
有限正权平方和有下界，不能自动满足这个全局正下界条件。
本章没有由该定理取得实际后验的正 Stein 核或密度公式，使用的是直接有限分部积分。

Yaozhong Hu、Fei Lu、David Nualart，
*Convergence of densities of some functionals of Gaussian processes*，
DOI 10.1016/j.jfa.2013.09.024，核对 [arXiv:1302.6962v2](https://arxiv.org/abs/1302.6962v2)。
PDF 第 16 页 Theorem 4.1 要求固定齐次 chaos F=I_q(f)、q≥2、EF²=σ²，
以及 M₆(F)=(E||DF||^−6)^(1/6)<∞，才给以四阶累积量控制的密度一致误差。
第 18 页 Theorem 4.4 的高阶导数还要求更高逆导数矩；
该版本显示式出现 3σ² 而非与四阶矩同量纲的 3σ⁴，此处不使用该显示式。
第 36 页 Theorem 6.2 另要求 D^(2,s)、s≥8、逆 Stein 因子 r 阶矩、
r>2 及 2/r+4/s=1。
第 38 页 Theorem 6.5 在其统一 Sobolev、矩与逆导数或逆 Stein 因子条件下，
将正态弱收敛加强为密度一致收敛。
这些额外条件不能省略；本章参考还含一阶项和精确截距，不直接套固定齐次 chaos 结论。

Ronan Herry、Dominique Malicet、Guillaume Poly，
*Superconvergence phenomenon in Wiener chaoses*，DOI 10.1214/24-AOP1689，
核对 [arXiv:2303.02628v3](https://arxiv.org/abs/2303.02628v3)
及原 TeX 的 th:main-negative-moments-sum-chaos、cor:densitysumofchaos。
PDF 第 9 页 Theorem 9 对固定有限 chaos 和 F_n，要求最高阶投影趋于标准正态、
全变量 L² 有界，得到任意固定阶逆 carré-du-champ 矩最终统一有界。
第 9–10 页 Corollary 10(a) 若再有低阶余项趋零于 L²，且 F_n 趋于标准正态，
则密度在每个固定 W^(q,p)(R)、q≥0、1≤p≤∞ 中收敛。

此结论直接覆盖本章 T^G/√ν 的一般密度及 L¹ 导数极限：
最高二阶投影的正态极限由原平方质量剖面得到，一阶与常数余项由精确中心界控制。
不同有限维数组可放在同一个可数等正态序列中。
本章没有把这一 Gaussian 光滑性称为新定理；四块 Fourier 推导另外给出了
两个独立半和的统一导数 L¹ 范数，用于把测量核导数转移给对方块。
原文的 (n+1)^−1G²+G 例子说明最高阶退化时不能仅凭正态弱收敛作此推断。
本章中心区 c/δ 个非退化二阶权重排除了该情形。

信息权重 F_M 的方差可随移动核心增长，不能直接将上述有限 chaos 结论
当作加权二元局部极限；K_M 的中心余项由两个独立块控制，才得到所需签名密度 L¹ 结论。
原始离散计数、固定总数条件化、精确后验中心、实际路径行依赖和最终 σ
则由各自的带权比较支付，不属于一般 Gaussian 结果的自动适用范围。

第 79 章已核对的 Huffmann–Mittelbach Gaussian 信息密度与
Ghourchian–Gohari–Amini 熵连续性原文继续承担其既有范围。
新增条件信息矩结论还需原完整 T 的固定高阶实际矩界；
第 77 章仅有输出二阶矩不能控制含 y² 的任意高阶目标核。
该扩展通过 L_x≤C、Bernoulli 中心矩展开、条件 CDF 截断取得，未用 TV 搬运无界矩。

Hyun-Suk Park，*Density Formula in Malliavin Calculus by Using Stein's Method and Diffusions*，
DOI 10.3390/math13020323，及预稿 DOI 10.20944/preprints202412.0740.v1，
书目已定位，三个原始获取入口返回 HTTP 403；未核对其定理条件，不作为证明前置。
本章不主张一般加权局部极限的新原则、全球原创性、形式验证，
也不宣称去除首项后的后验熵常数修正、熵响应方差收敛或每个输出的统一结论。

## 第 83 章：剩余类同步与 Liouville 多项式根排除

[理论卷第 83 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
保留原固定幅度、原合法十进制分母、精确 Gamma 等系数曲线、完整得分组和共同规模取整。
利用全部剩余类，把实际双根同步构造的对数均值界改进为
$C(1+\sqrt{d\omega}+d^2/Q)$，其中 $\omega$ 是精确切线截距的单侧整数差。
它同时给出长度为 $\ell$ 的区间中、$Q\ge C\ell^{-3/2}$ 时的
$C(1+\ell^{-1/2})$ 逐层界。固定参数的无限同步仍需要一个统一有限界，
或正文所列尚未证明的单侧相位复现条件；逐层构造不自动闭合此缺口。

另一个结果在原合法序列上排除所有非零内部根 $\Pi(\vartheta)$，$\Pi\in\mathbb Q[X]$。
低次多项式的过度格点对齐不能补偿实际均值中的 $3\ln Q$ 前因子；
次数至少三时，$\Pi''(\vartheta)/2$ 在固定有理格之外留下分离相位。
正文给出两个明确允许的无理正根参数，并分别算出趋零均值及相邻格点的指数分离。
这是经典 Taylor、整除和 Liouville 超越论证在原模型上的组合；
没有宣称新的通用多项式小数部分理论，也未将结论延伸到任意有理函数。

D. R. Heath-Brown，*Small solutions of quadratic congruences*，1985，87–93，
[原刊 DOI:10.1017/S0017089500006091](https://doi.org/10.1017/S0017089500006091)。
原文引言及 Theorems 1–3 处理整数齐次二次型的非零小同余解；
Theorem 1 限素数模数和至少四个变量，Theorem 2 在四变量下附加行列式的模素数条件。
其四变量证明通过二维各向同性子空间和行列式为 $p^2$ 的整数子格工作。
原文本层中有损坏的上标和卷号数字，这些不清晰数值不作为此处核验常数。
原计数问题具有实系数曲率、移动的非齐次截距、固定原分母和两个受约束指标；
新增自由齐次化变量或把十进制模数当素数，均不保持原问题。
因此该结果不提供正文所缺的单侧相位命中。

Cheuk Fung (Joshua) Lau，*Simultaneously Small Fractional Parts of Polynomials*，
[arXiv:2407.01611v1](https://arxiv.org/abs/2407.01611v1)。
原 TeX 主定理 `thm:MainTheorem` 对实多项式 $f_1,\ldots,f_k$ 要求全部 $f_i(0)=0$，
在给定宽度乘积与搜索长度关系下寻找一个共同正整数 $n<x$。
显示范围使用 $d(d-1)$，此处仅按 $d\ge2$ 比较，不从其正整数措辞外推到 $d=1$。
原模型的精确切线带非零截距与单侧目标，减去常数会改变命中事件；
Gamma 曲线也不是固定多项式，且其三阶误差在所需尺度上不能直接删去。
全区间的某个 $n<x$ 不同时保证原稀疏合法分母和局部父区间。
上述原假设因而不能消除第 83 章的 $\omega$。

Kiseok Yeon，*Small fractional parts of polynomials and mean values of exponential sums*，
[arXiv:2210.03085v1](https://arxiv.org/abs/2210.03085v1)。
Theorem 1.1 在 $k\ge6$、$s\ge k(k+1)/2$ 下，对无常数项的加性单项式形式
从自由整数向量盒中取得 $X^{-1+\epsilon}$ 小数部分界。
Theorem 1.2 的正幂次数满足 $k_1\ge6$、$2\le t<k_1$，并要求
$s>k_1^2+k_1+2\lceil\sigma(1-k_1)\rceil$；
$\sigma$ 由原文 (1.4) 中缺失幂次确定。
这些多个自由加性变量不是原精确系数图和整数剩余类约束已经拥有的自由度，
不能通过增加变量直接取得原共同规模单元。

N. G. Moshchevitin，*On small fractional parts of polynomials*，
[arXiv:0711.1753v1](https://arxiv.org/abs/0711.1753v1)。
Theorem 1 假设 $t_{n+1}/t_n=1+\gamma/n+O(n^{-1-\epsilon_1})$，$\gamma,\epsilon_1>0$，
讨论可选择乘子 $\alpha$ 的回避集合
$\liminf n\log n\,\|\alpha t_n\|>0$。
原定理写维数严格大于 $\gamma/(\gamma+1)$，末尾证明只总结不小于该值；
此处不使用其严格维数断言。原源文件按声明的 cp866 解码后仍有部分乱码注释，
所用英文条件和 ASCII 数学不受此影响，注释内容不承重。
原合法 $N_n$ 的超稀疏增长不满足该比值假设，固定非线性截距也不是可自由选择的乘子。

Yuval Peres、Wilhelm Schlag，*Two Erdős problems on lacunary sequences: Chromatic number and Diophantine approximation*，
[arXiv:0706.0223v1](https://arxiv.org/abs/0706.0223v1)。
主定理对整数序列 $n_{j+1}/n_j\ge1+\epsilon$，$0<\epsilon<1/4$，
给出一个乘子 $\theta\in(0,1)$，使
$\inf_j\|\theta n_j\|>c\epsilon/|\log\epsilon|$。
原 TeX `thm:dio` 在 $n_{j+M}>2n_j$、$M\ge4$、$240c_0\le1$ 时，
给半径 $c_0/(M\log_2M)$ 的全部目标邻域之补交非空。
原 $N_n$ 满足其稀疏增长条件，故该文确实给可选的回避乘子。
它不判定指定乘子，也不保证由同一率曲线关联的两根共同返回。
第 83 章的明确多项式根排除由原小数展开和对数前因子直接证明，未由一般稀疏性推断。

另取得的 *Small solutions of quadratic congruences and small fractional parts of quadratic forms*
扫描原件 [DOI:10.4064/aa-37-1-241-248](https://doi.org/10.4064/aa-37-1-241-248)
未取得可读的定理正文，不作为证明前提。
这些条件核对仅说明已查原文不能直接补齐当前固定分母的同步缺口；
不构成没有更强结果或全局原创性的断言。
$E_2$ 的存在性、锐利维数及指定双均值的共同实现仍未解决。

## 关联补充 84：噪声衰减校正与后验熵的常数阶二次响应

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
第 84 章在第 82 章的同一计数实现和同一带噪声输出上，确定后验熵的常数阶项。
自然单位下，需扣除的首阶线性项是
$\gamma y/[\sqrt\delta(\nu+\sigma_M^2)]$，完整噪声范围仍为
$\ln(1/\sigma_M)\to\infty$、$\ln(1/\sigma_M)=o(Q^3)$。
扣除后，输出积分 $L^1$ 剖面为
$(1/2-2/\sqrt3)(y^2-\nu)/\nu-\tfrac12\ln\nu$。
未校正分母 $\nu$ 给同一剖面的充要条件是 $\sigma_M^2=o(\sqrt\delta)$；
合法序列 $\sigma_M=Q^{-1/16}$ 则使未校正余量在实际条件输出概率下逃离每个有界区间。

Gaussian 回归的噪声衰减、分部积分、Hermite 二次多项式与
Edgeworth 展开的思想都是成熟工具。新增推导的范围是：实际观测方差和的定量速率、
完整后验的未尺度化中心信息比较、含精确中心的两次分部积分余项、
最终噪声尺度上的返回估计，以及由此得到的模型特定剖面和实际反例。
本条不把一般加权展开或二阶 Gaussian 微积分称作新理论。

Ivan Nourdin 与 Giovanni Peccati 的
*Stein's method and exact Berry–Esseen asymptotics for functionals of Gaussian fields*，
[arXiv:0803.0458v3](https://arxiv.org/abs/0803.0458v3)，
[DOI:10.1214/09-AOP461](https://doi.org/10.1214/09-AOP461)，
提供精确 Gaussian 逼近误差与一项 Edgeworth 修正。
核对的是 2009 年 12 月 9 日 v3 的 32 页作者／IMS 电子重印本；
原件说明其页码及排版与期刊版不同。
Theorem 3.1 位于 PDF 第 11—12 页：中心变量 $F_n\in\mathbb D^{1,2}$、
绝对连续律、方差趋一，Stein 因子误差
$\varphi(n)=\{\mathbb E(1-\langle DF_n,-DL^{-1}F_n\rangle)^2\}^{1/2}$
有限、最终为正且趋零，并要求 $F_n$ 与标准化 Stein 因子误差联合趋于
具有单位边缘方差的二元正态。结论包含 Kolmogorov 界及每个固定阈值的归一化 CDF 误差。
PDF 第 13 页 Proposition 3.3 再要求精确单位方差、有限第三绝对矩及
统一 $2+\varepsilon$ 阶矩，得到

$$
\Pr(F_n\le z)-\Phi(z)+\frac{\mathbb EF_n^3}{6}\Phi'''(z)
 =o_z(\varphi(n)).
$$

这一固定阈值结论不能直接替代增长信息权下的全直线 $L^1$ 带符号密度展开。
第 84 章的累积量常数符合这一经典机制，证明则另行支付实际离散后验、
移动核心以及精细噪声的误差。该 v3 的原始源码端点返回 403；
所需命题取自可读 PDF，未将源码访问失败记为已读 TeX。

Ciprian A. Tudor 与 Nakahiro Yoshida 的
*High order asymptotic expansion for Wiener functionals*，
[arXiv:1909.09019v1](https://arxiv.org/abs/1909.09019v1)，
给出更强的一般多项式加权展开。
核对的是 2019 年 9 月 19 日提交、题页日期 9 月 20 日的 57 页 v1 PDF
及其原始 TeX；[2023 年期刊 DOI](https://doi.org/10.1016/j.spa.2023.07.001)
仅作书目关联，不断言两版本相同。
对象是固定维 Wiener 泛函向量与确定正定目标矩阵。
PDF 第 10 页 [A1] 要求所有 $r>1$ 的统一 Sobolev 正则性、
二阶 Gamma 因子到非奇异矩阵的多项式 Sobolev 速率；
第 11 页 [A2] 要求中心高阶 Gamma 因子的指定 Sobolev $O(N^{-q})$
及 $L^r$ 中的 $o(N^{-q})$；第 15 页 [A3] 给出阶数关系
$q_0(k+1)>q$、$\xi(\ell-d)>q$、$\ell_1>p+1+d$
及期望 Gamma 因子的加权速率。
PDF 第 17 页 Proposition 1 给截断局部密度的加权一致逼近；
第 19 页 Theorem 1 在这些假设下对所有满足
$|g(x)|\le a(1+|x|)^b$ 的可测函数统一给 $o(N^{-q})$ 期望逼近，
每个固定 $a,b>0$ 均可。它覆盖真正的多项式加权测试，不能缩称为只对光滑或紧支撑函数的结果。

将本章 Gaussian 参考对标准化后，该理论提供候选通用路线；
但 $S_G$ 的方差随核心增长，其标准化、再放大的成本必须进入全部 Gamma 因子速率。
本章未仅凭“二者是二次型”就断言 [A1]—[A3] 成立，
而是给出所需的有限恒等式及显式 $O(\sqrt\delta)$ 二阶导数余项。
这不证明该 Gaussian 特例超出上述一般理论。

第 82 章已核对的 Herry–Malicet–Poly
[arXiv:2303.02628v3](https://arxiv.org/abs/2303.02628v3)
Corollary 10(a) 继续直接覆盖有限 chaos 参考的 $W^{2,1}$ 导数收敛；
正文的 Fourier 分块计算同时记录独立半块所需的一致常数。
已核对的 Nourdin–Peccati [arXiv:0712.2940v5](https://arxiv.org/abs/0712.2940v5)
提供 Gaussian 导数／散度对偶。
Nourdin–Viens 的全局正 Stein 核下界并未在此假设；
Hu–Lu–Nualart 原文 Theorem 4.4 的既有印刷维度问题也未作为前提使用。
含噪声的有限恒等式必须保留 $v_G+\sigma_M^2$，这些通用引用不能删除该项。

文献检索范围为 Gaussian 精确误差、Wiener 多项式加权展开与条件二次型，
未命中的关键词结果不构成不存在或全球原创证明。
第 84 章结论是普通数学文本，未作 Lean、摄入、覆盖或冻结声明。
它证明输出积分 $L^1$、同一实现的有界联合极限及纤维内第一平均；
不宣称余量方差／高阶矩收敛、每个输出控制、无界数据平均、
零噪声、$L_M$ 与 $Q^3$ 同阶的噪声、解码效率或实验等价性。

## 关联补充 85：有理函数根的过渡带与对偶曲线的整数约束

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
第 85 章把指定原率根的排除从 $\mathbb Q[\vartheta]$ 扩展到
$\mathbb Q(\vartheta)$，并确定该根对实际熵余项的贡献。
它在前一截断 $t=P_{n-1}/Q_{n-1}$ 上保留
$J_n^F=Q_n^2F(t)+Q_nF'(t)+F''(t)/2$。
该有理量的分母至多为前一层分母的固定幂，远小于 $Q_n/\ln Q_n$；
因此实际多项式过渡带要么为空，要么只有均值为固定正倍数 $Q_n^{-3}$ 的一个组。
根项非零的实际概率为 $O(Q_n^{-3})$。
两个倒数函数例子的预测量分母可精确约分，给出最终空带；它们各自的另一根仍未分类。

Taylor 展开、有理函数的高度控制、整数分离和 Markov 不等式是经典工具。
模型特定内容是原整数层上的完整过渡带判别、三次 Taylor 项进入实际均值的常数、
两个倒数参数的合法性与局部熵后果。
有理函数的分母不被假定为十的幂；普通 Liouville 逼近型分类也不替代原网格上的对数位移。

Ana Paula Chaves、Diego Marques、Pavel Trojovský 的
*On the Arithmetic Behavior of Liouville Numbers under Rational Maps*，
[arXiv:1910.14190v1](https://arxiv.org/abs/1910.14190v1)，
[期刊 DOI](https://doi.org/10.1007/s00574-020-00232-7)，讨论有理映射下的逼近类型。
核对的是 v1 PDF 与原始 TeX 的主定理、高度定义、引理及证明开头。
主定理要求有理逼近 $\alpha_n$ 的误差小于
$H(\alpha_n)^{-\omega_n}$、$\omega_n\to\infty$，并要求
$H(\alpha_{n+1})\le H(\alpha_n)^{O(\omega_n)}$；
其结论用原文的不可约有理函数和系数域次数条件表述为 $U_m$ 分类。
原十进制截断满足此类增长关系，但本文不使用该 $U_m$ 结论，
也不把系数属于任意扩大的数域当成已满足原始性条件。

该 v1 的 `hgamma` 显示式写 $H(F(\alpha_k))\ll H(\alpha_k)^{2m^2}$，
未体现函数次数。$m=1$、$F(X)=X^3+2$ 时，紧正区间内的既约 $p/q$
映到仍既约的 $(p^3+2q^3)/q^3$，高度为 $q^3$ 阶，不能由固定倍数 $q^2$ 控制。
本章另证依赖次数的分母界，不使用该显示指数。
原文关于非稠密 $G_\delta$ 与 Hausdorff 大小的关联措辞也未被用作前提；
类别性质本身不能决定维数。上述范围说明不判定原文所有结论。

V. V. Beresnevich、R. C. Vaughan、S. L. Velani 的
*Inhomogeneous Diophantine approximation on planar curves*，
[arXiv:0903.2817v1](https://arxiv.org/abs/0903.2817v1)，
核对了 PDF 及原始 TeX 中的曲率条件、计数定义、覆盖定理 `thm6`、计数推论和完整下界构造。
固定 $C^3$ 曲线在固定区间上曲率非零时，对每个子区间，存在依赖曲线及区间的常数，
使 $R_0<d\le2R_0$、$k_1/R_0\le\delta\le k_2$ 下的近曲线有理点邻域
覆盖至少一半子区间，并且对两个实平移统一成立。
其分母块确实可映到固定原 $N$ 下的辅助切线分母；
其平移量词也确实允许本章单侧相位对应的变化平移。

实际缺口在其他条件：移动对偶曲线的二阶导数为 $N$ 阶，
原证明的 $C_1=3c_2/(c_1c_0^8)$、$c_0<1/6$、$k_1^3>c_2C_1^2$
使所需充分宽度随 $N^{1/3}$ 增长；并且原计数不要求 $\gcd(p,d)=1$。
归一化曲率后还留下指数 $Q$ 的原格同余条件。
这给出该特定证明的适用障碍，不是最佳可能计数界的不可能性定理。
原文下界的最后 Taylor 估计将可达 $2R_0$ 的分母按 $R_0$ 处理，
修正固定二倍因子不改变上述增长次数；上界证明中平方 Fejér 核的一个常数亦未按原值采用。
两处都未作为本章精确数值前提，也不据此宣称其覆盖定理为假。

Dzmitry Badziahin、Stephen Harrap、Mumtaz Hussain 的
*An inhomogeneous Jarník type theorem for planar curves*，
[arXiv:1503.04981v1](https://arxiv.org/abs/1503.04981v1)，
核对了原始 PDF／TeX 的双重逼近定义、非退化条件、主定理及合并推论。
对固定 $C^2$ 曲线与沿曲线 $C^2$ 的非齐次函数，曲率零集的相应
Hausdorff 测度为零，且逼近函数递减趋零时，
$\sum_q\psi(q)^s q^{2-s}<\infty$ 给 $0<s<1$ 的零测度结论；
合并推论还包含既有的发散全测度半边及 $s=1$ 范围。
其整数线性形式在所有系数高度中无限次逼近，
不能直接产生一个指定原 $N$ 上满足驻点关系与原始基分数条件的有限计数。
同称“对偶”不保证对象和量词相同。

既有 Huang [arXiv:1403.7388v1](https://arxiv.org/abs/1403.7388v1)
在本章的新对偶映射下再次按原件条件核对：
即使暂设曲率常数统一，在宽度 $\delta\asymp A/D$ 处，
所列误差的 $\sqrt A D\ln D+D^{1+\varepsilon}$ 已不能保证固定 $A$ 的正下界；
真实移动曲线还具有增长的曲率常数。
原始三元组条件不能替代 $\gcd(p,d)=1$。这里引用的不是另一个 1403.8038v1。

检索涵盖平移曲线下界、对偶逼近及 Liouville 有理映射；
关键词和近期元数据中未查到可用结果，不构成不存在或全球原创证书。
$E_2$ 的空性、非空性、锐利维数和固定参数双均值实现均未由本章解决。
第 85 章属于普通理论与出处说明，未摄入、覆盖、冻结或作 Lean 声明；
未推出两个倒数参数的全熵余项趋零，也未推出无界熵的实际期望收敛。

## 原文对照：固定凸体薄壳与第 86 章同步上界

[理论卷第 86 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
把原精确 Gamma 曲线的 $O(Q^{-1})$ 整数尺度条带包含于一个固定光滑正曲率凸体
膨胀后的薄壳。由经典固定方向偏差 $O(t^{19/29})$，得到逐原层
$O(Q^{38/29})$ 对整数候选，以及 $\dim_HE_2\le38/87$ 和所述对数规范零测度。
这不证明同步集合非空或空，也不提供共同均值可达性。

**直接使用的原始输入。** Jingwei Guo,
*Lattice points in large convex planar domains of finite type*，
[arXiv:1010.4923v2](https://arxiv.org/abs/1010.4923v2)，2011-06-01；
[原 PDF](https://arxiv.org/pdf/1010.4923v2)、
[原 TeX](https://arxiv.org/e-print/1010.4923v2)。
该版本的 Remarks 6.5(1)（PDF 第 23 页）明确指出非消失曲率、型为 $2$ 时
坏锥 $D_2$ 为空，其方法给 $O(t^{2/3-1/87})=O(t^{19/29})$。
第 86 章使用这一逐方向特例，未把主定理的“几乎处处旋转”换成指定方向。

适用对象是一个固定、含原点为内点、边界 $C^\infty$ 且曲率处处正的紧平面凸体。
Lemma 3.4 先在切／法方向计算支持函数的高阶导数行列式
$-m!^2\kappa^{-2}$，再构造整数方向；第 6 节以这些整数向量生成的子格及全部陪集
分解原格，未把任意实仿射变换当作保整数映射。
Corollary 4.3 给两支支持函数相位的 Fourier 展开。
Proposition 5.2 的支持分离、导数及行列式条件，经固定曲率下界均取得固定常数；
差分阶 $m=3$ 时其 $T\ge C M_*^{9/4}$ 条件在 $T=tD,M_*\asymp D$ 下
给频率范围 $D\le c t^{4/5}$。
第 6 节 (6.10)–(6.13) 的逐锥和式及低／高频余项，与 Lemma 6.2 证明中的
卷积夹逼共同给第 86 章 (86.8)–(86.10)；平滑宽度 $t^{-10/29}$ 同时平衡
面积误差与主相位项，其余幂严格更小。因此所用特例无额外对数损失。
这些是原文的成熟格点方法，不作为本项目新创的一般偏差定理。

**其它来源的适用边界。** Guo 的
[On lattice points in large convex bodies, arXiv:1007.4284v1](https://arxiv.org/abs/1007.4284v1)
主定理处理 $d\ge3$；未用于本章二维结论。
Huxley 的 *Exponential Sums and Lattice Points III*，
[DOI:10.1112/S0024611503014485](https://doi.org/10.1112/S0024611503014485)，
Proc. London Math. Soc. 87 (2003), 591–609，其出版社摘要报告 $131/208$ 指数。
当前未取得完整可核对的原始定理条件，故不据此宣称 $131/312$ 的同步维数界。
原文访问返回摘要 HTML 或需令牌，与“原定理不成立”无关。

Huxley–Ivić 的
[Subconvexity for the Riemann zeta-function and the divisor problem,
 arXiv:math/0611809v3](https://arxiv.org/abs/math/0611809v3)
提供 Bombieri–Iwaniec 方法、局部有理格基与间距问题的背景；其已检查内容不提供
采用上述更强指数所需的完整闭域定理。
Michael Greenblatt 的
[Convexity, Fourier transforms, and lattice point discrepancy,
 arXiv:2402.16636v3](https://arxiv.org/abs/2402.16636v3)
第 2 节在平面正曲率情形以 slab 衰减 $1/2$ 仅给 $2/3$，不足以产生本章严格改进。
圆问题的专门指数也不自动适用于本章完成的非圆凸体。
Bourgain–Watt arXiv:1709.04340v2 的指定版本未取得原 PDF／TeX，未作为定理输入。
检索范围有限，不据未命中宣称更强结果不存在或本章具有全球原创性。

**本章承担的连接。** 原率根映射满足 $\Psi''>0$ 和
$\Psi(u)-u\Psi'(u)<0$；后者使精确保留该弧且包含原点的光滑凸体完成成为可能。
Gamma 修正 $Q^{-1}R_Q$ 与目标条带同阶，须纳入壳宽。
闭内域以严格的 Minkowski 泛函不等式排除，故边界格点不会被错误相减。
全壳多计其它弧仅用于上界；它不能提供下界或相位命中。
最后每对候选只覆盖有共同整数 $L$ 的原 $M=2^L$ 单元，单元宽度 $O(Q^{-3})$
把逐层指数传到同一个固定参数的 limsup 上界。
这些实际模型与几何之间的对应是本章新增推导；原有单根结论和所有开放的双根存在问题保持其范围。

## 原文对照：条件信息方差损失与第 87 章的平方权重桥

[理论卷第 87 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
在同一个实际带噪能量观测下，得到输出积分意义的首个后验信息方差损失。
自然单位的损失为 $-\sqrt{\pi/\kappa}\,Q^{1/2}$，低于原 $Q^2$ 阶方差；
条件为 $\ln(1/\sigma_M)\to\infty$ 且 $o(Q^3)$。
这是一条 repo-derived 的实际模型推导，非一般侧信息单调性。
有限原数据纤维内的后验方差，区别于把输出也平均后的信息量联合方差。

**条件微分与指数族的成熟输入。** Alex Dytso、Martina Cardone，
*A General Derivative Identity for the Conditional Expectation with Focus on the Exponential Family*，
[arXiv:2105.05106v2](https://arxiv.org/abs/2105.05106v2)，2021-08-30；
[原 PDF](https://arxiv.org/pdf/2105.05106v2)，
[DOI:10.1109/ITW48936.2021.9611503](https://doi.org/10.1109/ITW48936.2021.9611503)。
原 Theorem 1（PDF 第 2—3 页）要求 $U\leftrightarrow X\leftrightarrow Y$、
所列条件可积性与输出变量的绝对连续性，给条件均值导数与通道 score 的条件协方差恒等式。
Theorem 2 的 A1—A5 在开输出域、解析充分统计量的连续指数族上给相应特例；
Proposition 3 连接条件高阶累积量。
本章每个有限纤维的输入字母表有限、Gaussian 通道密度处处正，满足所需有限正则条件。
其 Gaussian 特例为
$d\mathbb E[U\mid Y=y]/dy=\operatorname{Cov}(T,U\mid y)/\sigma^2$；
该恒等式本身不控制指数小噪声下一致的平方信息量误差。
本章两次潜在 Gaussian 方差倾斜也是经典指数族微分，明确计算了对应缩放映射，
不把一般微分恒等式列为新发现。

该版本原式 (19) 在一般充分统计量 $T(Y)$ 的记号下，将对数配分函数的一阶、
二阶导数写为 $\mathbb EY$、$\operatorname{Var}Y$；
一般情形正确对象为 $\mathbb E[T(Y)]$、$\operatorname{Cov}(T(Y))$。
原显示式不作为本章前提；本章所用 Gaussian 方差倾斜直接从归一化密度求导。

**varentropy 的适用对象。** Erdal Arıkan，
*Varentropy Decreases Under the Polar Transform*，
IEEE Transactions on Information Theory 62(6), 2016, 3390–3400，
[DOI:10.1109/TIT.2016.2555841](https://doi.org/10.1109/TIT.2016.2555841)。
原文首页的 Theorem 1、1′ 处理两个独立二元数据元素经 XOR 与保留第二位构成的极化变换：
输出 varentropy 之和不大于输入之和，并有原文所列的零方差等号条件。
该处 varentropy 为条件 surprise 的联合方差，不是固定输出后的纤维方差。
它不直接覆盖计数输入的一次带噪能量观测，也不推出任意侧信息都降低纤维内方差。
均匀两点先验配两个不同 Gaussian 均值即可使原先零方差变为几乎处处正的后验纤维方差；
这说明本章负损失需要模型关系，不反驳 Arıkan 原定理。

**密度分部积分与导数收敛。** Yaozhong Hu、Fei Lu、David Nualart，
*Convergence of densities of some functionals of Gaussian processes*，
[arXiv:1302.6962v2](https://arxiv.org/abs/1302.6962v2)，2013-08-29；
[原 PDF](https://arxiv.org/pdf/1302.6962v2)。
Theorem 3.1（PDF 第 10 页）要求
$F\in\mathbb D^{2,s}$、$\mathbb E|F|^{2p}<\infty$、
$\mathbb E\|DF\|^{-2r}<\infty$，其中 $p,r,s>1$、
$1/p+1/r+1/s=1$。
其 $DF/\|DF\|^2$ 的 Gaussian divergence 与密度表示直接覆盖本章的通用机制。
本章具体计算有限维 divergence，并用增长的非中心卡方子块验证统一负矩；
不把未核对非退化条件的固定 chaos 结果直接施于实际离散后验。

Ronan Herry、Dominique Malicet、Guillaume Poly，
*Superconvergence phenomenon in Wiener chaoses*，
[arXiv:2303.02628v3](https://arxiv.org/abs/2303.02628v3)，
[原 PDF](https://arxiv.org/pdf/2303.02628v3)、
[原 TeX](https://arxiv.org/e-print/2303.02628v3)。
Corollary 10(a)，原标签 cor:densitysumofchaos:remainder，
在有界阶 Wiener chaos 之和、最高阶以外的余项趋于零及标准正态分布极限下，
给所述 Sobolev 范数中的密度收敛。
本章参考二次型除以 $\sqrt\nu$ 后满足这些条件，所以一般导数超收敛已有直接先例。
本章的分块 Fourier 证明保留了多项式加权所需的有限常数和整线导数尾界；
原推论本身不提供实际选择律的平方权重比较或条件均值平方的转移。
原 TeX 在定义 score 为 $\nabla\log f$ 后，
标签 eq:score-ipp 的分部积分显示式印为正号；
依该定义应为负号。本章 (87.19) 使用直接推导的负号，不依赖该印刷显示式。

**新增推导与边界。** Stirling 界、量化耦合、Gaussian 卷积、
指数族倾斜、卡方负矩、条件 Jensen 与全方差恒等式均保留经典归属。
本章新增的是原总数条件化下的平方信息权重比较、
平方根密度加权条件均值的 $L^2$ 比较、二阶带符号密度的整线控制，
以及同一个测量噪声的混合核协方差估计。
这些步骤消去两个输出二次项，得到实际完整后验的 $Q^{1/2}$ 阶损失；
仅有第 82、84 章的一阶 $L^1$ 回归不足以平方条件均值。
保留 $\gamma^2/(\nu+\sigma_M^2)$ 不表示余项为 $o(\sigma_M^2)$。
结论不含逐输出有限规模单调性、原数据上的无界期望收敛、
临界噪声相变、更高条件矩或解码算法。
对条件 varentropy、指数族导数、二次型 score 与密度正则化的定向原文核对，
未找到直接涵盖该完整实际后验陈述的原定理；这只是已检索范围内的结论，不证明全球原创性。

## 原文对照：两根边缘通用与第 88 章的非同步族

[理论卷第 88 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
把原精确 Gamma 相位的区间下计数延伸到负内根，并将两种符号共同放入
第 80 章的可数要求质量构造。所得固定参数集在每根分别实现所有正均值，
局部 $2/3$ 维 Hausdorff 测度无穷；删去第 86 章维数至多 $38/87$ 的同步集后，
此临界测度仍无穷。这是 repo-derived 的原模型连接，
不解决同步集合的非空性或空性，也不把分别可达改成同时可达。

**所用成熟方法。** Weyl 的指数和判据、二阶导数检验、固定 Fourier 下逼近、
Baire 定理和质量分布原理保留第 78、80 章的归属。
精确 Gamma 求导在负根仍成立，原因是两个计数坐标在内根紧弧上严格为正；
不是通过正根符号重命名跳过可行域边界。
V. Beresnevich、S. Velani，
*A Mass Transference Principle and the Duffin–Schaeffer conjecture for Hausdorff measures*，
[arXiv:math/0412141v1](https://arxiv.org/abs/math/0412141v1)，
[原 TeX](https://arxiv.org/e-print/math/0412141v1)，
原标签 thm3 及证明的 P0—P5 提供多子层、三倍区间分离、
临界内容累积和任意小质量分布常数的经典机制。
原定理要求放大球 limsup 的全 Lebesgue 测度及规范比值单调性；
单一 limsup 的结论不自动具有本章所需的可数交集性质。
本章复用第 80 章已经给出的任意尺度证明，并逐项验证带符号的输入，
保留下一要求的密度常数；没有复制一份新的通用质量传递定理。
Durand 的 large-intersection 结果所需严格规范或严格指数余量仍保持原范围，
不据类归属单独宣告临界等号处测度无穷。

**近期格点计数与共同原层的缺口。** Jonathan Hickman、Rajula Srivastava、
James Wright，*Counting rational points near manifolds: a refined estimate, a conjecture and a variant*，
[arXiv:2512.23204v1](https://arxiv.org/abs/2512.23204v1)，
[原 TeX](https://arxiv.org/e-print/2512.23204v1)。
其开头计数对整数分母 $1\le q\le Q$ 求和；
曲率条件 CC 要求图映射 Hessian 的每个非零线性组合行列式非零。
原标签 thm: refined count 在允许的维数／余维组合上改进上计数指数，
包括所显示的 $e(n,R)\ge(n+2)R/(n+2R)$。
这不是指定一个原分母的下命中定理，复数／Gaussian 有理变体也改变了算术对象。
因此不用于本章同步存在性；原文所陈猜想不作为已证输入。
复实 Hessian 说明段把实定义域为 $2m$ 的 Hessian 写成 $m$ 阶，
该未用段落不承担这里任何前提；本章不裁定其复数变体。

Damaris Schindler、Rajula Srivastava、Niclas Technau，
*Rational Points Near Manifolds, Homogeneous Dynamics, and Oscillatory Integrals*，
[arXiv:2310.03867v1](https://arxiv.org/abs/2310.03867v1)，
[原 TeX](https://arxiv.org/e-print/2310.03867v1)。
原标签 def counting func 的平滑计数含 $\omega(q/X)$，
其中固定光滑 $\omega$ 支撑在 $[1/2,1]$，空间权重固定，
逼近权重为支撑在 $(-1,1)$ 的偶函数。
原下界定理 thm main lower bounds 要求
$0<\eta\le1/8$、$l$ 非退化、至少 $\lceil(n+1)/\eta\rceil$ 阶导数及
$X^{-3/(2n-1)+a_n\eta}<\delta<1/2$，
$a_n=(2n+12)/(2n-1)$。
其主项 $c_{\mathbf t}\delta^mX^{d+1}$ 和相对误差幂
$X^{-\eta/[d(2l-1)(n+1)]}$ 是整个分母块的结论。
平面曲率对应 $n=2,d=m=1,l=2$，足够小 $\eta$ 时包含
$\delta\asymp X^{-1/2}$；但不能由此断言指定 $q=X$ 有命中。
把 $\omega$ 改成宽 $X^{-1}$ 的可变峰会使导数随 $X$ 增长，
原固定权重常数没有提供所需的一致性；移动 Gamma 曲线也有额外一致性义务。
这说明该引用尚不能补上共同原层下界，不是原曲线无命中的证明。

**结论范围。** 负根桥、带符号的精确原 floor 单元和共同要求日程，
是相对于已有正根通用集的增量；临界质量机制继续由第 80 章承担。
第 86 章薄壳偏差的误差阶大于正面积主项，仍只用作上界，
不能据此推出同层命中或无命中。
所有参数集结论保持同一个原固定参数和合法层序列；
两种实验可共享确定均值的子序列，不表示数据被耦合成同一次观测。
文献核对覆盖上述原定理的权重、曲率和分母量词；
未找到能直接补上指定原层同步下界的已检索原文，不证明这种定理不存在或本章全球原创。

## 原文对照：第 89 章的一般规范律与经典大交集接口

[理论卷第 89 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
保持第 88 章两根边缘通用集的定义、原 floor 单元、固定均值带和合法层序列不变，
将测度判据扩展到连续非减且 $f(t)/t$ 在零处单调趋于无穷的全部规范：
局部 $f$-Hausdorff 测度由 $\sum_nQ_n^2f(Q_n^{-3})$ 的收敛／发散判为零／无穷。
包括层代价趋零、相邻比值无界振荡的规范。
删除第 86 章同步集 $E_2$ 后保持同一判据；其存在性与空性仍未解决。

**局部 ubiquity 的原定理。** Victor Beresnevich、Detta Dickinson、Sanju Velani，
*Measure theoretic laws for lim sup sets*，
[arXiv:math/0401118v3](https://arxiv.org/abs/math/0401118v3)，
[原 TeX](https://arxiv.org/e-print/math/0401118v3)。
采用原文 Theorem 1 后标签 cor2 的推论，及紧邻的 dsm2、afm1 推导。
原条件 M2 要求紧致度量空间上球测度与 $r^\delta$ 同阶；
点状共振集的 intersection conditions 在 $\gamma=0$ 时成立。
推论以局部 ubiquity、开集可测、发散级数
$\sum_n(\psi(u_n)/\rho(u_n))^{\delta-\gamma}$
及 $\psi$ 或 $\rho$ 的 $u$-regular 性推出全测度。
这里取紧区间上的归一化 Lebesgue 测度、$\delta=1,\gamma=0$、
$u_n=Q_n,\rho(t)=c_0t^{-2}$。原单元中点的分离与局部下计数验证 ubiquity，
合法层增长验证 $\rho(Q_{n+1})/\rho(Q_n)\le1/4$ 最终成立。
原推论允许由 $\rho$ 控制双重和；并不要求
$\psi(Q_n)/\rho(Q_n)$ 单调或具有正的上极限。
局部固定正比例覆盖与放大球 limsup 的全测度分别属于假设和结论，
不能用前者冒充后者。

**严格规范与可数交。** Arnaud Durand，
*Sets with large intersection and ubiquity*，
Mathematical Proceedings of the Cambridge Philosophical Society 144 (2008)，
[DOI:10.1017/S0305004107000746](https://doi.org/10.1017/S0305004107000746)，
[作者原稿](https://www.imo.universite-paris-saclay.fr/~arnaud.durand/files/sets_with_large_intersection_and_ubiquity.pdf)。
采用所核对的 26 页作者稿 Proposition 1(e,f)、Theorems 1(a,c)、2，
不声称作者稿与最终排印版逐字相同。
Theorem 2 将全测度放大球族按规范的广义逆缩小后送入大交集类；
逼近族须局部有限于每个正半径阈值之上。
Proposition 1(e) 给包含该集合的 $G_\delta$ 集向上封闭性，
Theorem 1(a) 给可数交封闭性。
原严格顺序 $f\prec g$ 指 $f/g$ 在零处单调趋于无穷；
Theorem 1(c) 对这样的 $f$ 给无穷 $f$-测度，不能直接取 $f=g$。
第 89 章以 $g=f/\Theta(f/t)$ 保留级数发散并逐项核对规范单调性，
因而同一个 $g$ 可供所有有符号均值带使用，再在所需的 $f$ 处结算测度。
辅助规范削薄是成熟方法，原稿证明其有理逼近规范律时也采用这一机制。
广义逆允许规范存在平坦段；本章不额外假定严格可逆。

Arnaud Durand，*Describability via ubiquity and eutaxy in Diophantine approximation*，
Annales mathématiques Blaise Pascal 22 (2015)，
[DOI:10.5802/ambp.349](https://doi.org/10.5802/ambp.349)，
[出版原文](https://ambp.centre-mersenne.org/item/10.5802/ambp.349.pdf)。
Definition 6.4、Theorems 6.9–6.10 及印刷页 63 的端点说明保留上述严格规范边界。
该文文本提取中的部分交集符号失真，承重公式取前述作者稿中清晰的原陈述，
不根据失真文本扩大结论。

**增量与适用边界。** 大交集类、一般质量传递和辅助规范方法均直接归属上述经典理论；
不宣称新的一般 ubiquity 或可数交定理。
本章的模型内增量是两根原单元的完整条件映射、全部振荡规范的级数分类，
以及在同一固定通用集上删除同步集合的结论。
删除步骤使用 $h=\min(f,\sqrt t)$：其级数仍发散，
而 $\dim_HE_2\le38/87<1/2$ 给 $\mathcal H^h(E_2)=0$。
没有据维数上界断言任意发散规范都满足 $\mathcal H^f(E_2)=0$。
参数集测度不作为统计先验；每根各自的子序列仍不等于共同原层。
文献直接覆盖的是通用测度工具，原模型的对象与条件由正文连接；
上述有限文献核对不构成全球原创性认证。

## 原文对照：第 90 章的条件信息谱与第三阶覆盖

[理论卷第 90 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
研究同一个原完整计数后验在一个带噪能量输出之后的最小固定误差覆盖。
在 $\ln(1/\sigma_M)\to\infty$ 且为 $o(Q^3)$ 的范围，
以输出处精确条件熵为中心，给出 $Q$ 阶分位数、$-\ln Q$ 项及常数项。
新增桥梁是输出积分的 $o(1/Q)$ 条件信息谱比较；
原模型内的二维正态正则化使能量尾部比较不再支付逆噪声因子。
第三阶源编码、Edgeworth 和 Cornish–Fisher 项本身是经典方法，
不作为新的一般编码定律。

**常数阶编码的直接先例与印刷边界。** Masahito Hayashi，
*Semi-Finite Length Analysis for Information Theoretic Tasks*，
[arXiv:1811.00262v2](https://arxiv.org/abs/1811.00262v2)，
[原 TeX](https://arxiv.org/e-print/1811.00262v2)，
所核对原稿为 2018 年 11 月 10 日的 29 页版本，源文件为 draft10.tex。
PDF 第 3–4 页定义信息方差、三阶常数和格跨度修正
$v(d)=\ln(d/(1-e^{-d}))$，$v(0)=0$；
第 V 节、式 (51) 给 iid 固定长度源编码的常数精度展开，
第 VII 节说明强大偏差和 Edgeworth 方法。
这些是通用计算机制的直接先例，iid 假设不自动涵盖本章随数据和噪声变化的条件后验。

原式 (50) 将正确解码集合的质量约束写成 $P_X(\Omega)\le\varepsilon$，
按字面取空集即使最小基数为零；相应覆盖约束应为至少 $1-\varepsilon$。
其与随机化检验量的等同还需区分整数点选择。
第 90 章使用有限计数恒等式与部分并列组界，不调用该显示式。
原 Proposition 10（标签 L1）仅声明 $p$ 是概率分布，便写连续 Edgeworth 余项
$O(n^{-1})$；此无格点限制的字面版本不适用于 Bernoulli 格点源，
因为中心跳跃为 $n^{-1/2}$ 阶，与任意连续 CDF 的距离至少为跳跃的一半。
正文只对实际使用的平滑 Gamma 家族验证展开与尾余项。
原文 $\kappa(P\|Q)$ 定义中 $-\log(P/Q)$ 的中心化符号也与所称偏度不符，
本章的第三累积量和分位数符号直接计算。
上述三点均在原 TeX 核对，不归咎于 PDF 字体提取，也不否定其成熟方法。

**有限块长的第三阶界。** Shuqing Chen、Michelle Effros、Victoria Kostina，
*Lossless Source Coding in the Point-to-Point, Multiple Access, and Random Access Scenarios*，
[arXiv:1902.03366v4](https://arxiv.org/abs/1902.03366v4)，
[DOI:10.1109/TIT.2020.3005155](https://doi.org/10.1109/TIT.2020.3005155)。
2020 年 10 月 10 日的 35 页原稿第 3 页 Theorem 1 重述
Kontoyiannis–Verdú 的有限无记忆源界，在正信息方差及有限三阶绝对信息矩下，
对数码本大小的前三项为 $nH+\sqrt{nV}\,z-\frac12\log n$，上下界相差 $O(1)$。
第 4 页 Remark 1 说明固定 $\varepsilon\in(0,1)$ 及可数源字母表的扩展。
该结论不提供本章变动条件后验的精确常数；$Q^2$ 个有效信息项对应 $-\ln Q$，
并非新发现一般的 $-\frac12\log n$ 项。

Ioannis Kontoyiannis、Sergio Verdú，
*Lossless Data Compression at Finite Blocklengths*，
[arXiv:1212.2668v1](https://arxiv.org/abs/1212.2668v1)。
核对的 v1 PDF 第 9–10 页、Section II 的 Theorems 2–3 给一般离散源的
排序／阈值界，第 7 页式 (34) 讨论 Strassen 的非格点精化式。
第 23 页明确指出作者未能验证所引近似在 CDF 积分中的一个步骤，
其 Theorems 16–17 给另行证明的有限无记忆界。
第 90 章的积分核 $e^{u-t}\mathbf1_{u\le t}$ 有界且总变差为二，
已证 CDF 误差为 $o(1/Q)$；这使计数积分的误差同样为 $o(1/Q)$，
不是把指数加权计数直接按 TV 转移。

**侧信息与条件精度。** Lampros Gavalakis、Ioannis Kontoyiannis，
*Sharp Second-Order Pointwise Asymptotics for Lossless Compression with Side Information*，
[arXiv:2005.10823v1](https://arxiv.org/abs/2005.10823v1)。
PDF 第 4 页 Definition 2.1 和 Theorem 2.3 逐侧信息串排序条件概率，
并在大于 $\log n$ 的归一化下比较码长和信息量；
第 6 页 Assumption (M) 对平稳有限字母源及侧信息施加所列 Markov／混合条件，
第 8 页 Theorem 2.10 是以平均条件熵为中心的联合概率 CLT。
这些条件、中心和精度均不推出本章以 $H_x(y)$ 为中心的
输出积分条件局部极限；排序原理仍直接归属经典编码理论。

**密度导数工具。** Yaozhong Hu、Fei Lu、David Nualart，
*Convergence of densities of some functionals of Gaussian processes*，
[arXiv:1302.6962v2](https://arxiv.org/abs/1302.6962v2)。
2013 年 8 月 29 日原稿 Theorem 3.1（PDF 第 10 页）在所列 Gaussian Sobolev
正则性、正矩与逆导数矩条件下，以 $DF/\|DF\|^2$ 的散度表示并控制密度；
Proposition 3.6（第 14 页）在更高正则性和逆矩下控制高阶密度导数。
第 90 章用二维梯度 Gram 矩阵并显式核对逆矩，实现对应的有限维机制。
原标量定理本身不替代二维非退化性验证，更不直接验证实际离散后验。

Chaganty–Sethuraman，*Strong Large Deviation and Local Limit Theorems*，
DOI 10.1214/aop/1176989136，是元数据检索所指的相关文献；
所查原文下载端点返回 HTML 拒绝页，未取得可核对原定理，
故该文没有承担正文任何前提。

**结论范围。** 经典工具与本章实际模型桥梁分开归属：
完整向量条件化、全域有界过渡组、最终噪声尺度耦合、
二维核心正则化和精确中心化共同给出所需条件精度。
结论仅对固定内部误差水平成立，保留原实际 pair/path 和固定支持量词；
不主张每个输出、无界对数余项期望、零噪声、临界 $Q^3$ 对数噪声或高效编码。
有限文献核对未提供直接替代这组实际条件桥梁的原定理，
不构成不存在性或全球原创性认证。

## 原文对照：第 91 章的固定切点复现限制

[理论卷第 91 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
分析第 81、83 章已经构造的原共同规模单元。
逐层局部存在定理直接复用；本章新增的是精确 Gamma 修正的严格负号、
有限固定切点环形窗口的空 limsup，以及首个上方交点规则的单侧相位与等均值限制。
这些限制保持原合法分母、count floor、共同规模相位和实际 pair/path 均值桥。
它们没有解决整个双根同步集合 $E_2$ 的空性或非空性。

**切线方法的经典背景与分母边界。** Victor Beresnevich、Evgeniy Zorin，
*Explicit bounds for rational points near planar curves and metric Diophantine approximation*，
[arXiv:1002.2803v1](https://arxiv.org/abs/1002.2803v1)，
[原 TeX](https://arxiv.org/e-print/1002.2803v1)。
原 Theorems 1–2（源标签 t:01、t:02）在统一正曲率类的闭包内给局部下计数和覆盖；
其第二定理证明使用 Minkowski 线性形式及整数平移，属于有理切线构造的成熟背景。
所数互素三元组允许 $0<q\le X$，覆盖版为 $c_0X<q\le X$，
误差是 $\delta/X$，不是固定 $q=X$ 的结论。
原假设包括 $\delta X^2|J|\ge8C_1$、$X\delta\ge C_2$、$|J|\le1/2$，
以及所列 $X\gg|J|^{-3}$ 或另一二次尺度条件。
在本模型取 $X=N$、$\delta\asymp N^{-1/2}$，固定父区间在晚期可以满足尺寸要求，
但 Minkowski 输出只保证一个区间内的分母。
它未保证该分母整除原 $N$；改为最近的 $N$ 分母网格会产生 $N^{-1}$ 阶误差，
超过本题的 $N^{-3/2}$ 归一化条带宽度。因此不承担固定原层的下命中前提。

**固定分母的算法文献。** Nicolas Brisebarre、Guillaume Hanrot，
*Integer points close to a transcendental curve: an algorithmic approach*，
[arXiv:2606.04858v1](https://arxiv.org/abs/2606.04858v1)，
[原 TeX](https://arxiv.org/e-print/2606.04858v1)。
原 Problem probgen 固定正整数 $u,v,w$，对在复邻域解析的超越函数寻找

$$
\left|f(X/u)-Y/v\right|<1/w.
$$

这允许在问题定义中固定 $u=v=N$，与按分母求和的计数不同。
但 Algorithm algo:2variables 的保证是成功时返回包含所有解的候选列表；
列表可以为空，算法还保留短向量不足及消元 resultant 为零的失败分支。
主定理 thm:cplx2D 是固定函数、固定区间下随输入分母与多项式度数变化的复杂度结论，
原证明明确保留两个辅助多项式互素的启发式假设。
它不给正解数，也不给指定原层上的无限嵌套分支。
本章没有运行该算法，不把随 $Q$ 变化的隐式 Gamma 曲线代入固定函数的复杂度结论，
亦未证明它满足另一个有限阶整函数定理的全局假设。

**本章使用与不使用的结论。** 均值定理、积分曲率、最近剩余类取整、
Stirling／Binet 展开和有限集合的 limsup 推理均是经典工具。
模型内新联系是：原取整使 $A_Q'<0$，从而产生必须抵消的负 Gamma 修正；
同一规模中的 $-3\ln Q$ 预因子又强迫复现指标位于切点左侧，
与右侧首交点的取整规则共同给出 $\omega=O_d(Q^{-2})$。
有理截距排除仅适用于该规则或等正均值子目标；
没有构造原曲线上的有理斜率／有理截距点，也没有排除不等均值的全部同步可能。
文献核对给出上述具体适用边界，不作为不存在性或全球原创性认证。

## 原文对照：第 92 章的指数分辨率与二项量化耦合

[理论卷第 92 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
将精确条件熵中心下的第三阶覆盖扩展到
$\limsup\ln(1/\sigma_M)/Q^3<c_q/2$，仍要求 $\ln(1/\sigma_M)\to\infty$。
该系数是所证充分条件，不是噪声阈值锐性结论。
经典二项耦合支付唯一的逆噪声误差；外部计数能量通过二维联合平移移除，
其与外部信息量的依赖一直保留到最终条件中心化。

**直接使用的有限 Wasserstein 定理。** Thomas Bonis，
*Stein's method for normal approximation in Wasserstein distances with application to the multivariate Central Limit Theorem*，
[arXiv:1905.13615v2](https://arxiv.org/abs/1905.13615v2)，
[原 TeX](https://arxiv.org/e-print/1905.13615v2)。
2020 年 5 月 11 日版本的 32 页 PDF 第 1 页设定 iid、中心化、单位协方差；
第 5 页 Theorem 1、式 (9) 对 $m\ge2$ 给有限 $W_m$ 界：
常数只依赖阶数 $m$，分子由四阶矩矩阵范数和 $(m+2)$ 阶矩显式控制，
分母为 $\sqrt n$。原 body.tex 的 CTLmain、Wpmainthm 标签核对相同陈述。
在一维代入标准化 Bernoulli，成功概率位于 $[1/4,3/4]$ 时所有这些矩一致有界，
故直接取得 $C_m/\sqrt n$，不需密度、非格点或精确成功概率 $1/2$。
一维单调量化同时最小化各固定阶凸运输代价，给正文同一个耦合的 $L^2,L^4$ 控制。
这个精确阶及量化方法完全归属经典结果。

**二项原文的交叉核对。** Alexander A. Serov、Andrew M. Zubkov，
*A Full Proof of Universal Inequalities for the Distribution Function of the Binomial Law*，
[arXiv:1207.3838v2](https://arxiv.org/abs/1207.3838v2)，
[原 TeX](https://arxiv.org/e-print/1207.3838v2)。
2012 年 8 月 31 日版本第 2 页的定理对全部 $n$、$p\in(0,1)$、
$k=0,\ldots,n-1$ 给
$C_{n,p}(k)\le F_{n,p}(k)\le C_{n,p}(k+1)$；
内部 $C$ 为二项相对熵有符号平方根处的标准正态 CDF，
端点单独定义为 $C(0)=(1-p)^n$、$C(n)=1-p^n$。
第 2–5 页给完整 beta 积分及单调性证明，原 0542008.tex 中核对了定理和端点。
紧 $p$ 区间内，有符号根的 Taylor 展开和量化夹逼给
$|X-Z|\le C(1+Z^2)/\sqrt n$ 于 $|Z|\le c\sqrt n$，
其外以 $|X|\le C\sqrt n$ 和正态尾控制各固定矩。
这提供独立的二项专用核对，但正文已直接使用 Bonis 的有限定理。

Serov–Zubkov 将原不等式归于 Alfers–Dinges 的 1984 年文献；
该早期原文未独立取得，归属依据为这里核对的完整证明及其引用。
所取 TeX 的介绍性 Moivre–Laplace 显示式多出一个 $\Phi(x)$ 因子，
其后单独显示的 Stirling 公式省去 $(n/e)$ 的指数 $n$；
紧接的二项系数计算使用 $n^n$。这两处未用显示式不承担本章前提，
不把提取成功等同于每个印刷公式正确。

**不作统一估计依据的后来版本。** Bonis，
*Improved rates of convergence for the multivariate Central Limit Theorem in Wasserstein distance*，
[arXiv:2305.14248v4](https://arxiv.org/abs/2305.14248v4)，
2024 年 4 月 29 日版本第 3 页 Corollary 1 另用截断增量协方差条件，
并含依赖底层分布的渐近余项；更强的非格点收益要求非零绝对连续分量。
Bernoulli 没有该分量，且分布依赖余项不能直接当作随数据变化的 $p_j$ 的一致界。
本章用前述更早的显式有限定理，未借此推导未给出的统一性。

Carter–Pollard，*Tusnady's Inequality Revisited*，
[arXiv:math/0508606v1](https://arxiv.org/abs/math/0508606v1)，
DOI [10.1214/009053604000000733](https://doi.org/10.1214/009053604000000733)，
第 1–5 页 Theorems 1–2 的原对象是 $\operatorname{Bin}(n,1/2)$，有其所列
$n\ge28$ 及内部指标范围和尾部处理。实际 $p_j\to1/2$ 不能替代精确对称假设。
这些成熟结果说明精确量化阶并非新发明；实际参数对应由 Bonis 定理完成。

**组合范围。** 第 90 章已归属的 Kontoyiannis–Verdú、Chen–Effros–Kostina、
Gavalakis–Kontoyiannis 和 Hu–Lu–Nualart 分别承担经典排序／编码与密度机制。
它们不直接提供当前随数据、噪声变化的实际条件后验结论。
本章先比较联合可观测量和中心一阶矩密度，再于最终参考使用条件 $C/Q$ 密度界；
未在保留外部真实能量的中间通道虚报独立性。
文献核对有版本和范围限制，不作为全球原创性证明。

## 原文对照：第 93 章的代数根与傅里叶障碍

[理论卷第 93 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
使用原 $Q_n=10^{e_n}$ 的素因子限制排除代数无理率根的多项式过渡带，
并在根坐标中限制正有限均值复现集合所能承载的傅里叶衰减。
两根同步的存在或不存在未被解决。

**实际应用的子空间定理版本。** Boris Adamczewski、Yann Bugeaud，
*On the complexity of algebraic numbers I. Expansions in integer bases*，
Annals of Mathematics 165 (2007), 547–565，
[DOI:10.4007/annals.2007.165.547](https://doi.org/10.4007/annals.2007.165.547)，
[期刊原文](https://annals.math.princeton.edu/wp-content/uploads/annals-v165-n2-p04.pdf)。
Section 4、印刷第 554–555 页给绝对值、向量范数和射影高度的完整归一化，
Theorem E 给所用 $p$-进子空间定理，并归属于 Evertse。
每个赋值处的形式须线性无关，系数允许是 $K$ 外的代数数，解仍在 $K^m$ 中。
因此正文可取 $K=\mathbb Q$ 而在无穷处使用代数无理系数 $\xi$。
本原整数对的高度是欧氏范数，有限赋值处范数为一；
原分母约分后只有素因子 $2,5$，精确给出正文的受限分母下界。
该一般逼近机制是经典定理的直接应用，不作新数论定理申报。
原文自身的数字复杂度定理和正规性猜想没有承担本文前提。

Jan-Hendrik Evertse，*An improvement of the quantitative Subspace theorem*，
Compositio Mathematica 101(3) (1996), 225–311，
[原文](https://www.numdam.org/item/CM_1996__101_3_225_0.pdf)。
核对了前九个 PDF 页的标题、范围和允许 $K$ 外代数系数的说明。
扫描公式未被现有文本提取完整恢复，故正文精确不等式采用上项已完整核对的
Theorem E，不声称从缺失的扫描显示式中读出了它，也未审计长篇定量证明。

D. Ridout 的历史原文 *Rational approximations to algebraic numbers*，
Mathematika 4 (1957), 125–131，
[DOI:10.1112/S0025579300001182](https://doi.org/10.1112/S0025579300001182)，
及 *The p-adic generalization of the Thue-Siegel-Roth theorem*，
Mathematika 5 (1958), 40–48，
[DOI:10.1112/S0025579300001339](https://doi.org/10.1112/S0025579300001339)，
提供成熟结果的历史归属。所查 Wiley 路径返回 403，Cambridge 的页面及所列 PDF
返回访问页 HTML，未取得完整原定理；它们不是正文独立核验的承重来源。
正文使用前述可访问且完整陈述的 Theorem E。

**实际应用的傅里叶收敛结论。** Andrew Pollington、Sanju Velani、
Agamemnon Zafeiropoulos、Evgeniy Zorin，
*Inhomogeneous Diophantine Approximation on $M_0$-sets with restricted denominators*，
[arXiv:1906.01151v1](https://arxiv.org/abs/1906.01151v1)，
[原 TeX](https://arxiv.org/e-print/1906.01151v1)。
原稿 Beyond lacunarity 节的 mainCONV 定理与 Lemma lem2 直接给正文使用的收敛侧：
若整数倍分母处的傅里叶系数上确界可求和，而目标窗长度也可求和，
则相应上极限集测度为零。此处不需稀疏性或目标函数单调性。
原始有限 majorant 界及 Borel–Cantelli 证明均已核对。
原另一个稀疏计数定理中的对数衰减指数 $A>2$ 不应套到本收敛侧：
原 $\ln N_n$ 的增长使任何 $A>0$ 已足够求和。

该文的发散／下计数结论针对固定标量、固定测度及其明确条件，
不提供同一原层上随 $p,d$ 变化的精确对偶相位、单侧方向和剩余类共同命中的下界。
本章只直接采用收敛结论，配合实际均值给出的必要根邻近窗。
所得零傅里叶维数在根坐标中成立，不借非线性根映射冒领 $\beta$ 坐标的同一结论。

**核对边界。** 最初的 Annals p06 定位返回 Granville–Soundararajan 的另一篇原文，
标题核对后未采用；p04 才是本章使用的原文。
有限的论文检索和版本核对不构成全球原创性认证。
本章贡献是成熟工具在原实际模型中的定量对应，以及其对熵过渡项与可行研究路线的限制；
不把测度工具换成新概率先验，不从数论下界推断可变分母的有效统一常数。

## 原文对照：第 94 章的逐输出平滑与紧区间覆盖

[理论卷第 94 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
将指数分辨率范围内的精确熵中心三阶覆盖加强为每个固定紧输出区间的一致式。
其关键前提是逐输出未归一化测度、中心一阶矩密度及可观测量位移的定量控制，
再以正密度下界条件化。输出积分误差本身不提供这种上确界控制。

**高固定阶量化的来源。** 第 92 章核对的 Bonis
[arXiv:1905.13615v2](https://arxiv.org/abs/1905.13615v2)，Theorem 1、式 (9)，
直接给每个固定运输阶 $m\ge2$ 的有限界。
标准化 Bernoulli 且 $p\in[1/4,3/4]$ 时所需矩一致有界，
所以同一单调量化可在任意高但固定的阶数支付指数小的坏位移事件。
阶数可依赖严格噪声间隙，不能让它随规模增长而忽略原常数的依赖。
Serov–Zubkov 的紧参数量化核对及其未用印刷公式缺陷仍保持第 92 章所列范围。

**正态密度与逆导数矩。** Yaozhong Hu、Fei Lu、David Nualart，
*Convergence of densities of some functionals of Gaussian processes*，
[arXiv:1302.6962v2](https://arxiv.org/abs/1302.6962v2)，2013 年 8 月 29 日版本。
55 页 PDF 第 10 页 Theorem 3.1 要求 $F\in\mathbb D^{2,s}$、
$\mathbb E|F|^{2p}<\infty$、$\mathbb E\|DF\|^{-2r}<\infty$，
其中 $p,r,s>1$、$1/p+1/r+1/s=1$；其散度表示给密度及一致／Hölder 界。
第 3.2、4、5 节的导数与向量比较另有各自非退化假设。
第 94 章使用这一成熟演算机制，但为自己的二维信息量／能量对
明确证明秩、行列式小值概率、逆矩及带权导数；没有将标量定理直接当成向量定理。
固定块的全积分导数界经另一个独立块卷积后才变成切片上确界。

**直接涵盖正态参考密度的超收敛。** Ronan Herry、Dominique Malicet、Guillaume Poly，
*Superconvergence phenomenon in Wiener chaoses*，
[arXiv:2303.02628v3](https://arxiv.org/abs/2303.02628v3)，
[原 TeX](https://arxiv.org/e-print/2303.02628v3)，2024 年 3 月 19 日版本。
40 页 PDF 第 3 页 Theorems 1–2 对固定 Wiener chaos 内趋标准正态的序列
给密度及其导数的强收敛。第 9–10 页 Theorem 9、Corollary 10(a)
处理有限 chaos 和：最高阶投影趋标准正态且全序列 $L^2$ 有界保证负导数矩控制；
若低阶余项在 $L^2$ 中趋零、全变量趋标准正态，则得到正态密度超收敛。
原 super-fmt.tex 的 main-negative-moments-sum-chaos 与
cor:densitysumofchaos:remainder 条目核对相同条件。

第 94 章的正态核心参考归一化后是二阶 chaos 加趋零的一阶及常数余项，
因此参考密度收敛被该经典结果直接涵盖，正文 Fourier 估计给本证明需要的具体分块界。
该定理没有给原离散二项计数在指数小噪声下的逐输出替换误差，
也没有给完整后验中心信息量的一阶矩密度控制；这些仍由正文桥接。
原文还给 $G+(n+1)^{-1}G^2$ 的反例，说明有限 chaos 和趋正态
若未核对最高阶投影条件，并不自动具有连续密度。

**不能直接用于实际二项能量的二次型定理。** 同三位作者，
*Regularity of laws via Dirichlet forms — Application to quadratic forms in independent and identically distributed random variables*，
[arXiv:2303.09488v2](https://arxiv.org/abs/2303.09488v2)，
[原 TeX](https://arxiv.org/e-print/2303.09488v2)，2024 年 6 月 20 日版本。
34 页 PDF 第 2 页 Theorem A 与精确 Theorem 2.10 要求 iid 中心单位方差输入，
输入位于 $\mathbb D^\infty$ 且 carré du champ 有某个有限负矩；
系数算子对角为零，$\operatorname{tr}A^2=1$，
$\mathcal R_{128q+18}(A)>d$ 且 influence 足够小，方得到 $W^{q,1}$ 正则性。
原 reg-ptrf.tex 的 small-ball-gamma 假设、前置零对角设定及
regularity-quadratic-form 定理核对这些要求。
二项量化图像不满足该输入正则性，而当前能量是对角二次型；
故该结果只提供相关方法视角，不能直接承接实际后验。

**计数与边界。** 第 90、92 章已归属的源编码排序、Gamma 的
Edgeworth／Cornish–Fisher 展开与负半对数项仍为经典内容。
本章使用新证的 $o(1/Q)$ 紧区间条件 CDF 误差，
通过总变差为二的计数核和截止并列质量界得到常数精度。
精确条件熵没有被其主阶近似替换，也没有宣称阈值锐性、全输出一致性、
熵响应或条件方差的自动扩展。

文献核对限于所列原版与关系检索；部分 PDF 数学字形提取不完整，
Herry–Malicet–Poly 的承重条件据原 TeX 核对。
一个元数据检索响应为 HTTP 429，不计作已取得文献。
该检索范围不证明全球原创性；正文的新增结论为原模型中上述关系的完整组合。

## 原文对照：第 95 章的有效 Baire 输入与根数位障碍

[理论卷第 95 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
构造原边缘通用集中的可计算参数，并证明有限均值复现根的有符号长数位块。
一般可计算 Baire 选择是既有结果；需要在本模型中补齐的是它的有效输入：
完整得分组等号判定、原取整、实际 pair/path 均值的严格有限证书，以及搜索终止性。

**有效 Baire 的精确表示条件。** Vasco Brattka、Matthew Hendtlass、Alexander P. Kreuzer，
*On the Uniform Computational Content of the Baire Category Theorem*，
[arXiv:1510.01913v1](https://arxiv.org/abs/1510.01913v1)，
[原 TeX](https://arxiv.org/e-print/1510.01913v1)。
原文定义 $\mathrm{BCT}_0$ 于可计算 Polish 空间，输入为以负信息表示的
无处稠密闭集序列；负信息是其开补集的有理球枚举。
原 fact:BCT0-BCT1 明确陈述 $\mathrm{BCT}_0$ 可计算。
Cauchy 表示及负信息表示按该原版核对；没有使用正信息或跳跃版本，
也没有加入极限、泛性或真值 oracle。

第 95 章对每个固定有理均值带、符号及下限层，枚举通过严格原窗条件和
两种完整实际均值条件的 floor 单元内部有理区间。
第 88 章的原层完整单元可用性使该开集稠密，因此它的补集具备所需负名字。
可计算 floor 边界点的补集同样可枚举。
一般的剩余性没有提供这个输入，不能独自保证一个可计算点。
正文显式嵌套构造还输出原合法层及误差日程；没有把每个正实目标都说成
无需目标名字即可沿可计算子序列实现，那会违背可数性。

原文将 $\mathrm{BCT}_0$ 的可计算性追溯至 Brattka，
*Computable versions of Baire's category theorem*，MFCS 2001，LNCS 2136，
224–235，Theorem 6。该早期原文只核对到书目信息，未单独取得完整证明；
承重陈述取自已读的 2015 年原版。
同一 v1 后面的 comeager 定义／推论中存在 $X,\mathbb N^{\mathbb N},2^{\mathbb N}$
的环境空间记号不一致；本章不用该段把 Cantor 空间结论搬到区间，
所用定义和可计算性事实明确针对可计算 Polish 空间。

**原模型的有限算法边界。** 第 68 章已经按 Baker–Wüstholz 原定理证明
固定 $r$ 超越。由此原 $k_0,q$ 取整不在整数边界，完整得分等号化为
有理多项式恒等判定。pair 均值是有限多项式，path 均值由原平稳
$2M\times2M$ 标记转移矩阵幂精确给出；不以独立行或 Poisson 均值替代。
这些证书可枚举，再由第 88 章实际相对均值与整单元下计数保证搜索终止。
未知的渐近起始层不作为算法输入。
这里没有新的一般可计算性定理，也没有对天文尺度有限数组实际运行该算法的主张。

**正规数与前缀频率。** Verónica Becher、Pablo Ariel Heiber、Theodore A. Slaman，
*A polynomial-time algorithm for computing absolutely normal numbers*，
[作者原文](https://math.berkeley.edu/~slaman/papers/poly.pdf)，
2013 年 3 月 4 日版本，13 页。
Section 2.1 固定标准数位和 $b$-进区间；Definition 2.1 定义简单正规与正规；
Section 2.3 的 Definition 2.3、Lemma 2.4 给数位频率偏差及其判据。
本章只用这些经典定义，不应用该文构造绝对正规数的高效算法，
也不据此推断原率函数的逆像保持正规性。

原实际均值展开中的 $-3\ln Q$ 项使正根落在下方格点右侧、负根落在上方格点左侧，
距离为 $3\ln Q/(Q|I'(x)|)+O(Q^{-1})$。
由 $Q=10^{e_n}$ 得位置 $2e_n+1$ 开始、长度
$e_n-\log_{10}e_n+O(1)$ 的零／九块。
这些块占截止前缀的比例趋于 $1/3$，故相关数位频率上极限至少为 $1/3$，
偏差至少为 $7/30$。任意长数位块本身不足以排除正规性；比例估计承担该结论。
第 93 章的超越性和本章的可计算性与这一结论相容，但各自需要自己的证明。

**适用范围。** 两符号日程可以不同；$E_2$ 非空或为空仍未判定，
构造所得参数是否避开 $E_2$ 也未判定。
根的非正规性不自动成为 $\beta$ 坐标的非正规性。
本章不宣称实用复杂度、期望熵收敛、参数随机化或全球原创性。
有限关系检索与上述原版条件核对，只支持所列经典归属和模型内对应。

### 第 96 章：局部矩密度与显式常数阶熵响应

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)第 96 章
在全部严格半指数噪声区间内，将紧输出区间的条件熵中心写成原精确先验熵、
噪声对数、保留实际噪声方差的线性响应，以及显式二次常数项。
其局部带符号矩密度估计与第 94 章的覆盖定理作用于同一实际后验和观测。
Gaussian 分部积分、密度超收敛及 Edgeworth 方法已有来源；
以下区分这些通用工具与实际固定总数模型的传递义务。

Nourdin、Peccati，*Stein's method and exact Berry–Esseen asymptotics for functionals of Gaussian fields*，
[arXiv:0803.0458v3](https://arxiv.org/abs/0803.0458v3)，版本 2009-12-09，
Annals of Probability 37(6), 2231–2261。
原 PDF 第 11–13 页定理 3.1、命题 3.3 分别给标准化固定阈值 CDF 误差
和附加矩条件下的一项 Edgeworth 结论。
前者保留 Malliavin 可微性、绝对连续性、正且趋零的 Stein discrepancy 方差，
以及相应标准化二元向量的 Gaussian 联合极限。
这些条件不直接提供增长的未缩放中心信息量所需的逐点带符号密度展开，
也不自动把参考 Gaussian 结论传到噪声消失的实际离散后验。
第 96 章的两次有限分部积分是经典 Gaussian 演算的应用；
独立半核心的二阶密度导数上界另行支付局部余项。

Tudor、Yoshida，*High order asymptotic expansion for Wiener functionals*，
[arXiv:1909.09019v1](https://arxiv.org/abs/1909.09019v1)，版本 2019-09-19。
原文条件 [A1]–[A3]、命题 1 和定理 1 保留一致 Sobolev 矩界、
Gamma 因子余项的速率、非退化目标协方差，以及展开阶数、
可微阶数和局部化指标之间的明确不等式。
命题 1 给带权一致局部密度逼近；定理 1 对受固定多项式支配的可测测试类给规定的余项阶。
固定维测试类的多项式界不能替代本章未归一化且方差增长的核心信息量之统一估计。
正文直接给出所需一阶带符号密度的有限恒等式与余项范数，
没有宣称已核对整个实际阵列的任意阶 Wiener 展开条件。

Herry、Malicet、Poly，*Superconvergence phenomenon in Wiener chaoses*，
[arXiv:2303.02628v3](https://arxiv.org/abs/2303.02628v3)，版本 2024-03-19，
推论 10(a) 对有限 Wiener chaos 和，在低阶余项于 L2 趋零、
主项归一化后趋标准 Gaussian 的条件下，给所列 W(q,p) 密度收敛，包括 p 为无穷。
本章参考二次能量的最大系数趋零、方差趋正数，非中心线性项、
有限截距和测量噪声在 L2 中趋零，因此其通用导数收敛位于该范围。
原实际计数律不是这个 Gaussian 输入对象；实际局部质量与矩密度的误差仍须另证。
正文的 Fourier 分块估计同时给出对每个正噪声一致的有限导数界。

Mansanarez、Poly、Swan，*Edgeworth expansion on Wiener chaos*，
[arXiv:2510.14002v2](https://arxiv.org/abs/2510.14002v2)，版本 2025-10-27，
原 PDF 第 4 页定理 1.2 对方差归一化的单个固定 Wiener chaos 随机变量，
以其累积量控制到规定 Edgeworth 带符号密度的总变差误差。
这是相关的较新通用展开；定理没有直接给出增长信息权重的点态条件均值，
也没有包含原 count posterior、固定基数或消失噪声的比较。
因此本章不用未核对的加权／多变量推广替代 (96.19)–(96.24)。

Bonis 的 arXiv:1905.13615v2 有限 Wasserstein 矩阶估计，
以及 Serov–Zubkov 的 arXiv:1207.3838v2 任意二项参数 CDF 夹逼，
沿第 92、94 章保留其原作用和条件。
核心内标准化 Bernoulli 的各固定矩一致有界，允许按严格噪声间隙选择一个足够高的固定矩阶；
没有令矩阶随系统大小增长，也未把 p=1/2 的专门定理用于近似 p=1/2。
Gaussian 核恒等式、局部正密度归一化和 Bayes 熵恒等式均属经典工具。

新增实际桥梁分别控制中心信息密度与残差平方密度，
以独立块支付带符号二阶导数余项，并证明实际前两项方差轮廓有 O_P(delta) 精度。
这足以在常数阶把有限随机系数换成 gamma/[sqrt(delta)(nu+sigma^2)]；
只知道方差轮廓收敛不够。缓慢消失噪声说明 sigma^2 不能从该分母删除。
结果限于固定输出紧区间和固定支持数据概率，保留原精确先验熵；
不包含全实线一致性、外层期望熵、零噪声、端点锐性或高效计算。
所核对原始来源未直接给出该完整模型陈述；有限检索范围不构成全球原创认证。

### 第 97 章：可计算复现测度与全部晚层同步排除

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)第 97 章
构造每个有理内部区间中的可计算参数，保留原完整模型的双符号边缘复现，
并排除全部充分晚原层的一个必要同步算术包络。
结论是原 V 减 E2 的有效非空性；它不判定 E2 自身非空或为空。
算法给算术包络的可计算排除起点，实际正紧均值带的最终排除由原渐近必要条件推出，
没有声称已计算每个实际均值带的数值起点。

Galatolo、Hoyrup、Rojas，*A constructive Borel–Cantelli Lemma. Constructing orbits with required statistical properties*，
[arXiv:0711.1478v2](https://arxiv.org/abs/0711.1478v2)，
[原始 TeX](https://arxiv.org/e-print/0711.1478v2)，
DOI [10.1016/j.tcs.2009.02.010](https://doi.org/10.1016/j.tcs.2009.02.010)。
原文 “Constructive Borel-Cantelli sets” 一节定义有效可求和：
有算法由正有理误差给出整个后续尾和的上界起点。
其构造性 Borel–Cantelli 序列由一致有效开的好集组成，
要求这些好集补集的测度有效可求和。
标记 effective_BC_theorem 的定理在完备可计算度量空间、
可计算 Borel 概率测度下，给相应集合中可计算点在测度支撑上的稠密性。
“Shrinking sequence” 引理及该定理证明明确使用嵌套、有效缩径的开集。

这条抽象构造原理已有来源，不属于本章新增的一般定理。
本章先构造承载精确有符号复现证书的独立有限分支有理树和可计算测度，
再给原同步包络全部晚层的显式可求和上覆盖。
若调用上述开好集版本，必须用稍小的闭有理坏覆盖；
开坏集的闭补集不能直接满足它的开集假设。
正文直接证明剩余柱质量可计算并选择正质量子柱，保留一个可计算的算术起点。
单凭正测度有效闭集或小 Hausdorff 维数都不足以保证可计算点。

所检 v2 的 uniform-intersection 命题证明存在一个不用的显示不等式问题：
定义 a_m=2^(-n) 后写坏集测度大于 a_m，而前面的 normal form 给的是相反方向。
本文使用单序列定理的正确条件及正文独立的限制测度构造，
不将这个显示式作为前提，也不据它断言后续版本有同一问题。

Hoyrup、Rojas，*Computability of probability measures and Martin-Löf randomness over metric spaces*，
[arXiv:0709.0907v1](https://arxiv.org/abs/0709.0907v1)，
[原始 TeX](https://arxiv.org/e-print/0709.0907v1)。
“Measures as valuations” 中标记 val_operator 的命题说明
由可计算测度的 Cauchy 描述可以下半计算开集测度；
valuation_equivalence 定理把可计算测度与开集、有限理想球并的一致下半可计算估值联系起来。
它们没有断言任意闭集上的限制测度可计算。
本章用有限有理区间的双侧柱质量逼近及有效孔尾界提供这个额外条件，
不是由一般表示定理直接跳到可计算分支。

Huang，*Rational points near planar curves and Diophantine approximation*，
[arXiv:1403.7388v1](https://arxiv.org/abs/1403.7388v1)，
原文引理 1 给任意有限序列及有限谐波截断的差异度控制。
该工具及经典一阶／二阶导数指数和方法、Fejér 核是几何计数的成熟来源。
其后对分母求和的应用不能原样变成本章单个规定分母 Q_n 的命题。
正文显式给一个较粗但有效的固定层覆盖：
至多 C Q_n^(3/2) 个、长度 C Q_n^(-11/4) 的区间，
不用更锐曲线格点估计的未知常数。

原 signed phase 计数和有限实际完整组证书沿第 88、95 章复用。
新增连接是具有显式全尺度 3/5 次幂上界的可计算复现测度，
以及同步包络在该测度下的 Q_n^(-3/20) 全晚层预算。
基树独立于排除选择；查询剩余质量不会改变此前已定义的复现测度。
这保证每个正剩余质量父柱仍有可选的复现子柱，避免把分别存在的复现和排除
误当作同一参数上可同时实现。

所查来源直接覆盖抽象有效测度工具，没有直接给出本模型全部原取整、
完整组、双实验及同步包络的对应。该范围不构成全球原创认证。

### 第 98 章：局部二阶矩与首个信息方差响应

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)第 98 章
在完整严格半指数噪声区间、每个固定输出紧区间上，确定精确后验信息方差
相对原精确先验方差的主损失及首个输出相关修正。
主损失保留实际噪声方差，下一阶系数为
$(2\gamma/\nu)(2/\sqrt3-1)$。信息量用自然对数；
改用 bit 时，方差及其修正均除以 $(\ln2)^2$。
以下通用求导与展开方法属于已有理论。

Dytso、Cardone，*A General Derivative Identity for the Conditional Expectation
with Focus on the Exponential Family*，
[arXiv:2105.05106v2](https://arxiv.org/abs/2105.05106v2)，版本 2021-08-30。
原 PDF 第 2–3 页定理 1 保留 Markov 链、条件 score 乘积可积、
通道密度导数可积及输出绝对连续条件；
定理 2 在开输出域的连续指数族、解析充分统计及条件矩假设 A1–A5 下，
给条件期望导数与条件协方差恒等式。
本章每个有限实际纤维的 Gaussian 通道满足这些条件，
直接有 $\partial_y\mathbb E[U\mid y]=\operatorname{Cov}(U,T\mid y)/\sigma^2$。
该一般公式不提供指数消失噪声下的一致估计。
正文使用相关的经典归一化指数族求导，对潜在 Gaussian 方差作精确倾斜，
继而显式计算条件二阶矩与均值平方的消去；没有把一般求导恒等式当作新定理。

Tudor、Yoshida，
[arXiv:1909.09019v1](https://arxiv.org/abs/1909.09019v1)，
*High order asymptotic expansion for Wiener functionals*，
条件 [A1]–[A3]、命题 1、定理 1 提供带权局部展开的成熟方法。
其固定维归一化向量的一致 Sobolev 矩、Gamma 因子余项及指标条件
不能直接用于未缩放且方差增长的完整信息量。
本章从有限乘积特征函数给出所需前四阶密度导数的 O(delta) 余项，
未宣称已核验原离散阵列的任意阶 Wiener 展开条件。

Mansanarez、Poly、Swan，*Edgeworth expansion on Wiener chaos*，
[arXiv:2510.14002v2](https://arxiv.org/abs/2510.14002v2)，版本 2025-10-27，
原定理 1.2 对方差为一的固定 Wiener chaos 元素给带符号 Edgeworth 密度的 TV 界，
误差由 Gamma 方差的规定幂控制，展开系数可用 Hermite 矩表示。
这直接覆盖中心二次参考的通用带符号逼近，
但 TV 界本身既不给导数范数余项，也不给局部无界二阶信息矩的传递。
正文另证所需导数界及实际后验的带权局部比较。

Herry、Malicet、Poly，
[arXiv:2303.02628v3](https://arxiv.org/abs/2303.02628v3)，
*Superconvergence phenomenon in Wiener chaoses*，推论 10(a)
覆盖有限 chaos 和在低阶项 L2 消失及 Gaussian 极限下的密度导数收敛。
它提供参考正则性的通用来源，但不直接给本章曲率所需 O(delta) 速率，
也不包含实际选中计数律。原文已注明的 score 分部积分符号疑点
不作证明前提；正文从有限 Gaussian 积分逐项确定所用符号。

Bonis 的 arXiv:1905.13615v2 定理 1、式 (9)，以及
Serov–Zubkov 的 arXiv:1207.3838v2 任意参数 binomial CDF 夹逼，
继续提供第 92、94 章同一量化耦合的固定阶控制。
核心内标准化 Bernoulli 满足统一固定矩条件，
严格噪声裕量允许使用足够高但固定的矩阶。
不将 p=1/2 专用结论未经证明推广至一般 p，也不以实际路径行独立为前提。

本章实际桥梁是：在减去原精确完整先验方差之后，传递局部中心二阶密度；
以平方权重的联合切片导数先支付外部信息量与能量的相关；
用独立块移除精确非中心项；最后控制归一化误差和同一个噪声残差的混合矩。
Gaussian 倾斜、Hermite 代数、核恒等式及 Edgeworth 方法各有经典归属。
结果仅含固定紧区间上的数据概率展开，不给常数阶方差极限、
全实线一致性、全数据期望、一般条件化方差单调性或半指数端点结论。
所核对来源未直接给出该完整模型桥梁；这不是全球原创认证。

## 第 99 章：联合根组合的算术排除

对应 [理论卷第 99 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。
共同整数关系保留同一参数、同一原层、两个取整相位及对数位移，
因而比“两个根分别超越”多保留同步关系：根和、根差必须在实代数数
与原 Liouville 数的有理函数域之外。切向例外和随层变动的切线仍未解决。

Adamczewski–Bugeaud, *On the complexity of algebraic numbers I.
Expansions in integer bases*, Annals of Mathematics 165 (2007),
Section 4, Theorem E，是第 93 章核对的 $p$-进子空间定理版本。
允许独立代数系数线性形式；无穷处欧氏范数、有限处最大范数及高度归一化
不变。本章应用于两根的一个固定组合，不取得移动切线高度的一致界。
有理函数预测量直接复用第 85 章；公共分母可能含 $2,5$ 之外的素因子，
所需性质是它小于原层误差的倒数，而非整除原分母。

以下原始来源用于核对共同薄带路线，未作为同步存在定理：

- Li–Li–Wu, *Multiplicative Diophantine approximation with restricted
  denominators*, [arXiv:2409.18635v1](https://arxiv.org/abs/2409.18635v1)。
  原 TeX 的 thm1Haus、thm1HMeas、ThmSabPsi、ThmLacunary 及下界证明
  涉及自由平面坐标、同标量对角问题或固定整数底数。
  原序列满足相关 lacunarity 条件；缺少的是原反根非线性曲线上的两坐标
  同时命中两个带对数位移的目标。乘积小不保证两项同时小。
- Wang–Li–Li, *Uniform Diophantine approximation with restricted
  denominators*, [arXiv:2302.03923v2](https://arxiv.org/abs/2302.03923v2)。
  原定义及 Theorems 1.1–1.3 使用 $b^{a_n}$，
  假设 $\eta=\limsup a_{n+1}/a_n<\infty$；
  代入原 $b=10,a_n=2e_n$ 则 $\eta=\infty$。
  没有改变原递推以满足该条件。
- Baier–Ghosh, *Restricted simultaneous Diophantine approximation*,
  [arXiv:1503.07107v2](https://arxiv.org/abs/1503.07107v2)。
  原主定理假设正的无理 $k$-Diophantine 向量，$k\ge d$，
  对几乎每个 $\alpha>0$ 给出分母和一个分子均为素数的仿射直线逼近，
  指数为 $1/[d(3k+2)]$ 加允许余量。
  原 $N_n$ 非素数，反根曲线非该直线；几乎处处的分母求和结论
  未被解释为原指定层上的下界。
- Sanford, *A Note on Diophantine Approximation with Restricted
  Denominators*, [arXiv:2606.02620v1](https://arxiv.org/abs/2606.02620v1)。
  原 Diophantine density 定义要求每个充分大分母和每个本原分数有一致命中。
  命题 99.7 的本原测试分数直接否定原集合的任意正密度。
  该结论只使用定义。原主证明约分后未交代分母仍在任意指定集合中的步骤，
  因此不作为前提；这里没有声称反驳全文定理。

Li–Li–Wu 所引矩阵环面收缩目标的 manifold-theory 预印本，
限定检索未定位原文，没有借用未核对定理。
这些范围和不适用条件不构成全球不存在或原创性证明。

成熟工具包括子空间定理、有理分离、Taylor 展开及模运算。
仓内综合是共同整数关系、实际对数均值分离、同层反射尺度与由根和指定的
可计算稠密排除族。反射律以实际边缘复现为条件，没有在构造参数处证明该前提。
完整得分组未被独立 Poisson 行替代；$E_2$ 是否非空仍未解决。

## 追加锚（第 99 章来源后续增补区）

## 第 100 章：常数阶条件信息方差

对应 [理论卷第 100 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。
新增综合是：在完整实际计数后验及整个严格噪声区间上，扣除精确观测到的
有限方差／线性系数后，得到紧输出区间一致的显式二次剖面。
实际到 Gaussian 的中心二阶局部误差直接复用第 98 章；
新步骤把参考余项算到常数阶，并将同一测量残差一起倾斜。
没有从有界余项、弱收敛或 TV 近似直接推出常数极限。

Dytso–Cardone, *A General Derivative Identity for the Conditional Expectation
with Focus on the Exponential Family*,
[arXiv:2105.05106v2](https://arxiv.org/abs/2105.05106v2)，
PDF 第 5 页 Theorem 4、Proposition 3 将条件累积量联系到按充分统计量
缩放的输出导数。其条件是所指定连续指数族及相应可积性、正则性；
第 98 章已经核对 Theorems 1–2 的条件。
Gaussian 有限纤维满足这些有限矩条件，但含逆噪声的公式本身不提供
指数小噪声下一致估计。第 100 章直接证明归一化倾斜的精确密度变换，
倾斜全部潜在 Gaussian 坐标及同一个 $G$，再用热方程求导。
这些是成熟条件累积量工具，不把完整离散信息量冒认为通道的自然参数。

Mansanarez–Poly–Swan, *Edgeworth expansion on Wiener chaos*,
[arXiv:2510.14002v2](https://arxiv.org/abs/2510.14002v2)，
原 TeX Theorem 1.2：固定阶混沌中 $\mathbb EF^2=1$ 的 $F$，
与截至 $4m-1$ 阶的带符号 Hermite 密度之间，TV 误差至多
$C_{p,m}\operatorname{Var}(\Gamma(F,F))^{(m+1)/2}$。
对标准化的中心二次型取 $p=2,m=2$ 可直接给 $O(\delta^{3/2})$
参考带符号分布近似。这不包含本章需要的密度导数上确界、
乘发散系数后的对数曲率余项或实际选中离散律的中心局部矩。
加上独立一阶 Gaussian 噪声后的输出不被未经核对地归入单一二阶混沌。
本章用实际有限系数的乘积特征函数单独证明所需导数界。

Tudor–Yoshida [arXiv:1909.09019v1](https://arxiv.org/abs/1909.09019v1)
的 Conditions A1–A3、Proposition 1、Theorem 1 要求相应 Malliavin Sobolev、
Gamma 因子及指数／正则性条件；未对增长维度的完整未归一化信息量直接套用。
Herry–Malicet–Poly [arXiv:2303.02628v3](https://arxiv.org/abs/2303.02628v3)
的 Corollary 10(a) 提供所规定混沌和的通用密度导数收敛，
不自动提供此处放大后仍为 $o(1)$ 的定量阶。
Bonis 与 Serov–Zubkov 的有限 binomial 耦合输入仍按第 94–98 章的
精确条件复用，不重复声称新的耦合定理。

全部 Gaussian 积分、Hermite 多项式、热方程及指数倾斜代数均属成熟工具。
本章保留实际有限系数、同一残差的混合矩、常数阶核心比较及原支持一致概率范围。
限定文献核查不构成全球原创性证明。没有输出全轴积分、坏数据期望、
零噪声、端点最优性、增长紧区间或新的覆盖效率结论。

## 追加锚（第 100 章来源后续增补区）

## 第 101 章的全输出信息方差平均与文献范围

第 101 章在同一完整计数后验及精确 Gaussian 观测上，将第 100 章的
固定紧区间剖面提升为 $\int|D_x-R_*|f_x\to0$，由此得到平均剩余常数
$8/\sqrt3-25/6$。积分始终在给定数据的先验信道内；外层结论是实际
pair/path 数据概率收敛，对固定支持一致，不包含无界原始数据期望。
原严格区间 $\ln(1/\sigma_M)\to\infty$、
$\limsup\ln(1/\sigma_M)/Q^3<c_q/2$ 全部保留。
精确输出均值先保留，再由 $m_x=O_{\mathbb P}(Q^{-5/2})$ 支付；
观测到的发散有限系数及分母中的有限噪声仍不可替换。

全方差恒等式、条件正交投影、四阶矩截断和 Gaussian 指数倾斜均为经典工具。
新增连接在于先中心化完整信息量，以选中密度的 $L^2$ 误差支付全局方差密度，
在同一潜变量与输出上显式支付噪声残差的变化，联合消去相关外部能量之后
才取消外部信息方差，最后用任意高的固定 Fourier 阶数及 Chernoff 尾界
控制可积残余。紧区间收敛自身不许可积分，TV 自身不传递平方信息量。

Herry–Malicet–Poly，*Superconvergence phenomenon in Wiener chaoses*，
[arXiv:2303.02628v3](https://arxiv.org/abs/2303.02628v3)，原文 §2.3
Theorem 13 假设固定维各向同性向量的各坐标属于指定固定 Wiener chaos，
并弱收敛到标准 Gaussian；对充分大指标给
相对熵 $\le$ 一半相对 Fisher 信息 $\le C$ 乘四阶矩超额。
中心参考 $T_0/\sqrt{\nu_0}$ 属于二阶 chaos、方差为一，
$\max w_j\to0$ 给其正态极限，四阶矩超额为 $O(\delta)$，
故此参考 Fisher 信息速率直接属于既有理论。
它不识别乘 $A^2=O(\delta^{-1})$ 后的常数，也不自动把加入一阶测量噪声的
变量判成同一固定 chaos，更不提供实际离散选中后验的全局结论。
原文采用对数密度梯度的 score 定义，其分部积分显示式的符号问题仍按此前说明保留；
本卷直接从 Gaussian 积分推导所需倾斜，不依赖该显示式的符号。

Mansanarez–Poly–Swan，*Edgeworth expansion on Wiener chaos*，
[arXiv:2510.14002v2](https://arxiv.org/abs/2510.14002v2)，
原 Theorem 1.2 对固定 $\mathcal W_p$、$\mathbb EF^2=1$ 与任意固定正整数 $m$，
给出至 $4m-1$ 次的带符号 Hermite 展开，TV 误差由
$C_{p,m}\operatorname{Var}(\Gamma(F,F))^{(m+1)/2}$ 控制。
任意高固定阶的中心参考展开不是新一般理论；带符号 TV 界仍不控制低密度区的
对数导数。第 101 章通过相同系数数组的特征函数，另证四阶导数反演、
中间区间的相对展开与外部输出尾界，并以固定矩积分多项式余项，
避免额外施加 $\sigma_M^2(\ln Q)^C\to0$。

Dytso–Cardone [arXiv:2105.05106v2](https://arxiv.org/abs/2105.05106v2)
的 Theorems 1–2、Theorem 4／Proposition 3，及 Tudor–Yoshida
[arXiv:1909.09019v1](https://arxiv.org/abs/1909.09019v1) 的
Conditions [A1]–[A3]、Proposition 1／Theorem 1，分别提供已有的条件导数／累积量
关系和带明确 Malliavin 正则性及速率条件的局部加权展开。
前者的固定有限混合正则性成立，但其逆噪声导数不单独提供本区间的全局界；
后者的假设不能自动移植到增长且未归一化的离散信息量。
Bonis 及 Serov–Zubkov 的一般参数二项耦合／CDF 界仍按第 96、98 章核对的
版本和紧参数范围使用，不从对称二项外推。

这些来源的经典机制与本卷实际模型组合分开承担。
本章不声称文献全域原创性、零噪声结论、端点最优性、形式核验或新实验等价。

## 第 102 章：离散二次平滑与占据指数内的平均信息方差

[谱边界卷第 102 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
将第 101 章平均后验信息方差及全输出加权残余的条件扩大到
$L_M\to\infty$、$\limsup L_M/Q^3<c_q$，其中 $L_M=\ln(1/\sigma_M)$。
新步骤直接控制实际二项二次相位，并比较中心信息量前两阶的输出矩密度；
外部计数、精确后验中心与同一 Gaussian 测量残差均保留。
它不宣称严格端点成立、阈值必要或存在实际共振反例。

D. R. Heath-Brown，*A New k-th Derivative Estimate for Exponential Sums via
Vinogradov's Mean Value*，[arXiv:1601.04493v1](https://arxiv.org/abs/1601.04493v1)。
原始 TeX 引言式 (1) 回顾经典 van der Corput 估计：整数 $k\ge2$，
相位具有到 $k$ 阶的连续导数，且 $0<\lambda_k\le f^{(k)}\le A\lambda_k$。
正文只取 $k=2$，得到长度 $N$ 的二次相位和界
$C(N\sqrt{\lambda_2}+\lambda_2^{-1/2})$；
二次相位平移不改二阶导数，负号由共轭处理。
该论文新的 Theorem 1 从 $k\ge3$ 开始，不是本章所用的二阶定理。
经典工具的归属维持 van der Corput；二项单峰质量的分块变差估计与
Abel 求和负责将它转成对任意实中心一致的加权界。

A. Mitalauskas、V. Statulevičius，*Local limit theorem and asymptotic expansion
for the sums of independent lattice random variables*，
Lithuanian Mathematical Journal 6(4), 1966，
[DOI:10.15388/lmj.1966.19754](https://doi.org/10.15388/lmj.1966.19754)。
原期刊 PDF 起始定义与定理处理独立整数值随机变量，并增加算术集中条件。
本章的经验实中心二次型未被证明具有该文要求的共同整数格；
该来源也没有直接提供当前噪声尺度上的前两阶信息矩密度。
所以只作为局部极限定理的相关边界来源，不导入其未核对的算术条件。
原 PDF 公式提取存在字形限制，没有据提取文本宣称精确条件已满足。

Bonis 的 [arXiv:1905.13615v2](https://arxiv.org/abs/1905.13615v2)
Theorem 1 对独立同分布、中心化、协方差为单位阵的和，在相应
四阶及 $p+2$ 阶矩条件下给 $W_p$ 的 $n^{-1/2}$ 界。
一维紧参数 Bernoulli 标准化满足这些假设；同一单调分位数耦合同时实现
所有固定幂的最优运输代价。本章只在多项式低频段使用它，不把该误差除以噪声。
Serov–Zubkov 的 [arXiv:1207.3838v2](https://arxiv.org/abs/1207.3838v2)
任意成功参数的有限二项 CDF 夹逼及单独端点定义，继续提供二项专门核对；
未用对称二项的结论代替实际数据依赖的近半参数。

第 101 章的选中密度比较、相关外部能量支付、核心联合密度正则性、
有限噪声抵消及参考尾界均按原假设复用。
本章新增的高频预算使用固定但可随严格指数余量选择的多个未标记坐标；
信息量的平方展开至多标记两个坐标，测量残差矩的 Gaussian 因子精确保留。
输出密度很小时，用条件均值平方的凸截断支付误差，不作密度下界假设。

所查文献未直接给出这条完整选中计数信道、实际经验中心及移动指数噪声下的
平均信息方差定理；有限检索不构成全局原创认证。
结论仍是给定原始数据后的先验信道积分，在实际确定支持数据律下作一致概率判断，
分别覆盖 pair/path。它不提供无界原始数据平均、任意输出一致近似、
零噪声定理或其他后验泛函的自动推广；纯理论文本未进入消化或 Lean 冻结链。

## 第 103 章：固定阶逐输出 Rényi 熵与稀有能量倾斜

[谱边界卷第 103 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
研究完整计数后验在原 noisy scalar 后的逐输出 Rényi 熵。
对每个固定 $\alpha>0,\alpha\ne1$，在
$L_M\to\infty$、$\limsup L_M/Q^3<c_q/2$ 下，
$\delta[H_\alpha(\mathsf P_x^y)-H_\alpha(\mathsf P_x)+L_M]$
在固定输出紧区间上一致趋于 $J_\alpha/(\alpha-1)$。
这是两种原实际实验各自的、对确定支持一致的数据概率结论。
它不是平均条件熵或标签微观态熵，也不含变化阶数或噪声端点。

Alfréd Rényi，*On Measures of Entropy and Information*，
Fourth Berkeley Symposium, vol. 1, pp. 547–561 (1961)，
[原始 PDF](https://digitalassets.lib.berkeley.edu/math/ucb/text/math_s4_v1_article-27.pdf)。
原定义 (1.21) 对 $\alpha>0,\alpha\ne1$ 给有限分布的阶数熵，
(1.22) 给趋近 Shannon 熵的极限；正文把底二对数换成自然对数。
这一有限定义与 Gaussian 核的幂恒等式只给精确 escort 公式，
不提供本章的稀有输出局部密度。

Tim van Erven、Peter Harremoës，*Rényi Divergence and Kullback–Leibler Divergence*，
[arXiv:1206.2459v1](https://arxiv.org/abs/1206.2459v1)，2012 年 6 月 12 日版本。
原式 (26) 定义正有限归一化下的 $q^{1-\alpha}p^\alpha$ 倾斜律，
Theorem 27 给变分恒等式与极小者；$\alpha>1$ 时极小者结论另要求其所述可积性。
本章有限正概率计数盒上取均匀 $q$，满足这些 escort 识别条件。
计数二项系数本身亦取幂，不是先倾斜独立 Bernoulli 标签再聚合。
所取原文为明确的 v1；请求 v4 返回 404，没有据此宣称已读后续版本。

Joseph B. Kadane，*Sums of Possibly Associated Bernoulli Variables:
The Conway–Maxwell–Binomial Distribution*，
[arXiv:1404.1856v1](https://arxiv.org/abs/1404.1856v1)。
原 Section 2 式 (1) 与 Section 3 指数族形式识别单组计数 escort：
其 $m=C_j,\nu=\alpha$，成功参数换为
$\operatorname{logistic}(\alpha\operatorname{logit}p_j)$。
该分布识别本身不提供随规模变化的整个乘积在指数小噪声下的相对误差；
正文另由带余项 Stirling、原子包络及整个低计数能量范围证明所需估计。

Ronald W. Butler、Marc S. Paolella，*Uniform saddlepoint approximations for ratios
of quadratic forms*，Bernoulli 14(1), 140–154 (2008)，
[arXiv:0803.2132v1](https://arxiv.org/abs/0803.2132v1)。
原 Section 1 在支持端点渐近中固定维数，类 $C_R$ 要求相应最大特征值趋零。
Lemma 5 的式 (8) 给精确非中心平方矩母函数、式 (9) 给收敛带；
式 (10)、(13) 描述鞍点与密度近似。
这些是本文 Gaussian 变换与方法的经典背景，但其固定维数比值定理
不是本章增长三角数组、离散计数 escort 或固定总数修正的定理。
正文对自身数组直接证明最大权重控制、共同正倾斜域及可积 Fourier 尾界。
原 PDF 可读，TeX 来源请求返回 403，未将后者记为成功访问。

Arratia–Goldstein–Langholz 的
[arXiv:math/0506300v1](https://arxiv.org/abs/math/0506300v1)
Condition 2.1、Theorem 2.1 要求独立 Bernoulli 总方差至少为变量数的固定比例，
并取有界中心偏移。本模型补集有 $M$ 阶个变量、方差为 $q=o(M)$ 阶，
不能直接代入该定理。正文复用第 70 章已核对的方差参数补集倾斜证明，
再单独证明窄 Gaussian 权重下的能量条件均值界。

Daniels 的 *Saddlepoint Approximations in Statistics*，
[DOI:10.1214/aoms/1177728652](https://doi.org/10.1214/aoms/1177728652)，
以及 Chaganty–Sethuraman 的 *Strong Large Deviation and Local Limit Theorems*，
[DOI:10.1214/aop/1176989136](https://doi.org/10.1214/aop/1176989136)，
本次仅取得元数据，原 PDF 路径返回挑战 HTML；没有导入未核对的定理。
初次用于寻找 Daniels 的另一 DOI 对应不同题名，已由元数据排除，不作引用依据。

本章与第 70 章的全局计数 Rényi 熵、第 71 章输出平均的信息谱结论区别明确。
新增模型连接包括：在同一稀有输出加权下支付选中律修正，
以实际一、二行矩控制最大权重，保留精确中心的非中心倾斜，
以及在原噪声精度上把相对局部密度返回完整计数后验。
成熟 escort、鞍点和 Fourier 工具不称为原创；有限来源检索不构成全局新颖性认证。
正文仅为纯理论与归属说明，未进入消化或 Lean 冻结链。

## 第 104 章：增长的占据数组与线性噪声余量

[谱边界卷第 104 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
将第 102 章的平均信息方差和全输出加权残余推广到
$\Delta_M=\ln(q/Q^{11/4})-\ln(1/\sigma_M)\ge C_{r,\beta}Q$。
常数由原率函数的 Hessian 上界显式给出，只是充分值。
这允许 $L_M/Q^3\to c_q$，不宣称端点、更小阶余量或阈值必要性。

本章继续使用第 102 章已核对的
D. R. Heath-Brown，[arXiv:1601.04493v1](https://arxiv.org/abs/1601.04493v1)
引言式 (1) 所述经典 van der Corput 二阶导数估计。
所用相位是二次多项式，二阶导数不依赖经验实中心；
每个因子的常数固定，之后乘积中的 $C_v^{n_M}$ 明确保留。
没有使用该文从 $k\ge3$ 开始的新 Theorem 1，
也没有把增长因子数当成增长矩阶或假定相关常数一致。

Bonis 的 [arXiv:1905.13615v2](https://arxiv.org/abs/1905.13615v2)
Theorem 1 及 Serov–Zubkov 的
[arXiv:1207.3838v2](https://arxiv.org/abs/1207.3838v2)
仍只负责固定阶、紧二项参数的低频分位数比较。
第 102 章逐项核对的独立同分布、中心化、协方差及矩假设保持不变。
这一步的误差没有除以缩小的测量噪声。

A. Mitalauskas、V. Statulevičius，
[DOI:10.15388/lmj.1966.19754](https://doi.org/10.15388/lmj.1966.19754)，
继续作为独立格点和局部极限定理的相关边界来源。
原文要求整数值和算术集中条件，本章没有为真实经验中心的二次能量建立这些条件，
因此不直接套用其定理；原 PDF 的公式提取限制也未消除。

模型本身的新连接如下：原率函数在一个固定正位移区间严格低于 $c_q$，
故原计数线上有数量为 $u_*Q^2+O(1)$ 的组，以共同高概率具有指数级占据数。
该事件来自原一、二行相对 PGF 系数和并集界，path 行无需独立。
这些远处组的低阶能量小，却在高频区共同产生二次相位消减。
展开前两阶信息矩后，最多删除两个坐标；其余因子保留原计数及联合相关性。
增长乘积的对数收益为 $Q^3$ 量级，固定因子常数只付出 $Q^2$ 量级，
从而覆盖此前固定因子数无法支付的频率区间。

高频论证与实际选中律、相关外部能量及同一 Gaussian 残差的返回步骤分工明确：
前者新增，后者复用第 101、102 章不含逆噪声的界并核对原假设。
全输出方差通过前三个矩密度和条件均值平方的凸截断控制，未假定输出密度下界。
所有有限观测系数和噪声修正保持精确。

针对增长维数二次格点和、三角阵特征函数乘积及算术平滑所作的有限检索，
未提供可直接代入当前完整选中计数信道的定理；检索元数据未被当作定理来源。
这里区分经典工具与模型内新增推导，不作全局原创认证。
结论是原实际确定支持数据概率下的先验信道积分判断，pair/path 分别成立；
不提供全局原始数据期望、更小噪声的失败结论或其他后验泛函的自动推广。
纯理论文本未进入消化或 Lean 冻结链。

## 第 105 章：逐输出 Rényi 响应与有限噪声中心

[谱边界卷第 105 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
在第 103 章相同原计数后验、pair/path 数据律和半指数噪声区间内，
给出零输出与固定输出之间的 $\delta^{-1/2}$ 线性项及常数阶二次项。
中心采用包含全部原组、精确后验中心和实际噪声的有限鞍点。
对 $|\alpha-1|\ge\eta_Q\gg\sqrt\delta$ 还得到固定正紧区间内的穿孔一致版本；
阶数一的实际导数义务仍未由该比较解决。

R. W. Butler、M. S. Paolella，
[arXiv:0803.2132v1](https://arxiv.org/abs/0803.2132v1)，
*Bernoulli* 14(1), 140–154 (2008)，
继续提供第 103 章已核对的非中心平方和矩母函数、收敛域和鞍点密度前因子。
其固定维数支持边缘比值定理未被当成当前增长数组或实际计数 escort 定理。
本章先对有限 Legendre 函数 Taylor，未对该文近似式作超出假设的微分。

Sojung Kim、Kyoung-Kuk Kim，
*Saddlepoint methods for conditional expectations with applications to risk management*，
[arXiv:1510.01858v1](https://arxiv.org/abs/1510.01858v1)（2015-10-07），
第 2、3 节，Lemma 3.1、Lemma 3.2 和 Theorem 3.3，
研究有连续联合密度的随机向量及其 iid 样本均值，要求鞍点附近的联合累积量函数
和插入导数 $K_\gamma(\eta)$ 解析。插入导数的反演积分与密度的鞍点比值，
是本章条件信息量导数问题的经典近邻。
原离散计数 escort、相关 path 数据和增长数组尚未提供该定理的联合解析输入及一致导数界，
故该文不直接解决 Shannon 延拓；有限支持本身也不能替代随规模一致的界。

Alexander Katsevich，
*Saddle Point Approximation and Central Limit Theorem for Densities in high dimensions*，
[arXiv:2510.21545v1](https://arxiv.org/abs/2510.21545v1)（2025-10-24），
的 Assumption 2.1、Theorem 3.1、Corollary 4.1、Assumption 4.2 与 Theorem 4.3
提供高维密度近似的相关条件。本章不将其作为证明前提。
具体地，对方差一的标准化标量按字面取 $n\asymp\delta^{-1}$，
在 $\xi_n=2.5/\sqrt n$ 处，特征函数模至少 $1-\xi_n^2/2\to1$，
而该版本 Assumption 4.2(3)、式 (4.5) 的右端
$\max\{e^{-\sqrt n|\xi_n|},(1+|\xi_n|)^{-\kappa n}\}$ 趋于 $e^{-2.5}<1$。
故此直接标准化代入不满足印出的条件；这里不擅自修正其尺度，也不对其他版本作结论。
本章所需特征函数包络由原核心平方正态因子直接建立。

Rényi、van Erven–Harremoës 与 Kadane 的归属沿用第 103 章：
有限阶熵、escort 恒等式及幂二项分布是已知结构，未被单列为本章新定理。
新推导把 $O_{\mathbb P}(\sqrt\delta)$ 的未缩放对数密度误差传回实际完整计数后验，
明确支付核宽度扰动的 $|u'-u|/\delta$，并由精确有限阶数导数消除差商分母的伪障碍。
合法慢降噪序列 $\sigma=\delta^{1/8}$ 表明删除噪声鞍点会留下发散线性残差。

针对相对鞍点密度、条件矩与增长数组导数的有限原文检索不构成原创认证。
未取得的 Tierney–Kadane 原文未用作依据；相关访问失败不被当作文献反证。
本文只保留模型内推导及适用边界，不声称输出平均条件 Rényi 熵、Shannon 阶或无穷阶已由此解决。
纯理论文本未进入消化或 Lean 冻结链。

## 第 106 章：二次共振的积分成本

[谱边界卷第 106 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
把完整原计数信道的加权信息方差区间扩大到
$\Delta_M-\tfrac12\ln\ln Q\to\infty$，其中
$\Delta_M=\ln(q/Q^{11/4})-\ln(1/\sigma_M)$。
它保留实际中心任意取实数、完整固定总数后验、相关 path 行及同一测量残差。
任意 $\Delta_M\to\infty$ 的命题仍未解决；新条件只是一条充分条件。

Francesco Cellarosi、Jens Marklof，
*Quadratic Weyl Sums, Automorphic Functions, and Invariance Principles*，
[arXiv:1501.07661v2](https://arxiv.org/abs/1501.07661v2)（2015-02-27），
引言式 (1.3)–(1.4) 的 Jacobi theta 函数及精确函数方程，
要求复二次参数有正虚部，允许复线性参数，直接包含本文 Gaussian 的 Poisson 变换。
第 2.6 节的 $\mathcal S_\eta$ 包含 Schwartz Gaussian。
第 3.7 节 Lemma 3.18 对全部平移变量给尖点包络，
Lemma 3.19 沿 Lebesgue 横坐标积分有理尖点区域。
这提供积分共振峰宽度的经典结构。
本章另写有限分母 Dirichlet 分解，明确二项质量误差、增长因子常数 $C^n$ 和原模型尺度。
未把该文随机 theta 不变原理套到实际后验，也未从一般绝对连续测度推出有界密度。

Roger Baker，*L^p maximal estimates for quadratic Weyl sums*，
[arXiv:2103.05555v1](https://arxiv.org/abs/2103.05555v1)（2021-03-09），
主定理积分线性变量、对二次变量取极大，使用单位权的有限 Weyl 和；
本章则积分二次频率、带耦合的任意线性移位与二项权，故未直接使用该主定理。
其 Lemma 2 的有理主项分解保留误差
$q(1+|\beta_1|N+|\beta_2|N^2)$，本章未把该误差丢弃。
Lemma 3(i) 在相应互素条件下给完整 Gauss 和界，并归属 Estermann；
本章的模平方计算记录可覆盖偶分母的显式 $\sqrt{2k}$ 界。
这些二次数论计算不是新增的一般定理。

Bonis、Serov–Zubkov 仍只供应第 102 章原固定矩阶、紧参数的低频比较，
没有把耦合误差除以最终噪声。
Heath-Brown 的经典二阶导数界保留第 104 章原范围；本章的新积分证明不再按
“整个频段长度乘逐点最坏界”支付所有峰。
Mitalauskas–Statulevičius 的独立整数格点条件未为真实经验中心建立，仍不直接应用。

模型内的新连接是：对所有经验实中心共同主控的周期包络，每周期只付
$O(\mathcal D^{-1})$，其中 $\mathcal D=(q/Q^{11/4})\sqrt\delta$；
对数个原中心组控制中频非零有理峰，固定 16 个未标记因子与 Gaussian 权逐周期控制全部远频。
最多两个信息矩标记及同一 $G^2,G^4$ 项全程保留，所得任意多项式精度通过凸截断
进入条件均值平方，并复用无逆噪声的实际选中律回接。
小分母峰的标记抵消尚未证明，不能据现有上界失败宣告原命题失败。

有限原文检索不认证全局原创。结论是先验信道积分在实际数据概率下的判断，
未声称无界原始数据期望、逐输出一致、零噪声或其他泛函已同步推广。
纯理论正文未进入消化或 Lean 冻结链。

## 第 107 章：最大计数原子与无穷阶端点

[谱边界卷第 107 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
在原半指数噪声区间给出逐输出最小熵变化的系数 $\gamma/[2\rho(0)]$，
并独立证明 $\alpha\to\infty$、$\alpha\le\ln Q$ 的一致有限阶桥接。
最大原子由完整有限计数元组上的约束极小值直接处理；
固定阶 Rényi 系数的无穷阶极限只作一致性核对，不承担极限交换。

Robert König、Renato Renner、Christian Schaffner，
*The operational meaning of min- and max-entropy*，
[arXiv:0807.1338v1](https://arxiv.org/abs/0807.1338v1)，
Definition 1、独立子系统特例及 Theorem 1，
将经典—量子态的条件最小熵与最优 POVM 猜测概率的负对数相联系。
侧信息也为经典时，该量先平均每份侧信息下的最佳猜测概率。
本章对象是指定输出处的 $-\ln\max_n\mathsf P_x^y(n)$，不是该平均条件熵。
无条件最大原子定义相容，本文另从原 Gaussian Bayes 公式推导逐输出恒等式，
并将 bits 转为 nats。

Tim van Erven、Peter Harremoës，
[arXiv:1206.2459v1](https://arxiv.org/abs/1206.2459v1)，
Theorem 6 给无穷阶 Rényi 散度的本质上确界表达，
在可数空间为 $\ln\sup_xP(x)/Q(x)$，须保持其零值约定。
取有限均匀参照律即得到最大原子熵。
其固定分布对的阶数连续性不能代替本章增长模型的双极限论证。

Bernard Bercu、Jean-François Bony、Vincent Bruneau，
*Spectrum of the product of Toeplitz matrices with application in probability*，
[arXiv:0712.1302v1](https://arxiv.org/abs/0712.1302v1)，
Theorem 2.3、Theorem 2.4 要求连续实符号 $f,g$ 且 $g\ge0$，
给有限 Toeplitz 乘积的极端特征值与无限算子谱边缘的对应；
谱边缘一般不等于 $fg$ 的极值。
第 3 节、Corollary 3.1 对平稳 Gaussian 过程二次型给速度 $n$ 的大偏差原理，
其率函数可有斜率 $1/(2\lambda_{\max})$ 的仿射部分。
这提供谱边缘成本形状的经典近邻，但对象是 Gaussian 事件概率，
不能直接证明原受条件约束离散计数的最大原子或指数窄平滑密度。

本章使用经典二项众数比的离散曲率，以向量误差避免损失整个组数的常数；
全盒下界与最大经验方差组的可行整数构造分别承担两个方向。
原固定总数修正上、下界按各自方向使用，没有假定远元组上的统一正下界。
增长阶数的密度证明使用固定内部倾斜及单个平方坐标的显式密度，
未假定边界鞍点对阶数一致内部化。
高组 Stirling、尾项与核宽度误差中的 $\alpha\le\ln Q$ 因子逐项支付。

有限原文检索不认证全局原创；经典工具与模型内组合分开归属。
结论保留原实际 pair/path、紧输出和确定支持一致的概率范围，
不提供下一输出尺度、任意更快阶数、Shannon 阶或输出平均熵的结论。
纯理论文本未进入消化或 Lean 冻结链。
