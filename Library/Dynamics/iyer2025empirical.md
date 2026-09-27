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

## 第 108 章：绝对众数成本与近端包络

[谱边界卷第 108 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
把最大后验原子的领先阶成本推进到绝对 $o(1)$ 精度。
原完整经验最大方差 $v_*$ 保留在放大输出斜率中；
有限噪声项在逐输出成本中可发散，却在两个输出相减时严格抵消。
证明覆盖全部最小化元组，不预设唯一最大权重或唯一最优配置。

Jean-Jacques Moreau，*Proximité et dualité dans un espace hilbertien*，
Bulletin de la Société Mathématique de France **93** (1965)，273–299，
[Numdam 原文](https://www.numdam.org/item/BSMF_1965__93__273_0/)。
第 1 节的 $\Gamma_0(H)$ 是实 Hilbert 空间上适当、下半连续的凸扩展实函数。
Proposition 3.a 给平方距离罚项加该函数的唯一极小点；
Examples 3.c–3.e 分别处理仿射函数、非空闭凸集的示性函数和两者之和。
Example 3.e 的答案是先按仿射系数平移再投影。
取 $H=\mathbb R$、$C=[0,\infty)$、仿射系数 $\delta\sigma^2/(2v_*)$，
直接得到本章 $e^\circ(h)=(h-\delta\sigma^2/(2v_*))_+$。
这一步是经典定理的直接应用；它不证明原离散计数成本与仿射成本相差 $o(1)$，
也不赋予离散实际极小元唯一性。
原文完整 PDF 的提取含一项数值 token 替换警告；上述法文假设及公式可读，
未把提取进程成功等同于所有字形无误。

Philippe Mounaix、Satya N. Majumdar、Abhimanyu Banerjee，
*Bose-Einstein Condensation of a Gaussian Random Field in the Thermodynamic Limit*，
[arXiv:1111.3229v2](https://arxiv.org/abs/1111.3229v2)。
Section II 的 (i)–(iii) 假设包括环面上中心齐次 Gaussian 场、归一化正定协方差、
严格的零频最大协方差模、存在的极限谱、径向对称和谱边缘幂律。
式 (21)–(24) 把临界强度写为谱亏损倒数的积分；
边缘指数 $\zeta$ 小于维数 $d$ 时该积分有限，$\zeta\ge d$ 时无限。
Section III.A 相应排除后者的有限强度凝聚转变。
这些是热力学极限下条件场质量的结论，不是固定总数离散计数的最大原子公式。

形式上的谱轮廓 $\rho(s)/\rho_0=e^{-\kappa s^2/2}$ 对应一维二次边缘，
亏损倒数在零附近不可积。这与本卷 $K'(1/(2\rho_0)-)=\infty$ 的边界相容，
但不构成原计数模型的凝聚或非凝聚定理。
尤其不能从“单个最大方差坐标给可行上界”推导“典型后验质量凝聚于该坐标”。
本章未采用严格最大值或谱间隙假设。
所取版本横幅为 2012 年 1 月 30 日的 v2，PDF 内部日期为 2021 年 9 月 6 日；
两种日期原样区分，不由内部日期推断另一个版本。

本章的实际模型内容是完整有限经验系数比较、全元组离散曲率下界、
同一数据纤维的整数上界构造，以及原噪声精度下的绝对成本拼接。
普通密度归一化由第 105 章的实际相对鞍点比较推出，没有以弱收敛替代密度定理。
经典包络法、二项对数凹性及 Stirling 展开分别归属其成熟来源；
有限文献核查不认证全局原创。结论仍是纯理论文本，未进入 Lean 或消化链。

## 第 109 章：半整数带、theta 标记与未闭合的方差抵消

[谱边界卷第 109 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
在 $\ln(1/\sigma)\to\infty$ 且任意 $\Delta=\ln(q/Q^{11/4})-\ln(1/\sigma)\to\infty$ 下证明实际标量输出的
加权 $L^1$ 平滑，并将前两阶信息标记的剩余项定位于非零半整数共振带。
原完整信息方差定理仍缺带内中心抵消和输出尾部控制，未由标量结果自动推出。

Daniele Agostini、Carlos Améndola，*Discrete Gaussian distributions via theta functions*，
[arXiv:1801.02373v2](https://arxiv.org/abs/1801.02373v2)。
Section 2 定义采用 $e(x)=\exp(2\pi x)$，复对称矩阵的实部正定；
参数还必须避开 theta 零除子才能形成归一化分布。
Proposition 4.1、Remark 4.2（PDF 第 11–12 页及对应原 TeX）
把特征函数写成移位 theta 比，把矩写成 theta 导数、累积量写成对数导数；
协方差分子是 $\theta\theta''-(\theta')^2$，并由热方程联系线性与二次倾斜。
这些基本公式在原文亦归属此前离散 Gaussian 文献。

本章一维 Gaussian 相位对应矩阵参数
$B_{\rm theta}=1/(2\pi d)-2i\tau$、线性参数
$u_{\rm theta}=m/(2\pi d)+ib/(2\pi)$，实部条件成立。
但复杂经验相位处的 theta 分母未获一致非零保证；
因此本章保留不除以单坐标因子的有限乘积标记公式。
该文没有给原二项信息标记、固定总数选中律或增长数组下的统一二阶导数估计，
也不支付条件方差比较的全输出尾部。

J. P. Buhler、A. C. Gamst、R. L. Graham、A. W. Hales，
*Explicit error bounds for lattice Edgeworth expansions*，
[arXiv:1710.08845v1](https://arxiv.org/abs/1710.08845v1)。
Theorem 1 与 Section 1（PDF 第 1–4 页）处理有界、非退化整数随机变量的 iid 和，
固定格距与平移，给均值两侧概率差的一阶偏度及同余修正；
归一化表述把格距设为一，允许实平移。
版本横幅为 2017 年 10 月 24 日，内部标题日期为 2018 年 9 月 12 日，二者区分。
这说明格点修正须保留自己的算术条件，
并非直接适用于本章非同分布二次计数、经验实中心、Gaussian 平滑及两个信息标记。
骰子例子也不构成原实际计数模型的反例。

第 106 章已核对的 Cellarosi–Marklof [arXiv:1501.07661v2](https://arxiv.org/abs/1501.07661v2)
的 theta 变换及 Lemmas 3.18–3.19 提供经典 cusp/移位包络关系；
Baker [arXiv:2103.05555v1](https://arxiv.org/abs/2103.05555v1)
Section 2、Lemma 3 的完整 Gauss 和界保持其互素条件。
它们的分布性或最大估计不替代原共同环境的量化相位分离。
本章另直接证明小分母收缩与单模宽度：分母一、二只有一个模为一的 Fourier 模，
更大固定分母有严格收缩；使用全部可用中心因子将每个共振带物理积分宽度降至常数。

条件方差的共同调制抵消和信息倾斜二阶导数是经典条件矩与指数族恒等式，
不被另称为新通用定理。这里的模型内内容是实际标记 Fourier 定位、
无逆噪声的选中标量回接，以及保留精确中心、完整外部相关性和同一测量残差的接口。
原中心有理独立只排除精确共振，不给所需的近共振速率。
有限原文检索未找到直接承担全部剩余估计的结果，不认证其不存在或全局原创。
纯理论文本未进入 Lean、消化或冻结链。

## 第 110 章：有限 Gibbs 响应、Prékopa 边缘与高阶端点

[谱边界卷第 110 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
在原半指数噪声条件、固定原幅度与固定 $\beta$ 下，把紧输出的 Rényi 熵差
一致延伸到 $\alpha\ge a_Q$ 的整个无界区间，其中 $a_Q\sqrt\delta\to\infty$。
更强的有限阶因子公式覆盖每个固定 $c>0$ 的 $\alpha\ge c/\sqrt\delta$；
当 $\alpha\sqrt\delta\to c$，相对最小熵响应留下 $y/(2c\rho_0)$。
经验最大方差保留在放大中心中，收敛仍为实际数据概率、支持一致、pair/path 分别成立。

John C. Baez，*Rényi Entropy and Free Energy*，
[arXiv:1102.2098v4](https://arxiv.org/abs/1102.2098v4)。
完整五页原文的 Section 1 equations (1)–(2)、Section 2 equations (3)–(9)
把有限正概率写成 Gibbs 分布，并将 Rényi 熵表示为自由能差商。
原文注明 Beck–Schlögl 等已有相关恒等式；本章精确幂后验恒等式属于这一经典代数。
计数元组保留原二项质量及乘数，不能换成微观标签的等概率状态。
该文不给增长维数和阶数下的统一响应、稀有能量输出回接或实际路径行估计。
版本横幅为 2022 年 5 月 17 日，内部标题日期为 5 月 18 日，两者区分。
提取文本中 equation (9) 前一个未使用中间式缺少所需对数符号，
未判定来自原 PDF 还是提取；这里使用可读的 (9) 与正文直接有限求和，不依赖该中间式。

Dario Cordero-Erausquin，*On matrix-valued log-concavity and related Prékopa and Brascamp–Lieb inequalities*，
[arXiv:1801.04862v1](https://arxiv.org/abs/1801.04862v1)。
Theorem 1（PDF 第 2 页）对 $C^2$、正定、逐纤维可积的矩阵值 N-log-concave 函数，
给边缘仍为 N-log-concave；矩阵维数一就是经典 Prékopa 对数凹边缘定理。
Section 4（第 14–17 页）的 Proposition 10、Fact 11 及结尾证明已核对。
本章用明确的光滑正函数逼近 Gaussian 密度乘凸球上图集指标，
以支配收敛核对非中心、非等方差有限数组下的小球 CDF 对数凹性。
该定理只给每个有限维度的定性凹性；维度一致的小球下界、对数导数界与卷积尾界由本章另证。
不把平方和密度本身说成对数凹。
原文 reference [8] 归属 Prékopa 1971 年论文；另查的 1973 年原文未取得，未冒称已读。
两份当前原 PDF 的字体提取警告保留为来源边界，可读原命题与直接推导承担所用结论。

第 108 章已核对的 Mounaix–Majumdar–Banerjee
[arXiv:1111.3229v2](https://arxiv.org/abs/1111.3229v2)
讨论不同的 Gaussian 场凝聚问题，其齐次性、维数和谱端条件不直接承担本章原计数定理。
本章从原经验剖面证明 $v_*=v_0$ 及 $1-v_j/v_0\gtrsim\min(j^2\delta^2,1)$，
再对非最大模作合法临界倾斜，保留最大平方的未归一化核。
有限 CDF 控制全部非最大模，未由端点优化推出典型单模凝聚。

本章新增综合连接是原缩小谱隙、逆平方权重的小球支付、
至 $Q^6$ 的原计数幂律相对比较，以及由 $\ln N\le CQ^5$ 与无穷阶重叠。
有限支持的 $H_\alpha-H_\infty$ 界分别用于两个输出，未推断熵差单调。
有限文献检索不认证全局原创；未给无界输出、期望熵、Shannon 端点或更宽噪声结论。
纯理论正文未进入 Lean、消化或冻结链。

## 第 111 章：格点惊异比较、Gaussian 标记积分与条件方差接口

[谱边界卷第 111 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
给出同整数坐标上的二项／离散 Gaussian 中心惊异比较，
通过共同带噪通道的有符号核收缩，将原完整方差熵目标归约为格点大组问题。
大组和原外部组都保留各自惊异与能量的共同实现；实际固定总数选择由原中心方差比较支付。
归约不依赖输出密度下界或把能量误差除以噪声宽度。

第 109 章已核对的 Agostini–Amendola，
*Discrete Gaussian distributions via theta functions*，
[arXiv:1801.02373v2](https://arxiv.org/abs/1801.02373v2)，
仍提供离散 Gaussian、theta 正规化和矩的经典背景。
其既有 Proposition 4.1 与 Remark 4.2 不自动给出本章原二项中心惊异的有符号质量误差、
增长数组的全输出条件方差比较或原 path 数据范围。
本章的 $d^{-1/8}$ 比较明确给出 Stirling 中央余项、加权尾与精确中心的支付。
共同正核的 $L^1$ 收缩和条件均值的截断变分公式属于成熟测度与条件期望方法。

Denis S. Grebenkov，*Optimal and sub-optimal quadratic forms for non-centered Gaussian processes*，
[arXiv:1307.0185v1](https://arxiv.org/abs/1307.0185v1)。
原 TeX Section II 给 Gaussian 二次型特征函数、迹展开及非中心累积量。
其模型是离散时间的连续值 Gaussian 向量，不能把 “discrete-time” 当作整数格点概率。
本章以原有限 Gaussian 积分直接核对零、一、二阶惊异标记，
保留复均值和方差后得到聚合扭转能量乘 Gaussian 衰减；
再将所有实际 Poisson 模求和，逐坐标正规化接近一，故没有隐藏指数维数因子。
Gaussian 平方完成和矩求导本身不主张新意。
版本标识为 2013 年；当前 PDF 标题日期为 2018 年，原 TeX 使用日期宏，两者区分。

完整补偿后，任意实扭转的非零半整数混叠绝对积分为
$Ce^{-ce^{2\Delta}}+O(Q^{-400})$，不乘增长的 $Q$ 次幂。
只减先验方差的弱补偿则在原渐近权重上留下 $A\asymp Q^{1/4}$ 的参考扭转项。
所选参考扭转未被证明由原经验中心实现，故这个反例只限定估计方法。
频率相关复中心与逐输出条件均值仍是不同对象，完整非线性条件方差和尾部接口保持开放。

另检索 DOI [10.1214/aop/1176994310](https://doi.org/10.1214/aop/1176994310)
的全文入口只得到 HTML 阻断，未将其计作已读原文或定理依据。
有限文献检索不认证全局原创。
本章是原模型中的综合推导，未进入 Lean、消化或冻结链；
全余量下的实际方差熵极限仍未解决。

## 第 112 章：小球对数极限、凹性导数与移动经验谱

[谱边界卷第 112 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
把高阶 Rényi 输出响应延伸到 $\alpha\ge c\delta^{-1/4}$，得到原有限经验谱的修正
$-C_{\mathrm{edge}}y/(\alpha^2\sqrt\delta)$，其中
$C_{\mathrm{edge}}=\pi^2\rho_0/(\kappa\gamma^2)$。
有限阶因子保持精确，原半指数噪声条件不变，噪声可以任意慢地趋零。

Alexander Nazarov，*Log-Level Comparison Principle for Small Ball Probabilities*，
[arXiv:0805.1773v1](https://arxiv.org/abs/0805.1773v1)，2008 年 5 月 13 日，九页原文。
Proposition 1 比较固定正可和特征值序列，要求特征值比的无限乘积收敛。
Section 2 Proposition 2 对固定无限序列定义
$L(u)=-\tfrac12\sum\ln(1+2u\lambda_n)$，
在 $(L'(u)+r)/\sqrt{L''(u)}\to0$ 下给小球概率的尖锐渐近式。
原文将该式归属 Lifshits 1997 年 Theorem 2，并引 Sytaya 1974 年的 Gaussian Hilbert 空间方法；
这两个更早原件在本轮未取得，归属来自已读 Nazarov 原文。

本章数组有限、随机，随 $Q$ 和 $\alpha$ 同时改变；该命题不直接给它们的一致导数。
因此正文明确证明有限 Laplace 和的内外尾、倾斜均值与方差，再由固定步长割线和对数凹性得到能量导数。
这属于经典方法的原模型统一应用，不被称为新的通用小球原理。
Theorem 1 另有计数函数积分增长条件，Remark 2 给正则变动的充分范围与移除条件后的失败边界。
提取文本的计数函数不等号会对正可和无限序列给出无限计数，
尚未判定是原 PDF 还是提取问题；本章不采用该歧义定义或对应计数函数定理。
可读有限 Laplace 公式及正文独立的有限和承担推导。

Alexander I. Nazarov、Ruslan S. Pusev，
*Comparison Theorems for the Small Ball Probabilities of Gaussian Processes in Weighted L2-Norms*，
[arXiv:1211.2344v1](https://arxiv.org/abs/1211.2344v1)，2012 年 11 月 10 日，十页原文。
Section 2 Theorem 1／Corollary 1 与 Section 3 Theorem 2 处理固定自伴微分算子的 Gaussian Green 过程，
要求系数正则性、规范边界条件、权重属于相应 $W_\infty^n$、远离零且规定的根次幂积分相等。
Proposition 2 的积分 Brownian bridge 还保留 Proposition 1 的正则性与归一化假设。
在 $m=0$、权重一时指数因子为 $e^{-1/(8\varepsilon^2)}$，
与逆平方谱的经典常数一致；它不提供本章有限经验谱、非中心均值、移动阶数和原噪声的统一性。
没有把实际数组冒认为一个固定 Green 算子的谱。

第 110 章已核对的 Cordero-Erausquin
[arXiv:1801.04862v1](https://arxiv.org/abs/1801.04862v1)
Theorem 1 标量情形及 Section 4 证明仍承担 Prékopa 边缘凹性。
光滑正函数逼近凸球上图集指标后，支配收敛得到 CDF 对数凹；只用定性凹性，不引入维数常数。
Baez 的有限 Gibbs／Rényi 恒等式继续承担精确代数部分，未被扩称为移动数组定理。

Anderson–Darling 1952 原文入口返回 HTTP 200 的 1162 字节 HTML 阻断，未取得 PDF 或采用其定理。
两份 Nazarov 原 PDF 的字体提取警告及未使用定义的歧义保留为来源边界；
所用条件和公式均已核对。有限检索不认证全局原创。
本章未进入 Lean、消化或冻结链，也不声称更慢任意增长阶数、无界输出或 Shannon 端点已统一解决。

## 第 113 章：同输出温度输运与任意发散的格点平滑间隙

[谱边界卷第 113 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
证明原计数后验信息方差在所有 $L\to\infty$、
$\Delta=\ln(q/Q^{11/4})-L\to\infty$ 下的全输出加权收敛。
原有限噪声系数、实际经验中心、固定总数选择和 pair/path 范围均保留。
第 111 章的格点归约和较弱补偿反例仍成立；新增结果补上归一化输出导数与尾部接口。

Daniele Agostini、Carlos Améndola，*Discrete Gaussian distributions via theta functions*，
[arXiv:1801.02373v2](https://arxiv.org/abs/1801.02373v2)。
原 Proposition 4.1 和 Remark 4.2 给 theta 导数的矩、累积量、协方差与热方程关系。
其复参数域要求二次参数实部正定，并须避开 theta 零点除子才可取相应对数导数。
本章只对正实格点归一化和求导，并用绝对收敛 Poisson 和直接控制前两次温度导数，
没有假定复邻域无零点。
这些成熟有限格点指数族恒等式不自行提供增长数组、原经验中心或条件方差商的统一误差。

Denis S. Grebenkov，*Optimal and sub-optimal quadratic forms for non-centered Gaussian processes*，
[arXiv:1307.0185v1](https://arxiv.org/abs/1307.0185v1)。
原 Section II 的对象为有限实 Gaussian 向量、正定协方差和实对称二次型矩阵；
行列式形式的非中心特征函数及累积量来自精确 Gaussian 积分。
其中离散时间 Gaussian 过程仍是连续取值变量，不是整数格点分布。
本章以这些经典积分为参考，并另证固定物理输出下的温度换元：
坐标、噪声和扭转共同变换，快速输出相位保持不动。
来源版本的 2013 年 6 月 30 日 arXiv 身份、PDF 所印 2018 年 11 月 12 日以及原 TeX 的自动日期各有其字面范围，
不据排版日期改认版本。

Cellarosi–Marklof [arXiv:1501.07661v2](https://arxiv.org/abs/1501.07661v2)
与 Baker [arXiv:2103.05555v1](https://arxiv.org/abs/2103.05555v1)
的原 theta、Poisson 与 Gauss 材料保持第 106、109 章所列适用边界。
当前证明的实际输入是已经展开的两标记条带外界及第 111 章的格点质量比较；
没有借用未验证的丢番图条件、随机相位不变测度或条件局部极限定理。
Buhler–Gamst–Graham–Hales [arXiv:1710.08845v1](https://arxiv.org/abs/1710.08845v1)
的原定理针对独立同分布、有界、固定格距的格点和，不直接覆盖本章数组。
正文所需连续参考导数精度由实际权重累积量和中央坐标块的可积 Fourier 界逐项证明，
不由通用超收敛结论猜测速率。

正文的新增连接是归一化模的输出一、二阶导数分别带最大权重的一、二次幂，
从而与增长迹相乘后仍有界；随后在完整条件商中保留平方项，并以同一律的适中区间和尾部支付全先验方差。
核心联合密度导数是未加权估计，无界方差的转移另由第四矩裁剪承担。
非大组能量与惊异保留联合关系，支付后才消去外部先验方差。
这些条件不由文献中的单个有限 Gaussian 恒等式替代。

按 theta 热关系、条件 Gaussian 累积量及 Stein／二次型温度关系作有限检索，
未取得直接覆盖原标记格点条件方差结论的新定理；该未命中不证明文献中不存在结果。
本章不声称全局原创、形式核验、固定间隙或更小间隙下的结论，也不把充分条件称作锐阈值。

## 第 114 章：完整经验鞍点与增长阶数的相对局部密度

[谱边界卷第 114 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
在原严格半指数噪声条件下，用包含全部经验方差、非中心均值和能量噪声的有限累积量方程
$K'(t_\alpha)=V$，统一每条确定 $a_Q\to\infty$ 之上的 Rényi 输出响应，包括无穷阶。
精确有限系数保持在放大的线性项内；本章不声称有界阶数或 Shannon 附近的统一结果。

R. W. Butler、M. S. Paolella，*Uniform saddlepoint approximations for ratios of quadratic forms*，
Bernoulli 14(1)，140–154，2008，
[arXiv:0803.2132v1](https://arxiv.org/abs/0803.2132v1)。
原 Section 1 明确其支持端点渐近中维数固定。
Lemma 5 要求其非退化比值类 $\mathcal C_{\mathcal R}$、非负分母矩阵及非零分子秩；
式 (8)–(10) 给非中心 Gaussian 二次型变换、收敛带与鞍点导数。
本章的逐坐标 Gaussian 积分是这些经典变换的基本形式，不需要该比值类。
原固定维数相对误差定理未被直接套用于增长有限数组、移动阶数、非中心项和原整数计数后验。

Ivan Nourdin、David Nualart，*Fisher Information and the Fourth Moment Theorem*，
[arXiv:1312.5841v1](https://arxiv.org/abs/1312.5841v1)。
原 Theorem 1.1 要求方差一的 $F$ 属于固定阶 $q\ge2$ 的单一 Wiener 混沌，且对某个 $\varepsilon>0$ 有
$\mathbb E\|DF\|^{-4-\varepsilon}\le\eta$；Fisher 信息界的常数只依赖 $q,\varepsilon,\eta$。
Corollary 1.2 在一致负 Malliavin 矩条件下才把第四矩收敛扩展为密度的一致收敛。
没有该条件时，所列前四个等价断言不包括密度上确界收敛。
只引用第四矩中心极限定理不能省去这个假设。

本章中央辅助二次部分确实满足该文条件。
若 $W_0=2\sum w_j^2$、$F_0=\sum w_j(Z_j^2-1)/\sqrt{W_0}$，则它属于二阶混沌，方差一，
第四累积量为 $48\sum w_j^4/W_0^2\le C/A_\alpha$。
原比较坐标块还给
$\|DF_0\|^2\ge(c/A_\alpha)\chi_N^2$，其中 $N\ge c'A_\alpha$。
取 $\varepsilon=2$，由
$\mathbb E(\chi_N^2)^{-3}=1/[(N-2)(N-4)(N-6)]$
得到所需一致六阶逆范数矩。
因此中央辅助二次部分的密度收敛已有成熟直接依据。

完整倾斜变量还含 $2m_j\sqrt{w_j}Z_j$ 与独立 Gaussian 噪声，不属于单一二阶混沌。
正文对这个完整变量直接验证精确非中心特征函数、共同坐标块的可积频率尾和局部三阶余项，
再在倾斜均值附近取得密度远离零的相对比。
完整经验根与高计数组均值的差、相邻噪声宽度、原计数舍入和稀有输出下的固定总数选择，各自单独支付。
这些桥梁不由上述单一混沌定理自动提供。

所读原件的 arXiv v1 印记为 2013 年 12 月 20 日，而正文首页另印 2022 年 4 月 25 日；
这两个字面日期保留其来源范围，未据此改认 arXiv 版本。
PDF 提取产生字体警告，原 Theorem 1.1、Corollary 1.2 及式 (1.8)–(1.16) 的条件可读并已核对；
不声称无警告提取或完美字形转录。

第 105 章 Kim–Kim 来源要求独立同分布向量及其联合累积量的解析条件，
第 112 章 Nazarov、Nazarov–Pusev 来源处理固定谱或固定过程的小球问题；
这些边界不因新的经验鞍点写法而扩大。
正文不从 $C^0$ 渐近式微分出未控制的密度比，也不把高阶数的有效噪声误当作仍大于整数网格。
第 112 章的有限支持重叠与本章无界阶数的根到极点估计，共同承担无穷阶连接。

指数倾斜、局部中心极限、特征函数反演和有限 Rényi 恒等式均属经典方法。
本章新增的原模型连接是完整根处的高组相对密度、任意慢增长阶数的一致性、同一稀有输出的选择回接，
以及保留非中心项的无界阶数比较。
有限文献检索不认证全局原创，也不证明这些连接在其他文献中不存在。

## 第 115 章：一般 Gaussian 泛函密度定理与经验鞍点曲率

[谱边界卷第 115 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
在原严格半指数噪声条件下，把响应统一到每个固定 $\epsilon>0$ 的全部
$\alpha\in[1+\epsilon,\infty]$，保留完整有限经验根和 $K''(t_\alpha)$。
有界阶数的标准化输出只留在紧区间，正态密度的相对比因而贡献曲率，不能全部用中心密度替换。

Yaozhong Hu、Fei Lu、David Nualart，*Convergence of densities of some functionals of Gaussian processes*，
[arXiv:1302.6962v2](https://arxiv.org/abs/1302.6962v2)。
原 Section 6 的 Theorem 6.5、条件 (6.10) 适用于一般 Gaussian 泛函：
要求 $F_n\in\mathbb D^{2,s}$，$\|F_n\|_{2,s}$、$\|F_n\|_{2p}$、
$\|\|DF_n\|^{-2}\|_r$ 一致有界，$p,r,s>1$ 且 $1/p+1/r+1/s=1$，
以及向非退化正态的分布收敛；结论为连续密度的一致收敛。
证明以密度有界、等度连续和尾界建立紧性，再由分布极限确定所有子序列极限。

本章直接应用这一定理，取 $p=2,r=4,s=4$。
完整高组倾斜能量加原 Gaussian 噪声是方差一的至多二次 Gaussian 多项式，
系数平方和给维数无关的四阶 Sobolev 界。
原比较坐标块的平方系数至少为 $c/A$，有 $N\asymp A\to\infty$ 个坐标；
移位平方 Gaussian 范数的 Laplace 变换不超过中心情形，因而明确验证
$\mathbb E\|DF\|^{-8}\le CA^4/[(N-2)(N-4)(N-6)(N-8)]\le C$。
精确非中心特征函数给分布收敛。沿任意允许数组序列应用原定理，得到移动参数族的一致密度结论。

原 Theorem 6.2 使用另一随机量
$\langle DF,-DL^{-1}F\rangle$ 的逆矩，配合 Hessian 算子范数和不同指数条件；
本章不把它与梯度范数的逆矩混用，也不使用 Theorem 6.5 的替代条件 (6.11)。
第 114 章 Nourdin–Nualart 来源的单一混沌条件保持原范围。
本章完整非中心变量含一、二阶混沌，采用上述一般定理。

原定理不自动提供原计数幂律、完整选择、经验中心和方差的相对回接。
正文另外支付完整根与高组前两累积量之差、正密度紧区间上的相对对数比、相邻噪声宽度、
含二项系数的原计数取幂、稀有输出下的同一选择权重，以及所有更高阶数的精确有限方差下界。
该下界在同一根方程中分配均值贡献，保留非中心项，支持全无界阶数的曲率消失。

所读原 PDF 为 55 页，arXiv v2 印记为 2013 年 8 月 29 日，正文另印 2018 年 7 月 13 日；
保留两种字面日期，不据此改变版本归属。提取有可选 fontTools/CFF 警告；
上述定理、条件及完整紧性证明可读并已核对，不声称无警告提取或视觉核验。
第 105、114 章 Butler–Paolella 的固定维数适用边界保持不变。

Gaussian 累积量、Malliavin 密度判据、指数倾斜和有限 Rényi 代数均是经典结果。
本章为原实际模型补出有界阶数曲率与全阶数连接，不把经典一般密度定理称为新发现。
有限来源搜索不认证全局原创；固定 $\epsilon$ 的结论不自动延伸到 Shannon 端点。

## 第 116 章：固定带宽的 wrapped 核与实际相位修正

[谱边界卷第 116 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
在 $\ln(\sigma q/Q^{11/4})\to D\in\mathbb R$ 时保留全部半整数混叠，
给出原后验方差熵的显式有界相位修正及全输出加权余项。
原无修正极限等价于一个明确的经验周期积分趋零；这一实际中心断言仍未证明或反驳。

Daniele Agostini、Carlos Améndola，*Discrete Gaussian distributions via theta functions*，
[arXiv:1801.02373v2](https://arxiv.org/abs/1801.02373v2)。
原 Proposition 4.1 和 Remark 4.2 给 theta 比特征函数及其对数参数导数的累积量，
要求实二次部分正定，并在复杂参数上避开 theta 除子。
热方程把协方差与二次参数导数联系起来。
本章只对正的实 Gaussian 归一化求导，另以正 wrapped 核混合证明输出质量下界；
没有假设个别复杂 Poisson 模或复杂 theta 值非零。
这些有限数组恒等式不提供增长维数下的实际经验中心模一反集中。

Aaron J. Hendrickson、David P. Haefner，
*Valley-peak modulation in phase space: a law-invariant VPM and its theta-function structure*，
[arXiv:2603.01199v3](https://arxiv.org/abs/2603.01199v3)。
原 Section 3 的模型为 $X=\mu+(K+\sigma Z)/g$，其中 $K$ 是任意整数值变量、$Z$ 是独立标准正态。
模一个电子单位可精确消去整数 $K$，得到只依赖噪声的 wrapped Gaussian 相位。
其 *Wrapped Gaussian series and Jacobi theta functions* 小节同时给正 Gaussian 周期和与 Fourier/Jacobi 表示。
这些是正文 (116.33) 采用的经典核恒等式。

该文的分布不变性不消去本章的实际 $\Theta(K)$：
原二次能量含经验线性中心，不是该文的整数仿射信号。
正文保留共同计数相位，使用同一个正核的移位混合取得下界，
不把相位均匀或相位与惊讶独立当作前提。
该文的相机噪声、Poisson 大曝光和估计精度结论不被移用为后验方差熵或经验中心算术定理。
核的归一化在正文中明确：圆周平均为一，而原 wrapped 密度积分为一。

原第 68 章的完整选择中心共享初等对称多项式分母。
其有理独立性来自固定幅度的超越性和有理函数的不同消失阶，只排除精确等式，
不提供对偶格点附近的定量距离。
一、二行比较给占据和剖面，不能直接当作后验中心的联合模一反集中。
正文保留这个区别，并给充分条件及必要充分周期判据各自的结论方向。

第 111、113 章的 Grebenkov、Cellarosi–Marklof、Baker 及格点 Edgeworth 来源保持原范围。
Grebenkov 处理连续 Gaussian 二次型；Agostini–Améndola 提供真正离散 Gaussian 的 theta 运算。
已有格点 Edgeworth 论文不直接给本章增长维数、完整选择和同一输出下的条件方差结论。
所需定量导数展开由原特征函数乘积及固定高阶 Taylor 余项建立，
原中心带符号质量、非线性商式和外围能量误差分别支付。

有限相关检索未获得适用于这些共同后验均值的模一反集中定理。
一般 Dirichlet/Beta 后验反集中和其他模型的周期结论不被当作可用桥梁；
这不证明所需结果不存在，也不认证全局原创。
新增成果是原模型中的完整相位公式与边界归约，剩余实际概率问题按正文保留。

## 第 117 章：可微鞍点误差与 Shannon 差商的原计数回接

[谱边界卷第 117 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
在原严格半指数噪声范围内，将完整有限经验响应统一到闭区间 $[1,\infty]$。
响应以一阶处的精确系数作锚；Shannon 值由有限系数的阶数导数给出。
为支付趋于零的差商分母，正文证明了 Gaussian 密度比、原计数幂律和完整固定 $q$
选择修正的共同一阶可微余项，保留实际中心、低组、二项系数和任意慢衰减噪声。

Jesse Goodman，*Asymptotic accuracy of the saddlepoint approximation for maximum likelihood estimation*，
[arXiv:2005.11028v3](https://arxiv.org/abs/2005.11028v3)。
所读原 PDF 为 80 页，arXiv v3 印记为 2022 年 1 月 24 日，正文日期为 1 月 25 日；
两者按原文保留，不更改版本归属。
核对范围为 Section 2.2 的 standard asymptotic regime（SAR），
Theorem 1 及条件 (2.9)–(2.10)，Section 4.2 的 Proposition 10、Corollary 12、
式 (4.6)–(4.11) 与 Theorem 1 的证明。

原 SAR 要求 $X$ 是固定参数律的 $n$ 个 iid 副本之和，$K=nK_0$、$x=ny$。
条件 (2.9) 要求归一化倾斜特征函数有多项式衰减包络；条件 (2.10) 控制连续混合变换导数，
其阶数为 $k\in\{0,1\}$、$1\le k+\ell\le6$，以及 $k=2$、$0\le\ell\le2$。
Theorem 1 在归一化观察与参数的紧集上给出对数鞍点似然梯度误差 $O(1/n)$。
Proposition 10 与 Corollary 12 提供其中使用的连续可微余项。
核心步骤把精确指数倾斜因子提出，对剩下的 Fourier 积分求导，并在可积包络下控制导数。

上述定理不直接涵盖随 $Q$ 变化的非同分布经验数组、完整计数后验的固定 $q$ 依赖，
或指数小测量噪声。本章采用这一经典方法关系，实际验证当前二次数组的特征函数与导数包络，
不把固定 iid 定理的常数视为已经对本章数组族一致。
正文另外证明同一稀有输出下总偏差、模态惊讶与似然惊讶的联合矩，
以插入势能的配分函数比较回接原计数，再用精确选择协方差公式支付导数。
保留总偏差平方后，选择导数误差为
$O(\delta^5(1+m_Q+\delta^{-1}))=O(\delta)$，而非凭零阶误差直接求导。

第 115 章 Hu–Lu–Nualart 的 Theorem 6.5 仍只在其 Gaussian Sobolev 与逆梯度矩条件下
提供零阶密度收敛；它不提供本章对熵阶数的导数。
其既有应用用于远离一的阶数连接，本章另行验证包含一阶的可微桥梁。
Kim–Kim 的条件插入统计量方法和 Butler–Paolella 的二次型变换保留既述
iid 连续模型或固定维数边界，不替代本章原计数比较。

原 PDF 文本提取有可选 fontTools/CFF 编码警告；上述条件与推导可读且已核对，
不声称无警告提取或视觉核验。
有限幂律微分、指数倾斜、Gaussian/Wick 矩公式、Stirling 界、Fourier 反演及均值定理
均属经典工具。本章提供的是这些工具在原完整模型上的联合导数估计，
不把一般可微鞍点理论称为新发现；有限检索不认证全局原创。
结论不自动延伸至一阶以下、无界物理输出、输出平均熵或半指数边界等号。

## 第 118 章：拒绝抽样的一阶修正与实际相位中心的精度预算

[谱边界卷第 118 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
证明完整三标记周期泛函在共同相位平移后的中心稳定性，
其自然距离为 $\rho^2=\sum_jd_j(\widetilde\mu_j-\mu_j)^2$。
随后用经典拒绝抽样修正和精确双锚恒等式，分别将实际中心归约到可控精度。
固定噪声间隙下该实际周期泛函是否趋零仍然开放；中心的低维表示不是独立随机相位假设。

Hélène Boistard、Hendrik P. Lopuhaä、Anne Ruiz-Gazen，
*Approximation of rejective sampling inclusion probabilities and application to high order correlations*，
[arXiv:1207.5654v1](https://arxiv.org/abs/1207.5654v1)，
[原始 TeX 来源](https://arxiv.org/src/1207.5654v1)。
本章直接应用原 Lemma 1 以及 Theorem 1 证明中 `eq:expansion1` 的 $k=1$ 情形。
原定义是独立 Bernoulli 变量在总数等于整数均值后条件化；
要求总方差 $d\to\infty$，结论及余项对行指标一致。
当前原始后验精确具有该表示，校准满足全 $M$ 行均值和为 $q$、$cq\le d\le q$。

对照原系数，$c_2-c_1=(1-p_i)(p_i-\overline{\overline p})$，
故所用包含概率修正的符号为正：
$\pi_i=p_i+p_i(1-p_i)(p_i-\overline{\overline p})/d+O(d^{-2})$。
这里 $d$ 与加权均值均取全行校准，不是选中组窗的方差或先验信号占比。
原 Section 4.1 的固定阶累积量、删除坐标及 Edgeworth 证明也已核对；
Bernoulli 二阶以上累积量由总方差一致控制，特征函数的正弦平方包络支付外频尾部，
因而适用于本章变化的数组，毋须每个生成概率有正的统一下界。

原后续高阶相关应用中的 $N/d$ 有界条件不属于上述 Lemma 1 的一阶应用；
本章允许 $M/d\to\infty$。原累积量引理的字面陈述包含一阶，
而其证明单列一阶为均值和；本章只使用二阶及以上的方差阶结论。
此前记录的任意正幂高阶相关命题边界仍不用于本章。
该一阶包含概率公式是 Hájek 路线上的经典结果，不作为本项目的新一般抽样定理。

修正后每个实际中心的误差为 $O(C_jq^{-2})$，原数组给
$\sum_jd_jC_j^2\le Cq^3Q^{-7}$，故完整算术距离为
$O(q^{-1/2}Q^{-7/2})$。仅有 $O(C_jq^{-1})$ 的中心界不能支付同一精度预算。
新增推导是此经典修正与完整非线性周期商式的连接，包含同一残差噪声标记、
非大组惊讶及原物理输出必须保留的共同相位平移。

Simon Ruetz、Karin Schnass，*Bounds for matrices of inclusion probabilities in rejective sampling*，
[arXiv:2212.09391v2](https://arxiv.org/abs/2212.09391v2)，
[原始 TeX 来源](https://arxiv.org/src/2212.09391v2)。
核对原定义、Comparison bound 引理及 Operator norm and semi-definite order bounds 定理。
比较引理要求生成权重之和等于样本数；矩阵定理控制同一固定权重条件 Bernoulli 设计的包含概率。
它们不提供由实际 pair/path 数据生成的共同权重在模一意义下的细尺度概率律。
本章未用矩阵界填补这个反集中缺口。

另一归约直接复用 Recovery 卷式 (26.16) 的二行删除关系，再作一次有限初等对称多项式展开，
得到共同精确 $p_*,\tau_*$ 和有界非负系数的二次余项。
原确定分数逼近与共同补偿步长使该余项在每个 $\beta>1/2$ 的完整算术距离下趋零。
这条路线不依赖拒绝抽样渐近展开，也不把两个共同后验量视为可独立干预或独立抽样。
有限指数族协方差恒等式只描述形式似然干预，实际数据中的合法变动及其概率仍需另证。

两份指定版本的原始源码已读；有界关系检索还筛到条件 Poisson 极限定理、调查抽样集中和
有理函数反集中相关摘要，但未检查其原定理，故不作为正文前提。
原计数与好事件来自第 68 章及既有校准结果；实际依赖行的概率范围保持不变。
搜索未命中直接可用的经验中心模一律不意味着该结果不存在，也不认证全局原创。

## 第 119 章：条件中心化矩与后验信息方差的二阶响应

新增正文研究同一原始计数后验、紧物理输出和正噪声 $L=\ln(1/\sigma)\to\infty$、$\limsup L/Q^3<c_q/2$ 下的信息方差响应。输出、中心、完整群组、先验和固定总数约束均与第 117 章相同。所得是普通数学中的绝对 $o_{\mathbb P}(1)$ 误差公式，不作 Lean 核验或全局原创声明。

### Goodman：二阶导数需要额外的 Fourier 控制

Jesse Goodman，*Asymptotic accuracy of the saddlepoint approximation for maximum likelihood estimation*，arXiv:[2005.11028v3](https://arxiv.org/abs/2005.11028v3)。版本与此前条目一致，arXiv 版本日期为 2022-01-24，正文题页日期为 2022-01-25；本条补充该文 Theorem 6(b) 与 Appendix H（印刷页 51–52）的适用范围。

Theorem 6 的标准渐近制度为固定 iid 参数化 $K=nK_0$，并带局部识别性及非退化最大似然条件。其第二部分除结构条件 (2.30) 外，把 (2.10) 的导数控制加强为 $k\le2,\ 1\le k+\ell\le7$ 及 $k=3,\ \ell\le4$。Appendix H 明确重新控制被积函数和尾项的二阶导数，并把辅助余项的精度提升到均匀 $o(n^{-4})$，由此建立二阶连续可微性。它并非从已有一阶误差直接求导。

这些条件和 MLE 结论不直接涵盖增长维、经验系数、随尺度收缩噪声及固定总数计数后验。本章复用其成熟的导数化 Fourier 方法，在原始有限阵列上另证共同频率包络、标准化方差的两阶消去及混合空间导数；不套用未经验证的 iid 一致常数。原有版本日期差异及提取限制保持此前条目的范围。

### Kolassa–Li：同一条件分母下的鞍点反演

John Kolassa 与 Jixin Li，*Multivariate saddlepoint approximations in tail probability and conditional inference*，Bernoulli **16**(4), 2010, 1191–1207，DOI [10.3150/09-BEJ237](https://doi.org/10.3150/09-BEJ237)，arXiv:[1011.5775v1](https://arxiv.org/abs/1011.5775v1)，版本日期 2010-11-26。

该文以固定维 iid 向量的样本均值为起点，条件事件固定部分充分统计量。正文第 2 节说明解析变换与鞍点设置；条件反演比值 (4.1)、Lemma 4.1 的完整 Watson 引理证明及分母关系 (4.3) 将条件尾概率化为同一鞍点附近的分子分母近似，格点情形另用 (4.8)。其相对 $O(n^{-1})$ 近似在文中给定的固定维紧集与正则条件内使用。

该结果既不提供增长维计数阵列的 Rényi 阶数二阶导数，也不保证稀有条件事件下的中心化信息矩。本章只借用“分子分母须在同一条件实现上共同控制”的经典结构，不把原始固定总数后验直接认作 iid 充分统计量模型。完整原始 PDF 为 18 页，正文条件及引理证明可读；提取产生字体编码警告，因此不宣称无损提取或可视化核验。

### 本章补足的联合估计

记 $A_y$ 为同一乘积计数 escort 中的模态信息与测量似然信息之和，$m_Q\le C\delta^{-4}$，$M_Q=1+m_Q+\delta^{-2}$，$\mathcal D$ 为总数电荷。正文建立

$$
\mathbb E|A_y-\mathbb EA_y|^4\le CM_Q^2,
\qquad
\mathbb E[(1+\mathcal D^2)(A_y-\mathbb EA_y)^2]\le CM_Q.
$$

第一式由同一条件 Fourier 反演中的复 Gaussian 累积量和中心化均值差给出，随后通过实际高低群组、格点舍入和稀有分母传回完整乘积计数律。第二式使用同一输出下的电荷矩，不能由分别可达的边缘最优值拼接。

固定总数修正 $\ell$ 满足 $|\ell|\le C\delta^5(1+\mathcal D^2)$、$\ell\le C\delta^5$。其对数配分函数二阶导数精确等于两个条件方差之差；先中心化，再应用上述联合矩界，得到 $O(\delta^5M_Q)=O(\delta)$。这一步提供原始选择修正的二阶精度，未中心化的 $\delta^5m_Q^2$ 界则不能趋零。

有限配分函数累积量恒等式、Gaussian 平方变换、Stirling 估计、Fourier 反演与协方差恒等式均属经典；本章贡献是这些方法在原始计数和固定总数模型中精度足够的组合验证。结论保留完整经验鞍点导数、非中心项与有限噪声，不覆盖零噪声、半指数等号、无界物理输出或更高阶累积量。固定间隙周期项消失仍未解决。

## 第 120 章：共享后验参数、实际条件交换与算术反集中的边界

第 120 章有两个部分结果：完整周期泛函的实际中心可在所需算术精度下换成 $C_j\operatorname{logistic}(\operatorname{logit}p_*+jh_Q)$，其中 $p_*$ 是同一个精确固定总数后验包含概率；原始 pair/path 观测给出精确条件交换律及其最大片概率界。原固定间隙目标 $\mathfrak J_x\to0$ 仍未证明。

### Boistard–Lopuhaä–Ruiz-Gazen 的二点展开

*Approximation of rejective sampling inclusion probabilities and application to high order correlations*，arXiv:[1207.5654v1](https://arxiv.org/abs/1207.5654v1)，版本及原始条件同第 118 章归因。Theorem 1(ii) 在固定 $k=2$、总 Bernoulli 方差 $\mathcal D_x\to\infty$ 时给出

$$
\pi_{ab}=p_*^2\left[1-\frac{(1-p_*)^2}{\mathcal D_x}
+O(\mathcal D_x^{-2})\right].
$$

这里 $p_*$ 是两个等分数锚点的实际包含概率。共同校准的条件 Bernoulli 表示保持原全部行与总数约束，且 $\mathcal D_x\asymp q$。结合 $\tau_*-p_*(1-p_*)=-\operatorname{Cov}(X_a,X_b)$，该经典展开直接提供 $O(q^{-1})$ 的 susceptibility 修正；不把它当作新增的一般拒绝抽样定理。均匀性来自相同数组的固定删除展开，不把后续相关性应用中的 $N/d$ 有界条件加进原问题；旧版本一阶累积量表述的边界仍保留，只使用二阶以上累积量控制。

### Schofield–Bonner：约束保持与非负纤维连通不同

Schofield 与 Bonner，*Connecting the Latent Multinomial*，arXiv:[1504.04566v1](https://arxiv.org/abs/1504.04566v1)。原文定义 $\mathcal F_y=\{x\in\mathbb Z_{\ge0}^d:Ax=y\}$，说明一个整数核的格基可能在逐步移动时要求经过负坐标，因此不保证连接非负纤维。Markov 基须在所有相关纤维内连接任意两点，且每个中间点仍非负。

其特殊存在定理要求配置矩阵只含 0、1，并包含单位矩阵的全部列；这些条件没有被假定适用于本章 $(Q,P)$ 计数交换。正文从原模型直接导出 $n$ 的可行集是连续整数区间，邻步 $(Q,P,-Q,-P)$ 连接整个指定纤维，并给出

$$
\Pr(n\mid\mathcal F)\propto
\binom K{k^\circ+nQ}\binom L{l^\circ+nP}.
$$

因此引用用于区分“保约束”与“有正确条件分布的连通移动”，不向原模型导入未经验证的 Markov 基或计算效率结论。

### Barbour–Braunsteins–Ross：占位局部极限定理的额外条件

Barbour、Braunsteins 与 Ross，*Local limit theorems for occupancy models*，arXiv:[1908.00251v2](https://arxiv.org/abs/1908.00251v2)。原始版本的通用定理先要求整数值 $W,W'$ 组成近似 Stein 耦合 $(W,W',G,R)$。令 $D=W'-W$、$\sigma^2=\operatorname{Var}W$，还须控制

$$
\Upsilon=\mathbb E\bigl[|GD(D-1)|S_2(\mathcal L(W\mid\mathcal F_2))\bigr],
\qquad T=|\mathbb E(GD\mid\mathcal F_1)-\mathbb E GD|.
$$

定理要求 $\max\{\Upsilon+1,\|R\|_2,\sigma^{-1}\|T\|_2\}\le c_1$；局部距离还需 $q_0=\lceil\log\sigma\rceil$ 阶矩 $\sigma^{-1}\|T\|_{q_0}\le c_2$ 及 $c_1+ec_2<\sigma/2$。此处 $\sigma$ 是该定理中目标的标准差，不是正文测量噪声。相应结论为平移 Poisson 近似；不能直接转成非线性共享中心的模 1 反集中。

本章没有验证上述条件用于完整周期商，故不应用该局部极限定理来证明原算术目标。其实际一维交换坐标由明确阶乘比给出对数凹率 $c/Q$，再以真实正则纤维上的归一化得到 $O(Q^{-1/2})$ 的最大片概率与 Gaussian 尾。原始源包是单个 gzip 压缩 TeX，须按该格式读取；此前一般 tar 读取失败不构成原文不可得。

### 原始概率律与保留的缺口

第 17 章精确转移核的每个奇偶类上补偿系数总和为零。固定整段奇偶记录后，路径各时刻的标签条件独立，两个符号的行计数阵列分别为 multinomial；行计数内部仍因固定总数而依赖。pair 的同类分解同样成立，但两实验的符号槽数分布不同，未据此宣布实验等价。

对两个真实同类行，固定池掩码、外部标签和线性不变量后得到上述精确条件交换律。真实类的选择只服务于固定支持下的证明，不是观察者已知隐藏支持的算法。共享锚点概率沿同一纤维是 $L_u^\circ e^{nh_Q}+L_v^\circ e^{-nh_Q}$ 的分式线性函数；其系数、全总数归一化、变化的直方图都被明确保留。分母正不蕴含导数分子有定量下界，单个固定行对也不以高概率落在选定计数线上。

因此新结果是实际模型中的共同参数与合法条件概率接口；没有证明完整周期商的坏参数数目为 $o(\sqrt Q)$，也没有以人工相位先验、多个独立边缘最优值或标量局部极限替代该联合义务。普通理论文本，不作形式核验、全局原创或固定间隙已闭合声明。

## 第 121 章：条件单标量惩罚与后验信息三阶累积量

新增正文在原始计数后验、紧物理输出及 $L=\ln(1/\sigma)\to\infty$、$\limsup L/Q^3<c_q/2$ 下，给出后验信息三阶中心累积量的输出响应。完整经验鞍点、非中心项、计数多重度、固定总数和有限噪声均保留；实际 pair/path 结论分别成立，并对确定支撑一致。它不是环境累积量或输出平均，也不从第 119 章的 C2 误差直接求导。

### Siripraparat–Neammanee：直接复用逐点局部误差

Tatpon Siripraparat、Kritsana Neammanee，*A local limit theorem for Poisson binomial random variables*，ScienceAsia **47** (2021), 111–116，DOI [10.2306/scienceasia1513-1874.2021.006](https://doi.org/10.2306/scienceasia1513-1874.2021.006)。原出版 PDF 的 Theorem 2（印刷页 112）与完整证明（114–115）对独立、可异参数的 Bernoulli 和，在总方差 $d>1$ 下给出统一绝对局部误差 $O(d^{-1})$；不要求 iid 参数或固定项数。出版 PDF 可取得，文字提取存在字体编码警告，精细根号符号不全部清晰；本章只使用条件与证明可辨的粗阶数。

原始校准总数均值恰为整数 $q$，完整方差 $d_{\rm all}\asymp q$，互补方差 $d_c\asymp q$。中心分母是 $(2\pi d_{\rm all})^{-1/2}(1+O(q^{-1/2}))$。将互补和的逐点误差除以该中心质量，就得到第 121 章的

$$
\sup_k|L(k)-L_0(k)|\le Cq^{-1/2},\qquad
L_0=e^{\ell_0}e^{-\varepsilon\mathcal D^2},\qquad
\varepsilon=\frac{B^2}{2d_c}=O(\delta^5).
$$

支持外的 Gaussian 密度由 $d\le m,N-m$ 另给指数尾界，所以不把原文有限支持上的上确界误读成未说明的全整数断言。这里的独立 Bernoulli 是同一实际数据纤维上的校准表示，不是对实际路径行独立性的假设。

### 固定总数文献与不能移用的高阶范围

Hélène Boistard、Hendrik P. Lopuhaä、Anne Ruiz-Gazen，*Approximation of rejective sampling inclusion probabilities and application to high order correlations*，[arXiv:1207.5654v1](https://arxiv.org/abs/1207.5654v1)。该版本的 arXiv 印记为 2012-07-24，TeX 页脚为 2018-11-02；二者不强行归一。Theorem 1 及完整证明给固定阶纳入概率的 $d^{-1}$ 展开与 $O(d^{-2})$ 余项。第 3 节若干调查统计量结论另需 $\limsup N/d<\infty$，不能直接用于 $M\gg q\asymp d_{\rm all}$ 的本模型。

原 Proposition 1 字面上的“任意正整数幂”版本不作依据：均匀选取偶数 $N$ 中的 $N/2$ 个对象时，每个 $\pi_i=1/2$；三个不同指标各取平方，乘积恒为 $1/64$，而 $d=N/4\to\infty$。这只排除该版本的字面高幂用法，不裁决修正版本，也不是本章原始模型的反例。固定阶纳入概率定理及一阶中心乘积的适用范围与这一限制分开保留。此次使用的完整原文及证明可读，但提取含字体警告。

第 119 章已核对的 Jesse Goodman [arXiv:2005.11028v3](https://arxiv.org/abs/2005.11028v3) Theorem 6(b)/Appendix H 是带加强导数条件的 iid 鞍点 C2 结论；Kolassa–Li [arXiv:1011.5775v1](https://arxiv.org/abs/1011.5775v1) 的条件比值与 Lemma 4.1 是固定维条件反演。这些是成熟方法来源，均不提供增长维完整计数阵列的 C3 控制。

### 本章补足的共同条件估计

对 $0\le u,v\le2$、$1\le\alpha\le2$ 和 $k\le3$，幂与对数插入 $u^\alpha(\log u)^k$ 的统一 $1/2$-Hölder 界将逐点误差变为 $O(q^{-1/4})$，包括 $u=0$。因此无须对尾部可能极小的 $L$ 作未经控制的取对数近似。该误差直接积分于同一输出条件律，保持指数精度。

余下惩罚通过同一条件 Fourier 积分中的单标量 Gaussian 电荷处理。精确插入因子为

$$
(1+2\alpha\varepsilon\mathfrak v)^{-1/2}
\exp\!\left[-\frac{\alpha\varepsilon\mathfrak m^2}
 {1+2\alpha\varepsilon\mathfrak v}\right].
$$

分母实部至少为 1；总电荷方差及前三阶导数一致有界，均值由原始非中心量控制。求导前先积分这一标量结构，使广延信息波动在同一输出下的连接三阶累积量中抵消，得到选择修正的 C3 范数 $O(\delta^5)$。原始高低计数组、格点舍入、稀有条件分母与噪声宽度的三阶插入另有指数精度控制，不能仅由弱收敛或 C2 误差得到。

由有限配分函数的精确符号，后验信息三阶累积量满足

$$
C_{3,x}(y)-C_{3,x}(0)
=\sqrt\delta\,t'''_1y
 +\frac\delta2\left(\frac1{W_\alpha}\right)'''_{\alpha=1}y^2
 +o_{\mathbb P}(1).
$$

导数作用于同一实际纤维的完整有限经验鞍点。经典累积量恒等式、单秩 Gaussian 积分和 Fourier 方法不作新定理归属；新增内容是其在原始固定总数、稀有噪声输出模型中精度充分的组合。未断言第四阶或全阶结论、复阶配分函数无零域、无限输出区间、半指数等号、期望熵或全球原创性。

## 第 122 章：真实原始重分配与固定间隙的算术消失

第 122 章证明第 116 章的充分算术条件在原实际数据中成立：对每个固定非零谐波，精确全后验中心的最小对偶能量超过 $Q^2$ 的概率趋于一。随后复用第 116 章的完整商式、惊讶与噪声标记、正质量及全输出尾部，得到每个固定有限间隙 $\Delta_Q\to D$ 下的原后验信息方差加权 $L^1$ 极限。完整有限减项、精确输出均值与原始固定支撑量词保留；不另加相位独立或经验扭转假设。

### Boistard–Lopuhaä–Ruiz-Gazen：局部展开必须足以支付消去

Hélène Boistard、Hendrik P. Lopuhaä、Anne Ruiz-Gazen，*Approximation of rejective sampling inclusion probabilities and application to high order correlations*，[arXiv:1207.5654v1](https://arxiv.org/abs/1207.5654v1)。原 Lemma 1 的证明、标记为 Petrov/def:fm 的局部 Edgeworth 展开及 Bernoulli 累积量递推，给出本章所需的固定整数偏移结构。对整数均值 $n$、方差 $d\to\infty$ 和固定有界整数 $s$，本章使用

$$
\Pr(N=n+s)=\frac1{\sqrt{2\pi d}}
\left[1+\frac{\kappa_4}{8d^2}-\frac{5\kappa_3^2}{24d^3}
-\frac{s^2}{2d}-\frac{\kappa_3s}{2d^2}+O(d^{-2})\right].
$$

正文通过同一 Bernoulli 变换 $|\varphi(t)|\le e^{-2d\sin^2(t/2)}$，以及固定阶 $\kappa_m=O_m(d)$、$m\ge2$，明确核对所需一致余项。偶次项积分给上述系数，奇次虚部在对称区间消去。原文累积量引理字面的“任意正整数阶”不能用于第一阶均值；其正确的二阶及以上范围在这里足够。后续调查统计量所需的 $M/d$ 有界条件没有移入这个局部计算。

完整相对余项 $O(d^{-2})$ 是关键：相邻质量的 Turán 差首项为 $P_0^2/d$。若只有各项未控制的 $O(d^{-1})$ 相对误差，便不能从它们的差宣称该正首项。局部展开是成熟工具，本章不把这一通用展开命名为新定理。该原版本的其它高幂及日期边界仍按此前条目保留。

### Yaming Yu：初等对称多项式与分式线性导数

Yaming Yu，*On the inclusion probabilities in some unequal probability sampling plans without replacement*，[arXiv:1005.4107v2](https://arxiv.org/abs/1005.4107v2)。原始 TeX 的引言、Theorem 1 与第 2 节相应证明，使用严格正权重的拒绝采样纳入概率

$$
\pi_i(n)=\frac{\alpha_i e_{n-1}(\alpha_{-i})}{e_n(\alpha)}.
$$

将本模型似然按共同和归一化后，此式直接适用；齐次性使共同归一化因子消去。原文的分式线性函数导数含负 Turán 行列式，其严格性归于 Newton 不等式。Theorem 1 的主结论是不同样本量和采样方案的 majorization 关系，不提供导数下界或真实经验环境的反集中。

本章在同一完整固定 $q$ 归一化中排除两条可变行与一条中央锚，记其余行的初等对称系数为 $F_s$，两行乘积为 $B$、和为 $z$。精确新归约是

$$
\frac{dp_*}{dz}=\frac{L_0(BV-U)}{Z(z)^2},\qquad
U=F_{q-1}^2-F_{q-2}F_q,\qquad
V=F_{q-2}^2-F_{q-3}F_{q-1}.
$$

Newton 不等式给 $U,V>0$，但导数仍在唯一 $B_*=U/V$ 处为零。该平衡点不能用“严格负依赖”略去。外部校准与足够精度的局部展开进一步给 $\ln B_*=2\ln B_0+o(1)$，才允许用原始池总数的反小球界排除它。

### Borcea–Brändén–Liggett：负依赖不代替实际环境混合

Julius Borcea、Petter Brändén、Thomas M. Liggett，*Negative dependence and the geometry of polynomials*，[arXiv:0707.2340v2](https://arxiv.org/abs/0707.2340v2)。原文的实稳定／Newton 讨论及 strongly-Rayleigh-implies-CNA+ 定理证明，把稳定生成多项式与在条件化、外场和投影下保留的负关联联系起来。本章只用其框架辨明经典归属与适用边界：条件标签分布的负依赖不意味着原始路径环境独立，更不自动给后验中心的模一反集中或定量导数尺度。该文不是本章算术概率界的额外前提。

上述两个原始源码均可取得：Yu 版本是含 TeX 的归档，Borcea–Brändén–Liggett 版本是单 TeX 压缩源码。原始命题条件可直接核对。先前 Ruetz–Schnass、Markov-basis 与占据 Stein-coupling 文献保留各自矩阵、连通性和光滑度限制，未宣称它们覆盖本章非线性后验相位。

### 原始实现与足够精度

对每个固定真实支撑预先选两条信号行。原路径在给定整个奇偶记录后，标签槽按第 120 章的精确分解产生；再给定两行池与外部标签，正、负计数分配为两个条件二项律。固定负分配后，正分配 $k$ 每步改变常数得分，同时保留所有外部行、共同两行似然乘积及合法路径。实际最大分配原子为 $O(Q^{-3/2})$，没有把后验参数干预冒充原始数据操作。

在真实概率趋一的共同事件上，排除平衡点后，中央锚概率的相邻步长至少为 $q^{-1}e^{-CQ^2}$，整个值域却至多为 $C/q$。中央组大小 $n_0\asymp q/Q^3$，其相位步长与共振宽度之比至少为

$$
cq^{1/2}Q^{-11/2}e^{-CQ^2}\longrightarrow\infty.
$$

每个固定谐波只留下有界多个可能共振的真实分配；转折点及至多两个中央组成员变化另行支付。乘以实际二项最大原子后，坏概率趋零。所有相位、组大小、精确中心与比较方差来自同一条件纤维。其他组的变化仍在第 116 章的完整周期泛函中，未冻结为独立背景。

这种实际反集中连接关闭固定有限 $D$ 的算术缺口，但不证明趋零 $\sigma\mathcal B$、增长谐波族、零噪声、双根同步或阈值锐利性。经典局部展开、Newton 不等式、二项集中与 Poisson 求和各保留其归属；新增部分是原始模型中足够精度的共同实现与返回。结论属普通数学，不作 Lean 核验或全球原创性声明。

## 追加：固定总数选择的一阶响应与归一化信息谱抵消

对应理论卷第 123 章。这里辨认的是原始完整计数后验相对于同一精确标量下乘积计数比较律的输出响应。保留实际经验系数、完整取整、固定大小支持先验与有限 Gaussian 噪声，令 $\varepsilon_Q=B^2/(2d_c)$。在原严格半指数噪声范围、$\alpha\in[1,2]$ 及紧物理输出上，新增连接是

$$
R_\alpha(y)=\varepsilon_Q\sqrt\delta\,y
 +o_{C^3_\alpha,\mathbb P}(\varepsilon_Q\sqrt\delta),
\qquad
\Gamma_\alpha(y)=-\alpha R_\alpha(y)+\alpha R_1(y)
 =o_{C^3_\alpha,\mathbb P}(\varepsilon_Q\sqrt\delta).
$$

首项在固定数据纤维上与阶数无关，故归一化时消去。有限噪声仍有依赖阶数的空间得分修正，其范数多一个 $\sigma^2$ 因子；这里不把所有有限修正判为零。Shannon 熵、信息方差、三阶中心惊异累积量及闭阶数区间上的 Rényi 熵结论均只比较输出增量，不比较完整后验或无条件熵。

直接使用的成熟恒等式是 Bradley Efron，*Tweedie's Formula and Selection Bias*，作者托管原稿：[完整 PDF](https://efron.ckirby.su.domains/papers/2011TweediesFormula.pdf)。该原稿 22 页，完整文件 SHA256 为 `af27a444711d8d8c775ff8e6e3a19f7af32efe003fdb6ea9014af9782f2754c9`。原文 (1.2)–(1.4) 及 (2.1)–(2.8) 的完整指数族推导给出

$$
\mathbb E[U\mid U+N=h]
 =h+\eta\,\partial_h\log g(h),\qquad N\sim N(0,\eta),
$$

其中噪声独立、方差已知，先验可含原子。原稿归功于 Robbins (1956) 所记录的 Tweedie 公式。本章直接代入潜变量为高计数组的总能量、观测为 $V+\sqrt\delta y$、方差为 $\eta=\delta\sigma^2/\alpha$。该潜变量具有所需有限矩，Gaussian 卷积为正且光滑。原文后续对数凹性用于另一项条件方差比较，不是这里条件均值公式的前提。

这里的方差约定由原文明确的 $N(\mu,\sigma^2)$ 模型 (1.2)、第 2 节的累积母函数 $\sigma^2\eta^2/2$ 和公式 (2.8) 共同确定。公式的三阶阶数导数、稀有输出分母与随维度变化的统一界不由 Efron 的一般恒等式自动提供：第 123 章以精确倾斜密度、Fourier 多项式插入和原始计数桥另行支付。

相关条件系综原文是 Yu-Chen Cheng、Hong Qian、Yizhe Zhu，*Asymptotic Behavior of a Sequence of Conditional Probability Distributions and the Canonical Ensemble*，[arXiv:1912.11137v4](https://arxiv.org/abs/1912.11137v4)，该版本标注 2020-12-28，49 页；PDF SHA256 为 `b198c3044f47f8efd33958da4e3a1d046c452f12acf57e02829731379b6a0de4`。核对范围为 §§3.1–3.2、定理 3.1/3.2 的完整条件与结论及 §4.1.1 的条件密度与 Taylor 展开开头，不宣称核对全部 49 页证明。文中的收到／接受日期是占位符，不据其推断日期。

其定理 3.1 在固定非负子系统变量具有有限二阶矩、尺度 $\beta_n\to0$ 的条件下，对加性总量落在移动／缩放区间的条件律给出 KL 误差 $O(a_n+b_n)$，$a_n=\beta_n^2\mathbb EX^2$。它另外要求储库区间概率及其对数的统一二阶空间导数界 (3.10)、正区间概率下界与有界非负对数导数 (3.11)、相对渐近独立误差 (3.12)，以及总量区间概率正下界 (3.13)。定理 3.2 再加入条件离散到连续近似 (3.26)，给出加性点概率误差。

这些定理不直接支付本章在稀有点输出下、趋零多项式尺度上的三阶阶数导数；区间概率下界和加性 KL／TV 近似不能替代这里的同一输出密度比及插入矩控制。条件系综提供相关结构和研究路线，本章没有宣称已完成其一般定理的全部映射。上述来源与条件比较不构成全球原创性认证。

完整选择比的 Poisson–binomial 局部极限定理继续使用第 121 章已核对的 Siripraparat–Neammanee，*ScienceAsia* 47 (2021)，111–116，定理 2。独立异质 Bernoulli 与方差条件对应于同一校准总和及补集总和。Boistard `1207.5654v1` 的高次幂与版本边界继续保留，未用于本章新增响应证明。

单秩 Gaussian 行列式、条件指数倾斜、Fourier 插入、Taylor 积分余项及有限配分函数微分均属经典工具。新增内容是原实际模型中非中心电荷平方减能量的定量界、原始计数的同输出转移、$\varepsilon_Q\sqrt\delta$ 首项及归一化抵消的联合推导。零噪声、半指数等号边界、非紧输出、更大阶数及原始数据全平均均未纳入。

## 追加：增长谐波带的一致算术阻尼与缩带宽的全输出极限

对应理论卷第 124 章。在原始固定参数、完整取整、全计数组和固定大小支持先验下，取每个固定 $0<\gamma<3/2$，令 $\rho_Q=\sigma\mathcal B\asymp Q^{-\gamma}$。新增的实际重分配估计在同一个原始数据好事件上同时控制 $N_Q=\lceil1000\rho_Q^{-1}\sqrt{\ln Q}\rceil$ 个谐波，失败概率为 $b_Q+C(N_Q+1)Q^{-3/2}+2e^{-cQ}$，其中 $b_Q\to0$ 只支付一次。它与固定物理输出处的两阶归一化实倾斜、近乎平坦的正分母及全输出尾界结合，得到原完整选中后验的加权 $L^1$ 信息方差极限。所有有限经验系数与积分项 $C_xm_x$ 均保留。

Sergey G. Bobkov、Arnaud Marsiglietti，*Local limit theorems for smoothed Bernoulli and other convolutions*，[arXiv:1901.02984v1](https://arxiv.org/abs/1901.02984v1)，[原始 TeX](https://arxiv.org/src/1901.02984v1)。原始源文件 SHA256 为 `71e4c9e7979e47115de02d7576220b8ff1c6546f596c7891adcaf87d646e8ccd`，解压 TeX 为 `9ec21f4a97e55ca707be47a9dab7788eb74c2ae4dc9e5fae254c15c37c9a6de8`。使用范围为定理 1.1、1.2、7.1 的模型、完整假设与结论。

其模型是 $(X+X_1+\cdots+X_n)/\sqrt n$，其中 $X_i$ 为独立对称 $\pm1$ 变量，独立平滑变量 $X$ 的律固定。以 $f$ 表示 $X$ 的特征函数，$L^2$ 正态密度收敛要求每个非零谐波上的 $f(\pi k)=0$；定理 1.1 的充分方向另有有限一阶矩和 $f'$ 平方可积条件。定理 1.2 对一致密度收敛要求有限一阶矩及 $f'$ 绝对可积。定理 7.1 假设平滑密度连续且有界变差、有限二阶矩，并要求 $f,f',f''$ 可积，结论保留周期振幅 $A_n$ 乘 Gaussian 密度，误差为 $O(\log n/\sqrt n)$。

这项经典结果说明 Gaussian 平滑本身不能保证格点混叠消失。其固定平滑分布、线性和与对称独立 Bernoulli 模型不同于本章的二次三角数组、共同经验中心及固定总数选中律；它不直接给出本章的两阶惊异标记、随 $Q$ 缩小的噪声或原始模型反例。

Cong Ling、Laura Luzzi、Jean-Claude Belfiore、Damien Stehlé，*Semantically Secure Lattice Codes for the Gaussian Wiretap Channel*，[arXiv:1210.6673v3](https://arxiv.org/abs/1210.6673v3)，[原始源码](https://arxiv.org/src/1210.6673v3)。源归档 SHA256 为 `6b179025d930b7bdb5f15172f805d5ca19df7e151e3305c3aceda2848ec8af84`，`Security_arxiv.tex` 为 `2d62936a3af9625665d7125700e59baf443445b78cbb53afee00f97e348de72d`。核对范围为第三节的 flatness factor 定义、表达式命题及完整 Fourier／Poisson 证明、对偶格推论、smoothing parameter 定义，以及离散 Gaussian 二阶矩引理。

小 flatness factor 同时控制实密度比的上下界，提供这里在除法之前支付分母的经典关系。该文离散 Gaussian 二阶矩引理还要求改变 Gaussian 宽度后的 flatness 界，误差带明确的 $\varepsilon/(1-\varepsilon)$ 因子。单独的 $C^0$ 平坦性不能推出本章需要的两阶温度导数；编码及随机格系综的存在结果也不等于这里实际经验相位的阻尼。第 124 章保持同一残差和外围惊异—能量关系，直接对精确 Poisson 模求导并求和。

固定总数选择与实际重分配所用的局部 Poisson–binomial／Turán 估计沿用第 122 章已核对的 Boistard–Lopuhaä–Ruiz-Gazen `1207.5654v1`，只使用有界偏移下的 $O(d^{-2})$ 相对精度。Yu `1005.4107v2` 的包含关系、Newton／Turán 归属及 Borcea–Brändén–Liggett `0707.2340v2` 的负相依边界仍保持原范围，不推出原 path 行独立。带中心惊异的有符号质量界与共同通道收缩复用第 111 章；Gaussian 核心全输出极限复用第 101 章纯参考部分，不延用其受旧噪声范围限制的实际量化耦合。

新增的联合推导给每个固定 $\gamma<3/2$ 的充分范围。$3/2$ 来自条件二项最大原子与谐波并集的费用；这里不把它称为原模型的必要阈值，也不主张端点、零噪声、任意实输出上的点态一致收敛、原始数据全平均或全球原创性。

## 追加：精确噪声修正后的二阶选择响应与条件电荷四阶矩

对应理论卷第 125 章。在原始固定总数选择律、同一经验中心与标量、完整计数乘法重数以及严格半指数噪声范围内，保留第 123 章精确定义的 $\mathcal N_\alpha(y)$，得到

$$
R_\alpha(y)=\varepsilon\sqrt\delta\,y+\varepsilon\mathcal N_\alpha(y)
 -2\alpha\varepsilon^2V\sqrt\delta\,y
 +o_{C^3_\alpha,\mathbb P}(\varepsilon^2\sqrt\delta).
$$

这里 $\varepsilon=B^2/(2d_c)$ 与 $V$ 均为有限精确经验量。归一化信息谱扣除精确噪声响应后，二阶项为 $2\alpha(\alpha-1)\varepsilon^2V\sqrt\delta\,y$。相应 Shannon 熵与信息方差的输出增量系数分别为 $-2$ 和 $4$，该尺度的第三惊异累积量系数为零。上述比较仅针对两种律的输出增量差，保留原 pair/path 概率及固定支持上一致的量词，不推出无条件熵或完整后验相同。

Bradley Efron，*Tweedie's Formula and Selection Bias*，[作者原稿](https://efron.ckirby.su.domains/papers/2011TweediesFormula.pdf)，完整 PDF SHA256 为 `af27a444711d8d8c775ff8e6e3a19f7af32efe003fdb6ea9014af9782f2754c9`。第 2 节 (2.1)–(2.8) 的指数族推导给出，若潜变量 $E$ 与 $N\sim N(0,\eta)$ 独立，卷积密度为 $g$，则

$$
\mathbb E[E\mid E+N=h]=h+\eta(\log g)'(h),\qquad
\operatorname{Var}(E\mid E+N=h)=\eta+\eta^2(\log g)''(h).
$$

本章令潜变量为高计数 Gaussian 总能量，保留正的有限噪声方差与同一完整鞍点。该能量有所有固定阶矩，Gaussian 卷积为正，微分可由核函数支配。原文后续的对数凹性比较不是这两个恒等式的前提；第 123 章所述原稿 (1.3) 展示式的方差约定边界保持不变。

Hila Manor、Tomer Michaeli，*On the Posterior Distribution in Denoising: Application to Uncertainty Quantification*，[arXiv:2309.13598v2](https://arxiv.org/abs/2309.13598v2)，2024-02-19，原稿标注 ICLR 2024，31 页；[PDF](https://arxiv.org/pdf/2309.13598v2) SHA256 为 `4a1dd5dafb17f95e4970c401258725d0b53775824de48329158955ec25db26f0`。适用内容为 §3.1 定理 1 与附录 A 的 (S1)–(S13)。对具有密度的标量潜变量、独立加性 Gaussian 噪声及合法的 Bayes 积分微分，后验中心矩满足

$$
\mu_2=\sigma^2\mu_1',\qquad
\mu_3=\sigma^2\mu_2',\qquad
\mu_{k+1}=\sigma^2\mu_k'+k\mu_{k-1}\mu_2\quad(k\ge3).
$$

其方差关系提供上述条件能量方差公式的另一经典推导。它不是电荷平方在能量观测下的条件方差定理，也不把潜变量的高阶中心矩变成信息惊异累积量。第 125 章另证非中心 Fourier 插入中的二阶与四阶修正、四次幂坐标和的 $O(\delta)$ 界，以及原始乘积计数桥，得到同一输出下 $\operatorname{Var}(\mathcal D^2)$ 的变化为 $4V\sqrt\delta\,y+o_{C^3}(\sqrt\delta)$。

Cheng–Qian–Zhu `1912.11137v4` 的条件系综定理保留第 123 章已列的区间概率、空间导数、相对独立性及离散—连续近似条件。其加性 KL／概率误差不直接提供本章稀有点输出处的三阶阶数导数与 $\varepsilon^2\sqrt\delta$ 精度。完整选择比继续复用 Siripraparat–Neammanee，*ScienceAsia* 47 (2021)，111–116，定理 2 的独立异质 Bernoulli 局部估计及第 121 章的逐点高次幂转移。

Gaussian 四阶矩、单秩积分、条件倾斜、Fourier 插入与 Taylor 积分余项均属成熟工具。新增联合推导保留实际非中心性、计数格点及稀有输出分母，并把它们的误差支付到二阶选择尺度。允许 $\sigma\to0$ 任意缓慢；只有额外假设 $\sigma^2=o(\varepsilon)$ 的推论才删去噪声修正。不主张零噪声、半指数等号边界、非紧输出、更大阶数或全球原创性。

## 追加：双池合法重分配与指数薄水平带的整数凸链

对应理论卷第 126 章。在原始 pair/path 实验的同一奇偶记录与两个标签池掩码下，两个正计数分配具有真正的联合条件二项乘积律。完整固定总数后验中心保留共同归一化，其响应可在一致 $O(q^{-2})$ 误差内写成两个双曲函数之和。排除单池平衡与两池互补这三种实际退化事件后，水平曲线具有逐层一致的有限凸／凹分片；指数薄带的整数点仍保持严格凸链的斜率次序。

相应每个谐波的坏事件费用为 $O(Q^{-2}(\ln Q)^{1/3})$，共同坏环境只支付一次。取 $N_Q=\lceil1000\rho_Q^{-1}\sqrt{\ln Q}\rceil$ 后得到每个固定 $0<\gamma<2$、$\rho_Q\asymp Q^{-\gamma}$ 的完整加权 $L^1$ 信息方差极限。原始标量、Gaussian 残差、经验中心与有限系数 $A,\Lambda,C_x,Vprior_x$ 及积分项 $C_xm_x$ 均保留。端点、必要性、零噪声及原始数据全平均不在结论内。

Imre Bárány、Nathanaël Enriquez，*Jarník's convex lattice n-gon for non-symmetric norms*，[arXiv:0911.4361v1](https://arxiv.org/abs/0911.4361v1)，[原始源码](https://arxiv.org/src/0911.4361v1)。源归档 SHA256 为 `e4547dccf51473e9df4332dbbbea5ff93e4da0329cd78e644f3c15890e2e64e6`，`BarE.tex` 为 `a77a673f7359d88af79f0c92fc30670269daa4c51a65d5febb0d9fb7718ffae2`。第 2 节的 increasing slope construction 与主定理处理固定凸紧单位体、原点在内部的范数，以及极点互异的整数凸多边形。相邻边方向互异，最小周长具有 $n^{3/2}$ 量级。v1 引言印为 $n^{3/3}$，后续主定理明确使用 $n^{-3/2}L_n$；本章使用自行列出的粗整数边向量计数，不依赖该引言常数或极限形状结论。

Ryan Schwartz、József Solymosi、Frank de Zeeuw，*Simultaneous Arithmetic Progressions on Algebraic Curves*，[arXiv:0910.0904v3](https://arxiv.org/abs/0910.0904v3)，[原始源码](https://arxiv.org/src/0910.0904v3)。源归档 SHA256 为 `0f10a77936028fe0e4826f291b20345406ae72789e5d784876b6a4643c4f0117`，`sap.tex` 为 `39d42c930fa3fb2fac054e1f8cbc23b020bc9c74062188247874fc1af196c1b0`。第 3 节的定理及第二证明将无一次因子的实代数曲线分成有限条凸／凹、单调曲线，再用 Jarník 的长度—格点估计得到 $C_d k^{2/3}$ 上界。

本章的双曲余弦变换不保留整数网格，因而没有直接套用该代数曲线定理。正文在原计数坐标中证明分片数、曲率分子系数下界及薄带取整后的斜率严格次序，再由互异整数边向量的总长度得到 $O(W^{2/3})$。经典 1926 年原文未据此宣称已核对；这里使用上述原始现代论述和显式初等证明。

Ralph Howard、Ognian Trifonov，*Bounding the number of lattice points near a convex curve by curvature*，[arXiv:2207.09532v1](https://arxiv.org/abs/2207.09532v1)，[原始源码](https://arxiv.org/src/2207.09532v1)。源归档 SHA256 为 `7f1d382525ec23db2f019d1cf634b212c25c13e2c77d5bba921575a962f4ae1c`，主 TeX 为 `7b3379ec81037dcca9e11b645581f28086b679b6d7cc0878b7f460f143f8f17e`。第 8 节的三角形扰动、非共线性与近开弧定理要求总曲率不超过 $\pi$，曲率半径满足 $R_1\le\rho\le R_2$；对格间距 $d_{\mathcal L}$、余体积 $A_{\mathcal L}$、弧长 $L$ 和带宽 $h$，还要求

$$
h<\frac{d_{\mathcal L}^2}{2(R_2+d_{\mathcal L}+\sqrt{(R_2+d_{\mathcal L})^2-d_{\mathcal L}^2})},
\qquad A_{\mathcal L}/2-Lh-3h^2/2>0.
$$

其上界为 $2+L/[R_1(A_{\mathcal L}-2Lh-3h^2)]^{1/3}$；引言的相应版本还列出 $h<R_1$。仅代入本章粗略的指数曲率半径界不能得到所需多项式点数。因此正文另外证明薄带投影位移远小于曲率下界，保持整数点本身的凸链结构后使用经典边向量计数；一般近曲线定理本身不承担最终后验结论。

第 122 章的 Boistard–Lopuhaä–Ruiz-Gazen `1207.5654v1` 有界偏移局部展开提供 $O(d^{-2})$ 相对精度。Yu `1005.4107v2` 与 Borcea–Brändén–Liggett `0707.2340v2` 的包含关系与负相依边界不变，不据它们制造独立实际行。第 124 章的带标记 Poisson 展开、归一化实倾斜、条件商式及全输出截断按新的 $\rho_Q^{-1}\le CQ^2$ 费用逐项回接。

新增内容是同一原始实现上的双池条件律、精确响应、退化概率、定量曲率和指数薄带整数计数的联合证明，以及更小带宽下的完整后验极限；不主张新的普适 Jarník 定理、全球原创性或最优带宽阈值。

## 追加：固定阶条件电荷累积量与精确低阶扣除

对应理论卷第 127 章。保持完整计数乘法重数、同一原始中心与标量、实际 pair/path 律、固定支持上一致的概率以及严格半指数噪声范围。对每个预先固定的整数 $m\ge3$，同一乘积计数条件律下电荷平方的累积量满足

$$
\Delta\kappa_{m,\alpha}^Q(y)
=2^{m-1}m!V^{m-1}\sqrt\delta\,y+o_{C^3_\alpha,\mathbb P}(\sqrt\delta).
$$

精确扣除低阶有限计数累积量后，选择响应为 $(-1)^{m+1}2^{m-1}\alpha^{m-1}\varepsilon^mV^{m-1}\sqrt\delta\,y+o_{C^3_\alpha,\mathbb P}(\varepsilon^m\sqrt\delta)$。三阶时，归一化信息谱残差为 $-4\alpha(\alpha^2-1)\varepsilon^3V^2\sqrt\delta\,y$，对应 Shannon 熵、信息方差及第三惊异累积量的系数依次为 $8,-24,24$；这些是精确低阶扣除后的输出增量差，不是未扣除量的首项。

C. Vignat、S. Bhatnagar，*An extension of Wick's theorem*，[arXiv:0709.1999v1](https://arxiv.org/abs/0709.1999v1)，2007-09-13，[五页原稿](https://arxiv.org/pdf/0709.1999v1) SHA256 为 `272bf54cc581dbbb782abcc5e14854732c9c216892a6a84e9622cc3ec9d17606`。第 1 节陈述中心 Gaussian 向量的配对公式；第 2–3 节讨论球面对称性、椭圆分布与均匀球面方向，球面公式的归一化因子为 $\Gamma(n/2)/(2^r\Gamma(r+n/2))$。其证明使用各向同性 Gaussian 的方向与半径独立，再以半径的 $2r$ 阶矩除去 Gaussian 配对和。

第 127 章的数组各向异性且非中心，条件事件是能量加正噪声等于给定输出；没有均匀球面方向或独立半径前提，因此不直接套球面定理。所用中心配对恒等式是经典工具，复参数版本由收敛 Gaussian 积分及有限系数恒等式支持。新的估计分别支付坐标碰撞 $O(\delta)$、非中心偶次修正 $O(\delta^6)$ 与条件能量噪声，才得到固定阶矩比较。原稿第 4 节在协方差尺度与倒数尺度的混合表示之间存在约定差异，本章不使用该节固定归一化。

Jani Lukkarinen、Matteo Marcozzi，*Wick polynomials and time-evolution of cumulants*，[arXiv:1503.05851v2](https://arxiv.org/abs/1503.05851v2)，[29 页原稿](https://arxiv.org/pdf/1503.05851v2) SHA256 为 `50070a6e01fabe8b0ea7bc3cfad441c2392c29b51a210435fbe9a4869fac5148`。arXiv 版本戳为 2017-03-28，原稿首页另印 2018-08-21；这里按版本与完整哈希确定引用，不推定两日期的关系。适用内容是第 2 节重复随机变量的不同标签约定、(2.6)–(2.7) 的生成函数、(3.1) 的矩—累积量分拆以及附录 A 的有限矩递归定义。定义 3.1 与定理 3.2 明列其有限子乘积可积条件；动力学层级不用于本章。

对具有相应固定阶矩的实变量 $U$，经典逆关系为

$$
\kappa_r(U)=\sum_{\pi\in\mathcal P_r}(|\pi|-1)!(-1)^{|\pi|-1}
                 \prod_{B\in\pi}\mathbb E[U^{|B|}].
$$

每个重复变量须有独立标签，所有矩必须来自同一实际条件律。附录 A 明说省略若干一般性质的证明；此引用不声称原稿提供了省略的证明。上式也可由有限阶形式生成函数取对数得到。原始计数律具有有限支持，Gaussian 比较具有所有固定阶矩，满足这里的可积条件；没有使用随阶数增长的一致指数矩半径。第 127 章新增的是同一条件矩列表的定量比较及其原始计数转移，而非这个一般组合恒等式。

Gaussian 噪声的条件能量恒等式继续引用第 123、125 章已列 Bradley Efron 的 *Tweedie's Formula and Selection Bias* 第 2 节 (2.1)–(2.8)，以及 Hila Manor、Tomer Michaeli `2309.13598v2` 定理 1 与附录 A (S1)–(S13)。对潜能量 $E$、独立 $N\sim N(0,\eta)$ 和正卷积密度 $g$，配方直接给出

$$
\mathbb E[e^{zE}\mid E+N=h]
=e^{zh+\eta z^2/2}\frac{g(h+\eta z)}{g(h)}.
$$

局部实 $z$ 的微分给出所有固定阶条件能量累积量。正方差、Gaussian 能量的矩可积性及核函数支配保证当前应用合法；原文不提供数组极限中稀有点密度的三阶参数导数界，这一部分由本章共同 Fourier 包络证明。Siripraparat–Neammanee 的异质 Bernoulli 局部估计仍仅用于第 121 章已说明的完整选择比。

本章综合经典工具建立每个固定插入次数的计数桥、混合导数界以及精确低阶扣除。噪声可任意缓慢趋零；不把一阶的 $O(\delta^6)$ 替换误差带入三阶选择尺度。不主张阶数增长、一致无穷级数、超过三阶参数导数、非紧输出、零噪声、半指数等号边界或全球原创性。

## 追加：五池条件分配与三维整数凸位置

对应理论卷第 128 章。五个预选标签池在同一实际奇偶记录和槽位掩码下给出联合条件二项乘积律。十个变化标签的固定总数后验响应具有共同的 $O(q^{-2})$ 展开。只支付一次单池乘积退化和拐点带的实际概率后，对每个分配点，五个二阶导数中至少三个同号。对有限个三坐标子集取并集，并先条件化其余两个分配，保留真实乘积概率及任意水平值的一致计数。

在强凸常数 $\kappa$ 的矩形区域内，若整数点满足 $|F(n)-c|\le h$ 且 $4h<\kappa$，则对另一整数点 $m$ 有 $\nabla F(n)\cdot(m-n)<0$，所以每个点都是其凸包的暴露顶点。本章的 $h$ 指数小于 $e^{-CQ^2}$ 曲率下界，因而可以直接计数原分配坐标中的整数凸包。边长 $O(W)$ 的三维盒中，整数凸包顶点数至多 $O(W^{3/2})$；正文给出完整的初等面法向量证明及低维退化处理。

结合三坐标最大原子 $O(Q^{-9/2})$ 和 $W\asymp Q^{3/2}\sqrt{\ln Q}$，每个谐波的坏事件概率至多 $O(Q^{-9/4}(\ln Q)^{3/4})$。共同坏环境只支付一次。保留全部十一种中心组成员数并取增长谐波并集后，得到每个固定 $0<\gamma<9/4$、$\rho_Q\asymp Q^{-\gamma}$ 的原始全输出加权 $L^1$ 信息方差极限。有限 $A,\Lambda,C_x,Vprior_x$ 以及积分项 $C_xm_x$ 保持精确。

Alex Iosevich、Krystal Taylor，*Lattice points close to families of surfaces, non-isotropic dilations and regularity of generalized Radon transforms*，[arXiv:1103.1670v3](https://arxiv.org/abs/1103.1670v3)，[原始源码](https://arxiv.org/src/1103.1670v3)。源归档 SHA256 为 `50cb2652ca1938a83df96e2773dc4a4d6f5b88a62c39dfdc316e37f9d8d060b1`，展开 TeX 为 `1c483ff1d1fd9ae1d1a5af7640a8be00b52329b3c2a89b77705f7a0e5c884123`。引言归属 Andrews 的严格凸体格点界；主定理处理固定的齐一次函数，要求离开原点有 $C^{\lfloor d/2\rfloor+1}$ 正则性、非零的两组梯度及非零 Monge–Ampère 行列式，结论为平均配对计数。对称凸体推论还要求光滑边界的 Gaussian 曲率处处非零；非各向同性版本有另行列明的准齐次指数条件。

这些假设不直接提供随 $Q$ 变化的双曲水平面及鞍形分片上一致的常数，尤其不能把指数小的曲率界代成多项式点数。第 128 章先证明整数点本身处于凸位置，再用盒内整数凸包计数；没有调用该光滑曲面定理承担原模型结论，也没有在双曲余弦变换后的非整数网格上套格点定理。

George E. Andrews，*A lower bound for the volume of strictly convex bodies with many boundary lattice points*，*Transactions of the American Mathematical Society* **106** (1963)，270–279，[DOI:10.1090/S0002-9947-1963-0143105-7](https://doi.org/10.1090/S0002-9947-1963-0143105-7)。出版信息由出版社 Crossref 元数据及上列 Iosevich–Taylor 原稿引文核对；当前出版社 PDF 请求返回 HTTP 403，未据此声称读过 1963 年原文。正文需要的三维形式由独立列出的初等证明承担：整数面原始法向量互异、面面积支付法向量长度、坐标投影给出表面积上界，再由 Euler 关系控制顶点数；低维整数凸包可加一个坐标方向整数顶点形成三维棱锥。此处不宣称新的普适凸格点定理。

Boistard–Lopuhaä–Ruiz-Gazen `1207.5654v1` 的引理 1 和第 3 节局部展开保留第 122 章已核的条件与直接 Fourier 余项证明。本章只使用固定偏移及方差发散的独立辅助 Bernoulli 和，累积量界只用于二阶及以上；不采用原文过宽的一阶累积量表述。对十标签联合响应，一次展开共同分母后才得到 $O(q^{-2})$ 精度，不能由两次 $O(q^{-1})$ 近似相减取得。

第 126 章的 Bárány–Enriquez、Ryan Schwartz–Solymosi–de Zeeuw 与 Howard–Trifonov 平面结果保持原适用边界，不提升为曲面定理。第 124 章的带标记 Poisson 级数、共同 Gaussian 残差、条件均值平方截断与全输出尾部估计，按新的 $\rho_Q^{-1}\le CQ^{9/4}$ 逐项支付。新增内容是同一原始实验下的五池精确条件结构、同号曲率有限覆盖及其完整后验回接，不主张全球原创性、端点或最优带宽。

## 追加：有限二次惩罚的条件 Laplace 变换

对应理论卷第 129 章。对完整乘积计数律 $Q$，定义辅助族 $Q_s(n)\propto Q(n)e^{-sD(n)^2}$，测量仍用原始 $T,\mu,V,\sigma$。对每个固定有限 $S$，在 $0\le s\le S$、$1\le\alpha\le2$ 及紧输出上一致，响应为

$$
R_s(\alpha,y)=\frac{s}{1+2\alpha sV}\sqrt\delta\,y
+o_{C^3_\alpha,\mathbb P}(\sqrt\delta).
$$

误差还可在 $s>0$ 时除以 $s\sqrt\delta$ 后一致趋零。这里的概率是原始 pair/path 数据概率，对确定大小支持一致。有限噪声保持为正，满足严格半指数范围，允许任意缓慢趋零。固定正 $s$ 的族是辅助模型；与原始全 $q$ 选择律的联系只在其实际 $\varepsilon=B^2/(2d_c)$ 处成立。

Eduardo Abi Jaber，*The Laplace transform of the integrated Volterra Wishart process*，[arXiv:1911.07719v3](https://arxiv.org/abs/1911.07719v3)，[42 页原稿](https://arxiv.org/pdf/1911.07719v3)，SHA256 `ac3a87176726d7f62c17de6d32084a129b4e743940c457fb0f76c4fc6ed75057`。arXiv 版本戳为 2024-07-08，首页日期为 2024-07-09；不推定二者关系。附录 A 命题 A.1 对实 Gaussian 向量 $\xi$、均值 $\mu$、半正定协方差 $\Sigma$ 和半正定惩罚矩阵 $u$ 给出经典恒等式

$$
\mathbb E e^{-\xi^\top u\xi}
=\det(I+2\Sigma u)^{-1/2}
 \exp\{-\mu^\top u(I+2\Sigma u)^{-1}\mu\}.
$$

秩一情形直接提供第 129 章实参数插入式。原稿第 2 节假定平方可积 Gaussian 过程及连续协方差；定理 2.2 的短证明使用给定过滤族后向量仍为 Gaussian 的表示。这一条件不同于本章的二次能量加噪声条件事件，不能据此宣称条件向量仍独立或 Gaussian。正文的复频率延伸由实部正定的有限 Gaussian 积分配方证明，没有把实半正定定理外推到其假设之外。

Galen Reeves，*Conditional Central Limit Theorems for Gaussian Projections*，[arXiv:1612.09252v2](https://arxiv.org/abs/1612.09252v2)，2016-12-30，[12 页原稿](https://arxiv.org/pdf/1612.09252v2)，SHA256 `d217bc5302ffc5606e2bc1d1a1c04c9d51fca4c71b83d1cadaa922620c0f16c2`。定义 1、假设 1–2、定理 1–2 与推论 3 使用独立于输入向量的 IID Gaussian 投影矩阵，误差对投影矩阵平均。第 III.B 节包含球面归约及定理 1 的证明。本章电荷方向固定，条件是能量加噪声的给定值；不存在该独立随机投影矩阵，故不直接应用其定理，也不从平均 Wasserstein 或相对熵界推出点态条件密度的三阶参数导数界。

Elizabeth Meckes，*Quantitative asymptotics of graphical projection pursuit*，[arXiv:0811.2769v2](https://arxiv.org/abs/0811.2769v2)，2009-04-20，[9 页原稿](https://arxiv.org/pdf/0811.2769v2)，SHA256 `d288854b75dc7dbf2234a3cf255496e5be97039bc13caad59003cff33c799f8a`。条件 (3) 控制确定向量的平均径向偏离，条件 (4) 控制所有方向的投影二阶矩；定理 2 对均匀球面随机方向给有界 Lipschitz 测试函数的概率界。其证明使用交换对及球面浓缩。此方向随机性在本章不成立，定理不能直接用于固定方向、非中心、各向异性数组的稀有输出条件律。两篇投影论文在此承担方法边界的归属，不承担本章定量结论。

Reeves 与 Meckes 的 PDF 文本提取分别带有 40447、48205 字节的可选 fontTools/CFF 警告；Abi Jaber 提取无警告文本，但含 NUL 与控制字形。引用以原版本及完整 PDF 哈希为准，不把文本提取的排版异常用作公式前提。Reeves 引理 15 提取中的维度或标签异常不用于任何常数。文献核查范围不等于全球原创性认证。

Gaussian 噪声的条件能量得分恒等式继续使用第 123、125、127 章列出的 Efron 与 Manor–Michaeli 原始条件。正方差卷积密度 $g$ 满足 $\mathbb E[E\mid E+N=h]=h+\eta(\log g)'(h)$；完整鞍点反倾斜后的共同位移须在两个输出相减时精确消去。各向异性条件律未被替换为均匀球面律。

本章新增推导的核心是复方差与零频方差之差的 $O_{C^3}(\sqrt\delta\,|\xi|)$ 界、沿右半平面线段的有限 Taylor 余项及共同 Fourier 包络。它们直接给 $O_{C^3}(s^2\delta+s\delta^6)$ 的函数估计；原始计数转移再支付指数误差。Jensen 在任意固定有限惩罚区间给正下界，因此不需要人为的 $1-Cs>0$ 限制。不是由固定阶矩公式的无穷求和得到。

辅助族的信息谱响应导出 Shannon 熵、信息方差与第三惊异累积量的输出增量差，系数依次为 $-2s^2V/(1+2sV)^2$、$4s^2V/(1+2sV)^3$、$24s^3V^2/(1+2sV)^4$。这些是有限计数后验的 nats 及相应幂次单位，不是原始环境方差或微观状态熵。结论不包含增长的 $S$、负惩罚、超过三阶参数导数、非紧输出、零噪声或半指数等号，也不替代第 127 章精确扣除后的更细高阶尺度。

## 追加：固定维数合法分配与全部次临界多项式带宽

对应理论卷第 130 章。对每个预先固定的维数 $d\ge3$，使用 $2d-1$ 个不交合法标签池，在同一个原始奇偶记录及槽位掩码下保留联合条件二项乘积律。曲率同号的 $d$ 个坐标通过有限覆盖取得；先条件化其余分配，再用极薄水平带中原始整数点的凸位置计数。每个谐波的坏事件概率为

$$
O_d\!\left(Q^{-3d/(d+1)}(\ln Q)^{d(d-1)/(2(d+1))}\right).
$$

给定固定 $0<\gamma<3$，先选固定整数 $d>\gamma/(3-\gamma)$，再令 $Q\to\infty$。共同退化事件只支付一次，谐波数仍为 $o(Q^3)$。完整带标记 Fourier 返回、条件均值平方截断及尾部估计给出原始全输出加权 $L^1$ 信息方差极限。有限 $A,\Lambda,C_x,Vprior_x$ 与 $C_xm_x$ 均保持精确；没有将维数改成 $d(Q)$。

Travis Dillon，*Small lattice polytopes have few vertices*，[arXiv:2606.30856v1](https://arxiv.org/abs/2606.30856v1)，[原始 TeX 归档](https://arxiv.org/src/2606.30856v1)，归档 SHA256 `0105c9a16ef613cfe79d7f37c56f9ffaf277986668652c34c599b2adc2a8477a`，完整 `main.tex` SHA256 `c34d574cdeffc2d0861319ef4cd22e6c9452f73c2f1ccb978d54a58ce69f4c0c`。全文及书目给出 Konyagin–Sevast'yanov 的面归纳路线，并把体积—顶点界归属 Andrews。对满维整数凸多面体，经典关系是

$$
v(P)\le c_d\operatorname{Vol}_d(P)^{(d-1)/(d+1)},
$$

其中常数只依赖维数。第 1–2 节的变换后面法向量、秩截断及 Hölder 组合提供证明路线；附录讨论格余体积、整数点与体积、逆转置法向量。正文只使用该经典关系，不使用后续更强的旗标计数或紧性附录。

该 v1 的若干显示步骤不能逐字照搬。以环境维数体积表述时须加满维假设；首次满秩法向量计数包含零点，权重应为 $i-d+1$；保留的面数只保证 $k-r_0\le M_*$；Hölder 后的指数是 $1-(d+2)/d^2$；平面基例须避开 $d/(d-2)$。余子式法向量需要交错符号，线性变换后的面积须保留为 $\operatorname{Vol}_{d-1}(A(F))$，不能替成原面积。这些限定在第 130 章完整证明中直接承担，保留原始来源字节及其适用边界。

正文以最大体积单形作保体积仿射归一化，再由坐标投影控制表面积；原始整数法向量的格余体积以 Bezout 和底乘高计算。对低维凸包，逐次添加原顶点加一个坐标单位向量，形成保留全部旧顶点的整数棱锥，直到满维且仍位于受控盒内。因此任意平移边长 $W$ 的盒内，处于凸位置的整数点数为 $O_d(1+W^{d(d-1)/(d+1)})$，不需要失控的子格余体积，也没有把三维 Euler 关系外推到高维。

S. V. Konyagin、K. A. Sevast'yanov，*A bound, in terms of its volume, for the number of vertices of a convex polyhedron when the vertices have integer coordinates*，*Functional Analysis and Its Applications* **18** (1984)，11–13，[DOI:10.1007/BF01076356](https://doi.org/10.1007/BF01076356)。书目由 Crossref 元数据及 Dillon 原始引文核对。出版社 PDF 路由返回 HTTP 200，但重定向正文为 cookie-error 的文章 HTML，未取得或检读 1984 年 PDF。第 128 章 Andrews 1963 原稿不可得的边界保持原状；这里的可用来源为 Dillon 原始说明及正文写全的经典证明，不声称已读不可得原文。

Iosevich–Taylor `1103.1670v3` 的原定理要求固定齐次形状、光滑性、非退化梯度及 Monge–Ampère 条件，其常数不能直接用于随 $Q$ 变化且曲率指数小的分片。第 130 章计数的是原分配整数坐标的凸包，不使用余弦双曲变换后的网格，也不把光滑曲面平均界当作当前盒界。

Boistard–Lopuhaä–Ruiz-Gazen `1207.5654v1` 的已核原始 TeX 和第 122 章直接 Fourier 证明给出发散方差下固定有界偏移的局部 Bernoulli 比。这里 $d$ 固定，因而 $[-(2d-1)-1,2d-1]$ 仍是固定偏移集。一次共同分母展开给出完整选择响应及 $O_d(q^{-2})$ 余项；不以两次 $O(q^{-1})$ 近似相减代替。所有中心组的 $4d-1$ 种成员数均保留，原始 pair/path 联合条件法则不等于独立原始行。

第 124、128 章的全输出返回按 $\rho_Q^{-1}\le CQ^3$ 逐项支付。非零半整数谐波保持物理相位、完整中心、外侧惊异标记及同一个 Gaussian 残差；先减精确先验方差，再做真实二阶参数微分与商的截断。所得积分常数仍为 $8/\sqrt3-25/6$。本章综合经典几何与原始选择律得到固定维数算术族及新的带宽充分范围，不主张全球原创性、增长维数的一致性、$\gamma=3$、必要性、零噪声或计算效率。

## 追加：次临界负二次倾斜的条件指数尾界

对应理论卷第 131 章。保持原始完整乘积计数律、中心、能量观测和严格半指数噪声范围，对固定 $\eta\in(0,1)$、有限 $S,R$，在同一数据纤维内取

$$
-\frac{1-\eta}{4V}\le s\le S,\qquad 1\le\alpha\le2,\quad |y|\le R.
$$

辅助族 $Q_s(n)\propto Q(n)e^{-sD(n)^2}$ 的输出响应仍为 $s\sqrt\delta\,y/(1+2\alpha sV)$，余项连同前三阶 $\alpha$ 导数在 $s\ne0$ 时除以 $|s|\sqrt\delta$ 后一致趋零。$V$ 及上述区间在参数求导时固定；概率是原始 pair/path 数据概率，结论对确定大小支持一致。负 $s$ 的辅助族没有被认作原始全 $q$ 选择律。

新增联合尾界由同一元组上的 $D^2\le2mE+2(\sum_j e_j)^2$ 与原始能量似然完成平方得到。固定指数权重的代价至多为 $\exp(O(Q^{7/2}))$，可由高计数单元补集的 $\exp(-cQ^4)$ 吸收。中心单元则使用正定精度矩阵及同一 Fourier 积分内的联合加权矩，支付原始计数与 Gaussian 积分的三阶导数比较。取略大的固定次临界插入 $a_+=(1-\eta/2)/(4V)$ 后，得到原始计数条件律的 $\mathbb E e^{\alpha a_+D^2}\le C$，并由余量导出加权 Gaussian 型电荷尾界。所有估计保留同一输出分母，未把有限矩收敛换成指数可积性。

Daniel Hsu、Sham M. Kakade、Tong Zhang，*A tail inequality for quadratic forms of subgaussian random vectors*，[arXiv:1110.2842v1](https://arxiv.org/abs/1110.2842v1)，[8 页原稿](https://arxiv.org/pdf/1110.2842v1)，SHA256 `25c384d7416d1b7f3938f58a970cc06220667ec8fe57271ea7da9244a98287f9`。定理 1 假设 (3) 要求对每个实向量成立的联合线性矩母函数上界；注记 2 的正二次指数矩范围为 $0\le t<1/(2\sigma_{\rm proxy}^2\|A^\top A\|)$。引理 1 由收敛 Gaussian 积分的直接配方给二次及线性插入式。这些是本章精度计算的经典背景，但该线性矩母函数假设没有自动给出原始 powered-binomial escort 或能量条件律以实际 $V$ 为精确代理方差的界。原稿 arXiv 版本戳为 2011-10-13，首页打印日期为 2024-11-27；这里不推定二者关系。

Mark Rudelson、Roman Vershynin，*Hanson-Wright inequality and sub-Gaussian concentration*，[arXiv:1306.2872v1](https://arxiv.org/abs/1306.2872v1)，[9 页原稿](https://arxiv.org/pdf/1306.2872v1)，SHA256 `70cc064b9e8149cf670e78d16ab04f26ec90ad510c54772c70a0fcaeef0f2a4e`。定理 1.1 要求独立中心化坐标及共同 $\psi_2$ 界，以算子范数和 Hilbert–Schmidt 范数控制二次型偏差。其普适常数不识别本章精确次临界余量；能量条件化后也没有坐标独立性。该定理承担方法归属，原始后验的条件指数尾界由正文另行推导。原稿 arXiv 版本戳为 2013-06-12，首页打印日期为 2019-02-25。

Julyan Arbel、Olivier Marchal、Hien D. Nguyen，*On strict sub-Gaussianity, optimal proxy variance and symmetry for bounded random variables*，[arXiv:1901.09188v1](https://arxiv.org/abs/1901.09188v1)，2019-01-26，[23 页原稿](https://arxiv.org/pdf/1901.09188v1)，SHA256 `c398f0aa1059e7651948bc2fa38052bd747d1cc7ee3dbed9d3e6caf7fb87af54`。命题 3.2 的局部累积量展开表明，真实方差充当全局最优 sub-Gaussian 代理方差须有第三累积量为零、第四累积量非正。第 4.1 节对命题 1.1 的 Bernoulli/binomial 证明使用 $p(1-p)(1-2p)$：非退化且 $p\ne1/2$ 时，真实方差不是精确全局代理方差。这限定了未条件化捷径的适用性，没有反驳本章通过联合能量似然得到的条件结论。这里不使用原稿后续最优代理方差公式的证明链。

Yingdong Lu，*Non-asymptotic concentration of magnetization in the Curie-Weiss model at subcritical temperatures*，[arXiv:2303.00227v1](https://arxiv.org/abs/2303.00227v1)，2023-03-01，[5 页原稿](https://arxiv.org/pdf/2303.00227v1)，SHA256 `aaea9ab2d39ffda9e138d91aab865545ea41c3d047ec6e3e71e41e2852466ac4`。定理 2 的条件为逆温参数 $\beta>1$、外场 $h\ne0$，结论是速率 $n$ 的平稳 Metropolis–Hastings 磁化过程的 Ornstein–Uhlenbeck 极限。这里的 “subcritical temperature” 不对应本章的秩一精度余量，故不将其扩散或局部浓缩结论用作计数能量后验的全局尾界。

Hsu、Rudelson、Arbel、Lu 四份 PDF 的文本提取分别保留 51967、53923、0、33399 字节的警告；引用以钉住的完整原稿哈希和上述可核对的条件为准。排版提取不承担公式推导。第 129 章 Abi Jaber 附录 A 的实 Gaussian 公式要求半正定惩罚；本章的负插入通过实部正定的直接配方建立。Reeves、Meckes 的独立随机投影条件仍不适用于固定电荷方向。上述范围核对不构成全球原创性认证。

结论保持固定正 $\eta$、固定有限 $S,R$ 和有限层正噪声，不跨越精度极点，不处理趋零余量、增长惩罚、非紧输出或半指数等号。辅助谱的第三惊异响应系数 $24s^3V^2/(1+2sV)^4$ 随 $s^3$ 变号；它仍是辅助计数后验的输出增量差。

## 追加：增长维数合法分配与明确近临界带宽

对应理论卷第 132 章。使用预先确定的 $d_Q=\max(3,\lfloor(\log Q)^{1/3}\rfloor)$、$2d_Q-1$ 个不交标签池和 $N=\lceil1000\rho_Q^{-1}\sqrt{\log Q}\rceil$，在原始 pair/path 数据概率下得到 $\rho_Q\asymp Q^{-3}\exp((\log Q)^{3/4})$ 的完整加权 $L^1$ 信息方差极限。维数只用于概率证明，完整计数律、原始标量、物理数组、有限中心化系数及同一个 Gaussian 残差均保持不变。

经典 Andrews 体积—顶点界沿 Konyagin–Sevast'yanov 面归纳路线，在第 130 章的满维、秩边界及变换后面积条件下给出显式常数递推。第 132 章证明 $\log c_d\le40d^2\log(d+1)$，再通过整数锥补维得到任意平移盒的 $\log L_d\le50d^2\log(d+1)$。对应来源仍为 Travis Dillon，*Small lattice polytopes have few vertices*，[arXiv:2606.30856v1](https://arxiv.org/abs/2606.30856v1)，原始归档 SHA256 `0105c9a16ef613cfe79d7f37c56f9ffaf277986668652c34c599b2adc2a8477a`，主 TeX SHA256 `c34d574cdeffc2d0861319ef4cd22e6c9452f73c2f1ccb978d54a58ce69f4c0c`。第 130 章已列明的原文索引和代数边界继续保留；1984 年出版商响应为 HTML，Andrews 原文路线返回 403，二者均未被当作已阅 PDF。

增长偏移的局部比使用发散方差 $D$、整数均值 $n$ 的独立 Bernoulli 和，在 $|s|\le D^{1/8}$ 一致给出

$$
\frac{\Pr(N=n+s)}{\Pr(N=n)}
=1-\frac{s^2+(\kappa_3/D)s}{2D}
 +O\!\left((1+|s|)^4D^{-2}\right).
$$

完整证明使用固定阶累积量、Bernoulli 的全频模界及实 Fourier 积分。Boistard–Lopuhaä–Ruiz-Gazen，*Approximation of rejective sampling inclusion probabilities and application to high order correlations*，[arXiv:1207.5654v1](https://arxiv.org/abs/1207.5654v1)，原始归档 SHA256 `258b7a04a6e18116eb0d9a8e8ae290f84b94622cc05f85bab55c546eecf9953b`，已阅 TeX SHA256 `54c68cc91f9e753e985112b4e57d09d30b57232b2c0aab0e1fc5a1bcb6842218`，提供 rejective sampling 的固定偏移方法背景。增长偏移的上述误差由正文独立给出；方差控制累积量只用于阶数至少为二的情形。

Dmitry Dolgopyat、Yeor Hafouta，*Edgeworth expansions for independent bounded integer valued random variables*，[arXiv:2011.14852v2](https://arxiv.org/abs/2011.14852v2)，[原始 TeX 归档](https://arxiv.org/src/2011.14852v2)，归档 41726 字节、SHA256 `4906383d05ec79ea719480528b372fa035b84a4d6f9b532e6f970099be9498b9`，解码 TeX 137398 字节、SHA256 `e5890655891e657c273815be51c10067884cfaa5b3cbc2fc90c0c8fe7384742a`。原文定理 `ThEdgeMN` 及三角阵定理 `IntIndThmAr` 假设独立、一致有界整数变量、发散方差和固定展开阶数。其充分模条件为 $M_N\ge R(r,K)\log V_N$；辅助 Bernoulli 数组中 $K=1$ 且 $M_N=\sum\min(p_i,1-p_i)\ge D$，满足相应非共振前提。这一对应仅属于辅助独立和，不把原始观测行或经验相位向量视为独立。

原文的 superstable 删除定义将删除数约束在一个预先固定的上界内；它不直接提供本章增长池数的一致响应。正文以一次共同条件分母展开得到 $O((m+2)^4/q^2)$ 余项，保留共同校准、所有 $2m+1$ 种中心组成员数和同一条实际历史。局部概率比的全部系数及误差由正文的实积分证明，不使用原稿中待核的二阶特征多项式系数或共振点邻域强化衰减显示式。

全部随维数增长的损失显式出现：格点常数 $\exp(O(d^2\log d))$、盒及子集覆盖 $12^d$、原子界 $C^dQ^{-3d/2}$、一次支付的 $Cm(Q^{-3/2}+e^{-cQ})$、窗口尾部 $2mQ^{-204}$ 以及成员数因子。最终算术项的对数为

$$
-(\log Q)^{3/4}+O\!\left((\log Q)^{2/3}\log\log Q\right),
$$

同时 $(m+1)N/Q^3\to0$ 保证每个成员数只需有限个候选共振水平。第 111、124、130 章的带标记密度比较、条件均值平方截断、真实参数二阶导数及全输出尾部在 $\rho_Q^{-1}\le CQ^3$ 下逐项支付，给出原始加权 $L^1$ 结论及积分常数 $8/\sqrt3-25/6$，保留精确的 $C_xm_x$。本结论不覆盖 $\rho_Q\asymp Q^{-3}$ 端点、必要性、原始环境期望或计算效率，也不作全球原创性认证。

## 追加：临界四次型电荷与原始计数的全局尾部

对应理论卷第 133 章。在原始校准乘积计数律的能量后验上施加 $a=1/(2V)-\kappa\sqrt\delta$ 的辅助电荷权重，保持完整经验 $V$、$C_2=\delta^{-1}\sum_jv_j^2$ 及原始严格半指数噪声范围。对固定紧集内的 $\kappa,y$，归一化常数的尺度为 $\delta^{-1/4}$，电荷 $\delta^{1/4}D$ 趋近密度正比于

$$
\exp\!\left[\left(\frac{y}{2V^2}-\kappa\right)z^2
                  -\frac{C_2}{4V^4}z^4\right].
$$

结论包括 Wasserstein 距离 $W_1$ 与每个固定阶多项式矩；$\kappa$ 可为负。它属于所定义的辅助后验，不将其认作原始固定大小支持先验 $P$ 的后验，不声称离散—连续全变差收敛或熵阶数导数。

Raphaël Cerf、Matthias Gorny，*A Curie–Weiss model of self-organized criticality*，[arXiv:1301.6911v3](https://arxiv.org/abs/1301.6911v3)，[原始 PDF](https://arxiv.org/pdf/1301.6911v3)，SHA256 `50481fae88774def12c174f3aae1e173de7aad7dc0c731b9c93c9f0780ea2860`；*Annals of Probability* 44(1), 444–478 (2016)，[DOI:10.1214/14-AOP978](https://doi.org/10.1214/14-AOP978)。已核对模型、定理 1、定理 2 与推论 3。其临界权重为 $\exp(S_n^2/(2T_n))$；定理 2 对固定独立同分布对称律要求密度、正指数平方矩及对某个 $p\in(1,2]$ 的卷积可积性条件。四次型极限和第四根归一化属于该经典机制。它不直接给出本章各向异性三角计数阵列、经验中心及带噪声点条件化的相对密度结论；本章的系数由自身条件能量计算取得。

Sander Dommers、Cristian Giardinà、Claudio Giberti、Remco van der Hofstad、Maria Luisa Prioriello，*Ising critical behavior of inhomogeneous Curie–Weiss models and annealed random graphs*，[arXiv:1509.07327v2](https://arxiv.org/abs/1509.07327v2)，[原始 PDF](https://arxiv.org/pdf/1509.07327v2)，SHA256 `eeffb4eae4ade6d59ab0a8176f462ba3a855afdb5784a846a2536af522da85b2`。已核对条件 2.3–2.5、定理 2.15 和第 4.5 节的临界窗口推导。其秩一自旋相互作用与经验权重条件区分有限四阶矩和重尾区间，且有限经验临界参数与其极限的差可改变窗口。第 133 章相应保留有限 $V,C_2$，但不从该自旋模型移植计数条件律。原 PDF 的 arXiv 版本戳为 2016 年 7 月 14 日，正文打印日期为 2018 年 7 月 9 日；不将二者混作同一个版本日期。

Jinho Baik、Ji Oon Lee、Hao Wu，*Ferromagnetic to paramagnetic transition in spherical spin glass*，[arXiv:1805.05630v1](https://arxiv.org/abs/1805.05630v1)，[原始 PDF](https://arxiv.org/pdf/1805.05630v1)，SHA256 `cd97d2490c3eb570b8bc6ea801115cf5461a95d6f541e16ff64d2164bd3efac3`。已核对模型、无序条件、窗口 $2\beta=J^{-1}+B/\sqrt N$、定理 1.4 与其中的积分定义。该文采用球面均匀测度、满足指定独立性与矩条件的 Wigner 无序及固定 $J>1$，研究自由能涨落。这些假设不等同于本章固定经验的各向异性 Gaussian／计数向量及带噪声能量观测；其结果未被用于把本章条件律替换为球面均匀律。

Matthias Schulte、Christoph Thäle，*Cumulants on Wiener chaos: moderate deviations and the fourth moment theorem*，[arXiv:1410.7964v1](https://arxiv.org/abs/1410.7964v1)，[原始 PDF](https://arxiv.org/pdf/1410.7964v1)，SHA256 `39712a2ccc53082b4053315635f230d72459649957751b388c1f58084acb3111`。已核对模型、定理 1 及推论 2。其固定齐次 Wiener chaos 需要规定的归一化和趋零收缩量，允许的中偏差尺度受相应累积量参数控制。这类概率中偏差结论本身不提供本章含电荷依赖非中心项和独立观测噪声的相对点密度。

正文使用条件 Gaussian 公式、秩一特征值交错、精确行列式变换、Fourier 反演和二项式尾界这些经典工具。具体连接包括：在 $D=\delta^{-1/4}z$ 条件下，能量均值移动 $\sqrt\delta C_2z^2/V^2$，而能量方差为 $2\delta C_2+o(\delta)$；负能量倾斜保留数量为 $\delta^{-1}$ 的谱块，从而得到真实密度界 $C\delta^{-1/2}\exp[-cz^4/(1+\sqrt\delta z^2)]$；最后联合支付无界电荷权重与原始似然的计数尾部，并在同一输出上比较相邻噪声宽度。有限噪声同时改变二次项和四次项，保留它们后才令 $\sigma\to0$，无需附加趋零速率。

原始 PDF 的文字提取存在字体或控制字符边界；上述归属只使用已核对的具体陈述与条件，不认证完整提取无误。四次型临界机制属经典理论；本章新增综合是完整经验中心下的全局条件密度界与原始计数回接，不作全球原创性认证。

## 追加：双符号互素投影与精确三次带宽

对应理论卷第 134 章。在原始完整计数、固定大小支持先验、精确经验中心和同一 Gaussian 测量残差下，得到 $\rho_Q=\sigma\mathcal B\asymp Q^{-3}$ 的完整加权 $L^1$ 信息方差极限；结论在原始 pair/path 数据概率下分别成立，并对确定的真实支持一致。积分结论保留完整的有限 $C_xm_x$，常数仍为 $8/\sqrt3-25/6$。

新增关系来自一个共同合法条件律：不预先揭示标签池的负分配，保留相互独立的 $k\sim\operatorname{Bin}(K,1/2)$、$l\sim\operatorname{Bin}(L,1/2)$，其中 $K,L\asymp Q^3$。原始整数 $P,Q$ 互素，所以 $Ql-Pk=h$ 固定了 $k$ 模 $Q$ 的唯一剩余类。有限循环 Fourier 反演给出剩余类概率 $Q^{-1}(1+O(e^{-cQ}))$，再乘以负分配的最大二项式质量，得到 $\sup_h\Pr(Ql-Pk=h)\le CQ^{-5/2}$。这是原始合法条件分配的计算，不将经验相位当作独立均匀变量。

Friedrich Götze、Yulia S. Eliseeva、Andrei Yu. Zaitsev，*Arak Inequalities for Concentration Functions and the Littlewood–Offord Problem*，[arXiv:1506.09034v8](https://arxiv.org/abs/1506.09034v8)，[原始 TeX 归档](https://arxiv.org/src/1506.09034v8)。归档 21269 字节，SHA256 `391fce603ab3520282b44d0cb6650da2cd676548d3b5e2ddac11e9202077059c`；解码 TeX 68969 字节，SHA256 `b53d9c2bb604600f00ad2ebecb0b09ef56456e1bfe8d04a99382dde5e57bb112`。已核对引言的独立同分布加权和设置、浓集函数、引理 1–2、凸广义等差数列定义和定理 1–2。定理 1 处理规定的复合 Poisson／无限可分律；定理 2 用系数测度到低秩凸广义等差数列的质量距离控制加权独立和。其独立性只在本章合法条件分配建立后适用。这里的重复系数为 $-P,Q$，具有明确的低秩算术结构，相应距离可为零；该逆结构界不直接给出所需的 $Q^{-5/2}$。正文独立证明全部有限循环估计，并保留原文关于仅看系数可能丢失分布信息的边界。

平面凸格点计数复用第 132 章对任意平移盒、低秩凸包和整数锥补维已给出的完整论证。经典来源及原文边界仍见第 130、132 章对应条目，包括 Travis Dillon 的 [arXiv:2606.30856v1](https://arxiv.org/abs/2606.30856v1) 及 Andrews、Konyagin–Sevast'yanov 方法；Andrews 原始路线 403 与 1984 年出版商返回 HTML 的访问边界不因本章被升级。固定偏移拒绝采样比复用第 132 章在偏移 $[-4,3]$ 的展开，来源背景为 Boistard–Lopuhaä–Ruiz-Gazen [arXiv:1207.5654v1](https://arxiv.org/abs/1207.5654v1)；本章不需要增长删除数的文献定理。

真实补偿后的分数仍含未揭示分配的误差。正文将该误差一致压到 $\exp(-\phi Q^3+O(\log Q))$，再将它付入必要薄条事件；未声称投影是后验的精确充分统计。三个合法池的曲率符号覆盖、$Q^{5/2}\sqrt{\log Q}$ 整数窗口和乘积原子界给出逐层 $CQ^{-10/3}(\log Q)^{1/3}$。对每种中心成员数保留 $O(1+|\ell|/Q^3)$ 个共振整数，联合代价为

$$
C Q^{-10/3}(\log Q)^{1/3}(N+N^2/Q^3)
=O\!\left(Q^{-1/3}(\log Q)^{4/3}\right),
\qquad N\asymp Q^3\sqrt{\log Q}.
$$

环境、窗口和拐点带的失败概率只支付一次。池仅用于原始数据概率的证明，没有从物理后验删去标签。全部密度标记使用同一个真实归一化倾斜及固定物理输出，依次验证 Fourier 绝对界、正实分母、非线性条件均值平方和全输出尾部。辅助循环 Fourier、二项式集中、凸格点与 Poisson 求和均属经典工具；新增综合为这条合法共同实现与完整原始信息方差极限的连接，不声称最优阈值或全球原创性。

## 追加：临界熵阶窗口与三阶输出响应

对应理论卷第 135 章。对第 133 章的同一完整乘积计数律和同一物理临界能量，令 $\alpha=1+s\sqrt\delta$，并对似然与插入项同时取 $\alpha$ 次幂。正文得到固定 $s,\kappa,y$ 紧集上的 $C_s^3$ 归一化极限及负对数输出比极限，四次参数为 $\kappa-s/(2V)$。原始经验 $V,C_2$、中心、全部计数重数和低计数组均保留；噪声只需原严格半指数余量，允许任意缓慢趋零。结论在原 pair/path 数据概率下分别成立，对确定真实支持一致；辅助乘积律不与完整固定总数选择律等同。

Pierre-Loïc Méliot、Ashkan Nikeghbali，*Mod-Gaussian convergence and its applications for models of statistical mechanics*，[arXiv:1409.2849v1](https://arxiv.org/abs/1409.2849v1)。原 PDF 1334322 字节，SHA256 `7bf9646716fbb2477ff2bc89359ed41e854b9ba1f9c8fae9fd22d277223d0e92`，版本日期 2014-09-09。核对第 3 节假设 (A)、(B)，命题 5 的完整高斯卷积恒等式和证明，定理 6 的紧性、极限律与 $L^1$ 剩余函数收敛等价及其证明，以及第 3.3 节定理 8 的 Rademacher 四次极限与 Laplace 证明。其整个矩母函数、局部一致 Laplace 剩余收敛和可积性条件不能由本模型的局部密度近似自动取得。该文清楚说明临界变换需要全局积分控制；它不直接给出本章同一输出下的计数律三阶导数比较。

Peter Eichelsbacher、Matthias Löwe，*Stein's method for dependent random variables occurring in Statistical Mechanics*，[arXiv:0908.1909v1](https://arxiv.org/abs/0908.1909v1)。原 PDF 426879 字节，SHA256 `a8a5a2cba871e50e5c19f8a9a5aea5f8b71ba44db07637d9200a90cf754c51a6`，版本日期 2009-08-13。核对原 Curie–Weiss 律 (1.1)、单自旋类 $\mathcal B$ 的指数平方可积性、定理 1.4(1) 和备注 1.6。定理的对称二点自旋及趋近临界温度条件给出带二次扰动的四次极限；备注允许有限层四次系数。二次扰动和四次窗口是经典内容，其 Kolmogorov 误差不能直接求三次参数导数。本模型的非齐次计数组、指定的含噪二次能量输出，以及所需相对密度精度不由该分布近似定理提供。本章不使用定理 1.4 的其余分支，也不声称核对该文全部证明。

J.-F. Bercher，*Source Coding with Escort Distributions and Rényi Entropy Bounds*，[arXiv:1109.3385v1](https://arxiv.org/abs/1109.3385v1)。原 PDF 92099 字节，SHA256 `652819d2c41b4db2aac836b5088bac8601dc31fa179e3a59767523ce21acd893`，版本日期 2011-09-15。仅采用已核对的 (1)–(3) 有限字母 Rényi 熵、Shannon 熵及 escort 概率定义，并保留原文对熵阶和另行选定 escort 参数的区分。对同一物理插入因子取幂，指数应为 $\alpha aD^2$；这属于精确有限和代数。该文的编码不等式、整数码长问题及其后续 Jensen 断言不作为本章前提。

Ronald W. Butler、Marc S. Paolella，*Uniform saddlepoint approximations for ratios of quadratic forms*，[arXiv:0803.2132v1](https://arxiv.org/abs/0803.2132v1)，Bernoulli 14(1), 2008, 140–154，[DOI:10.3150/07-BEJ6169](https://doi.org/10.3150/07-BEJ6169)。原 PDF 288450 字节，SHA256 `d46dfb6e1e10c5c608d6301dca677fe3af9f779b31c37e926e7e30725542a748`。核对固定维数的高斯二次型比值设置、类 $\mathcal C_R$、引理 5 的非中心矩母函数，以及定理 9 的单零特征值和非退化条件。其一致性是固定维数下沿支撑边缘的相对误差控制，极限相对误差一般不为零；不能当作本章增长数组的 $C^3$ 小误差定理。原文说明大部分证明另置于 2007 年技术报告，该报告未取得，故不声称核对这些完整证明。本文只以精确高斯变换作经典背景，正文独立推导所需估计。

本章的具体连接包括：重标度 $\alpha F_\alpha$ 后与熵阶无关的协方差行列式、负能量倾斜下的全局密度导数界、临界权重和同一输出约束下的联合分数矩，以及先消去共同高维因子的原始计数三阶相对误差。计数比较明确支付原输出分母的 $\sigma$ 尺度，且为 $\alpha<1$ 单独证明 escort 尾界。有限噪声下实际阶响应斜率为 $C_2/[V(2C_2+\sigma^2)]$；全局控制后才令噪声趋零，得到 $1/(2V)$。四次指数族的累积量求导公式是经典恒等式，原始计数的三阶逼近使其可用于这里的输出响应。

原件抽取警告分别为 0、183560、30442、95928 字节；损坏字形和 fontTools/CFF 警告不表示原文已被修复，定理适用范围按上述已读部分限定。正文未将未求导的有序噪声夹逼直接求导，未假定复参数下的非零区域，也未由分别最优的边缘界组合共同条件矩。不主张无缩放的熵阶导数收敛、增长参数窗口、完整相图或全局原创性。

## 追加：有限响应像与四次噪声尺度

对应理论卷第 136 章。在同一原始 pair/path 数据律和完整固定总数后验中，九个合法池的双符号互素投影产生五维薄带估计。新连接是实际后验锚点的有限响应像：一次排除总概率 $O(Q^{-3/2}\log Q)$ 的过渡区后，锚点位于十九个极窄区间；连同十九个实际组成员数，每个谐波至多保留 $3\cdot19^2$ 个候选。经典凸位置计数给每层 $CQ^{-25/6}(\log Q)^{5/3}$，从而覆盖 $O(Q^4\sqrt{\log Q})$ 个谐波。正文逐项回接完整计数、惊奇量标记、同一高斯残差、外部能量和输出尾部，得到 $\rho_Q\asymp Q^{-4}$ 下原始加权后验方差密度结论，保留精确有限系数 $C_xm_x$。

Hannah Cairo、Ruixiang Zhang，*Power loss for the Mizohata–Takeuchi Conjecture on $C^k$ convex hypersurfaces*，[arXiv:2512.08064v1](https://arxiv.org/abs/2512.08064v1)。原 source archive 33552 字节，SHA256 `423326d20e04ba18f60077604d21a6d410dee2770d13c5d6a22bad7936e439a2`；原 TeX 84199 字节，SHA256 `5aa1145d5f0e4e5e691203441550ea5c1ae56d31ab5507bf6bab12b833b0bb04`。其凸体与格点概率关联定理（TeX 标签 `thm-convex-density`）固定维数 $N$，要求 $g\in SO(N)$ 服从均匀 Haar 旋转，并对有界体积凸集给出关联点数尾界；本模型的整数投影没有这个旋转律，故不采用该概率估计。该定理及其证明已核对。

同一原件末节的 `sharplatticethm` 允许依赖尺度 $R$ 的小 $C^2$ 扰动，使曲面含有 $\gtrsim R^{n-2+2/(n+1)}$ 个缩放格点；其陈述和证明已核对。`latticethm` 的固定扰动版本另选递增整数子列，并除以任意趋无穷的损失函数，其陈述已核对。这些曲面并非本模型可实现的经验中心数组，不能当作当前统计结论的反例。论文明确区别人工扰动曲面与球面、抛物面等指定曲面。正文保留经典几何指数，新增概率节省来自精确响应像，不来自对随机旋转或可扰动曲面结论的移植。

本章实际使用的是第 132 章 (132.7)–(132.13) 的任意平移立方体凸位置整数点界，包括低维凸包的整数棱锥补全和显式 $L_d\le\exp(50d^2\log(d+1))$ 常数。经典归属仍为 Andrews、Konyagin–Sevast'yanov 及此前核对的 Dillon [arXiv:2606.30856v1](https://arxiv.org/abs/2606.30856v1) 论述；这里固定 $d=5$，不将固定光滑曲面的常数假定为随 $Q$ 变化形状的一致常数。有关原始文献的此前取得范围不因此扩大。

完整后验响应使用第 132 章的共同校准与局部 Bernoulli 比值展开，在同一整数均值处只涉及固定偏移 $[-10,9]$。其经典展开背景为 Boistard、Lopuhaä、Ruiz-Gazen，[arXiv:1207.5654v1](https://arxiv.org/abs/1207.5654v1)，适用范围沿用此前核对；只对二阶及以上累积量使用方差控制，不采用过宽的一阶累积量表述。第 134 章互素双符号投影的最大原子界来自同一条件二项律的有限循环 Fourier 反演，不是假定独立经验相位。此前 Arak [arXiv:1506.09034v8](https://arxiv.org/abs/1506.09034v8) 的确定系数独立和结论，也不直接适用于任意条件化后的非线性经验中心。

原始 signed count 比较、精确实参数归一化标记模态和尾部控制分别沿用第 111、124、132、134 章。Poisson 求和及实指数族二阶恒等式属于经典工具；本章重新支付 $\rho^{-1}=O(Q^4)$ 下的所有逆噪声因子，并保持第 101 章 (101.19)、(101.8)、(101.22)–(101.23)、(101.31) 的参考律映射。外围能量先在共同实现中平移，之后才消去外围惊奇量方差，未由普通全变差或弱极限直接转移无界矩。

非线性统计浓度论文 [arXiv:0708.4272v1](https://arxiv.org/abs/0708.4272v1) 的原 source 路径返回 HTTP 403，未采用其定理。加权 Ehrhart 多项式和附加 Riemann Hypothesis 的素点计数亦不提供本章所需的投影二项薄带概率。本章不主张检索穷尽性、全局原创性、最优噪声边界或零噪声结论；平台近似仅筛选候选层，精确曲率与完整物理后验始终保留。

## 追加：超临界介观窗口中的等权双阱

对应理论卷第 137 章。在第 133、135 章的同一完整乘积计数律上，令 $a=(2V)^{-1}+\eta_Q$，其中 $\eta_Q\downarrow0$、$t_Q=\eta_Q/\sqrt\delta\to\infty$，速度为 $v_Q=t_Q^2$。正文证明 $v_Q^{-1}\log(\delta^{1/4}Z_Q)\to V^4/C_2$、重标度电荷的等权双阱极限及所有固定多项式增长连续测试的收敛，并给出保留经验系数的 Laplace 原理。原始 pair/path 数据概率、确定真实支持一致性、固定输出紧集和原严格半指数噪声余量均保留；辅助乘积计数律不与完整固定总数选择律等同。

Van Hao Can、Viet-Hung Pham，*A Cramér type moderate deviation theorem for the critical Curie-Weiss model*，[arXiv:1709.04267v2](https://arxiv.org/abs/1709.04267v2)。原 PDF 200950 字节，SHA256 `650b110a482de2b217ed967a7cdcb0eed4c2ae7809a4d8ac6e49d3ed2ceae548`，12 页，版本日期 2017-10-30。定理 1.4 和推论 1.5 针对 Rademacher Curie–Weiss 模型的固定临界参数 $\beta=1,h=0$、$W_n=S_n/n^{3/4}$ 与 $0\le x\le n^{1/12}$，给出四次极限尾部的显式修正。其直接 Laplace 方法保留二项 Stirling 因子及实际配分函数，区别中央计数和远尾。固定临界条件与误差范围不能替代本章任意缓慢离开临界窗口的异质计数组和指定含噪能量输出。原抽取中定理 1.4 的 $F$ 尾积分与相邻分布函数记法有冲突，末尾比率表也有未采用的表述；这些公式不作本章前提，不据此静默修复原文。

Francesca Collet、Richard C. Kraaij，*Dynamical moderate deviations for the Curie-Weiss model*，[arXiv:1607.05182v2](https://arxiv.org/abs/1607.05182v2)。原 PDF 344721 字节，SHA256 `8e5bc67452b3bbc69c826f3170999a1fbd7650cec0a395b60140e4db1af4f769`，26 页；arXiv 标记 2017-01-13，标题页另印 2018-09-10，二者均保留。定理 2.7 要求 $\kappa\ge0$、$b_n\to\infty$、$b_n^4/n\to0$，温度参数为 $1+\kappa b_n^{-2}$，并假定初态已满足速度 $nb_n^{-4}$ 的大偏差原理；结论是重标度磁化路径的作用量，Lagrangian 为 $|\dot x-2(\kappa x-x^3/3)|^2/8$。第 3.3 节通过非线性生成元的紧集收敛，配合包含函数与 Hamilton–Jacobi 比较原则证明该结论。附录假设 A.14 与定理 A.17 还要求适定鞅问题、可测解律、扩展生成元收敛、初态大偏差及比较原则。该动力学模型和初态假设不提供本章静态指定能量输出下的相对密度、归一化因子或等权结论；也不由其固定临界窗口的定理 2.8 推出增长窗口结果。未把外部 Feng–Kurtz 文献当作已经独立核对的本章定理来源。

Marius Costeniuc、Richard S. Ellis、Hugo Touchette，*Complete Analysis of Phase Transitions and Ensemble Equivalence for the Curie-Weiss-Potts Model*，[arXiv:cond-mat/0410744v1](https://arxiv.org/abs/cond-mat/0410744v1)。原 PDF 314816 字节，SHA256 `5d9a3083b55b17a97d5a149bf482b6f812b910b080c6b710b78a4b88a3622009`，25 页，版本日期 2004-10-28。模型固定字母数 $q\ge3$、均匀独立先验及能量 $-\|L_n\|^2/2$；微正则条件是能量区间，取热力学极限及区间宽度趋零。定理 5.1 以微正则熵的严格支撑线、非严格支撑线和无支撑线，区别平衡宏观态上的完全、部分和不等价；引理 6.1 与定理 6.2 将其用于该 Potts 模型。它没有给出本章三角数组在极窄带噪输出下的相对密度，更不能仅据能量条件化便替换为另一个正则系综。原抽取在第 6 节区间端点出现 $u_0$ 与 $-u_0/2$ 的不一致写法，相关数值端点不采用；此前一般系综定理及第三、四节全部证明不作为已完成的独立核对范围。

高斯电荷条件化、二次型行列式、实指数倾斜、Fourier 反演、Stirling 展开、有限维 Laplace 方法和 Landau 双阱机制均为成熟方法。本章具体证明的连接是：移动实鞍点处有界的尺度化密度因子、整条电荷轴上的速度尾界、趋于一的相对反射比较，以及成本 $P(Q)e^{Cv_Q}$ 的同一输出计数回接。前者使任意缓慢发散的 $v_Q$ 不误吞 $O(\log Q)$；反射比较决定两个井的权重，不能仅由速率函数有两个零点推出。原始计数回接的指数精度先吸收多项式成本，再取自由能极限。

三份原 PDF 的抽取分别保留 78501、163547、91490 字节警告及原字形缺陷；不将成功读取等同于无瑕抽取。正文允许 $\eta_Q^3/\delta$、$\sigma^2v_Q$ 等修正绝对发散，只在速度尺度上证明其可忽略。不主张通用的未缩放前因子、有限级精确对称、阱内 Gaussian 波动、增长测试族、全局相图或全局原创性。

## 追加：共同有理响应值与五次带宽下的原始方差熵

对应理论卷第 138 章。在原完整固定总数选择律、全部组和原校准中心上，正文将 $\rho_Q=\sigma\mathcal B\asymp Q^{-5}$ 时的整段坏谐波归并为最多九个共同有理响应值，再由一个合法原始计数池的投影原子界和精确曲率控制，证明所有输出上的原始加权 $L^1$ 方差熵极限。有限经验量 $A,\Lambda,C_x,m_x$、同一个残余 Gaussian、确定真实支持的一致概率以及 pair/path 两种实际实验分别保留。这里的关键限制是共同实现中的联合事件，不是独立相位假设。

Florin P. Boca、Alexandru Zaharescu，*The correlations of Farey fractions*，[arXiv:math/0404114v4](https://arxiv.org/abs/math/0404114v4)。原源包 68766 字节，SHA256 `b56222f2e3a9aa6d69c59991aa778907404dcfbafc335a8ef0718819d8c45407`；原 TeX 46797 字节，SHA256 `2d02135d88c232a49b09cdd4c0b44e98c88494320891b381bf8f672a1b4801aa`，正文日期 2005-01-18。定义和定理 1、2 研究区间 $[0,1]$ 内确定 Farey 集合中不同元素的相关测度，按集合大小 $N_Q\sim3Q^2/\pi^2$ 归一化；相邻讨论给出二点相关函数在 $[0,3/\pi^2]$ 上为零。第 2 节开头直接使用不同分数的距离至少为 $1/(qq')\ge Q^{-2}$。本章只采用并直接证明这一整数行列式分离，不将原文平均相关定理迁移为随机经验中心的分布定理。分离对任意平移和任意大小的整数分子仍成立；相同有理值的多个非既约表示必须共同处理。原文定理 1 后注记 (i) 在给出 $0<y(A_jy-B_jx)\le1$ 后称相关分母大于等于一，该措辞不作为本章前提。核对范围为定义、定理及上述明确段落，不声称重新验证原文全部相关公式的证明。

Ayla Gafni，*Counting rational points near planar curves*，[arXiv:1401.4958v1](https://arxiv.org/abs/1401.4958v1)。原源包 8068 字节，SHA256 `c9b08e96a9e02432697676a1c193084f20ba52858a1a0eac27bac8f787081cea`；原 TeX 26462 字节，SHA256 `1bdd757ff56d4e8485516ab4fbdfbd94c5f6075951f5f095af25cc60fd271e21`。其计数是 $1\le q\le Q$ 或 $Q<q\le2Q$ 中满足 $\|qf(a/q)\|<\delta$ 的整数对，曲线定义在固定区间，$f''$ 连续且与零分离。定理 1、2 另要求 $f''\in\mathrm{Lip}_\theta$、$0<\theta<1$ 及 $\delta\ge Q^{-(1+\theta)/(3-\theta)+\varepsilon}$。核对了原始定义、定理、推论及 Selberg 多项式展开的初始证明归约。本文响应曲线随 $Q$ 变化，最小曲率可为 $Q^{-2}e^{-CQ^2}$，条带宽度则为 $e^{-c_qQ^3/2+O(\log Q)}$；未满足可以直接引用其一致计数渐近式的条件。本章以强凸性直接证明实际极薄条带内至多两个整数点，保留具体曲率与误差的比较。v1 将 $\beta<\eta$ 一侧的扩张仍写成含 $\xi$ 点导数和值的式子；该扩张不作本章依据，也不据此判定原文整个计数结论。

有理数的行列式分离、强凸性插值、条件二项分拆、有限循环 Fourier 反演、局部系数比、Poisson 求和和实指数倾斜均为成熟工具。新增连接在于：同一后验锚点的三个可能组大小和三个平台值给出九个窄区间；每个区间在整段谐波截止内只容纳一个有理值；再回到精确响应，把所有该值的谐波表示约束为一个原始计数事件。平台近似只用于定位有理值，不作为指数薄条带的误差宽度。

正文随后重新支付五次逆带宽下的完整物理回接：带标记计数密度、同一残余的前两次倾斜导数、正的真实密度分母、条件均值平方、全部输出尾部、外部能量平移以及原始固定总数选择修正。旧高维凸位置计数并非本章的新一维估计的前提。第 136 章的四次带宽结论保留；本章不主张更窄带宽、最优阈值、必要性、零噪声、原始环境期望或全球原创性。

## 追加：移动双阱内的局部高斯波动与输出中心位移

对应理论卷第 139 章。对第 137 章同一原始乘积计数后验，正文用有限经验谱、有限噪声和原物理输出定义实鞍点中心 $r_*(Q,y)$，证明符号与 $2\sqrt\eta(D-\operatorname{sign}(D)r_*)$ 联合趋于公平符号和独立标准正态分布，包括每个固定连续多项式增长测试。条件仍为 $\eta\downarrow0$、$\eta/\sqrt\delta\to\infty$ 任意缓慢、原严格半指数噪声余量和固定输出紧集；保留原始 pair/path 数据概率及确定真实支持的一致性。结论属于辅助完整乘积计数律，不声称已转移到固定总数选择律。

Daniel Gandolfo、Jean Ruiz、Marc Wouts，*Limit Theorems and Coexistence Probabilities for the Curie-Weiss Potts Model with an external field*，[arXiv:0811.2735v1](https://arxiv.org/abs/0811.2735v1)。原 PDF 293788 字节，SHA256 `0aa27573d1cf9ff818632ce875d937c92de5ccbccd8e03af7121b7b37ba618d1`，17 页；arXiv 标记为 2008-11-17，标题页另印 2018-11-03，二者保留。其模型是固定字母数的 Potts 经验向量，参数 $(\beta_n,h_n)$ 趋于固定 $(\beta,h)$。定理 3.1、3.4 和注记 3.2 使用移动极小点修正来描述高斯波动，在共存情形条件于一个指定极小点附近；所用非退化极限 Hessian 排除临界端点。定理 3.5 的共存权重另要求参数扰动为 $n^{-1}(\lambda,\nu)+o(n^{-1})$。命题 4.8 及其证明给出移动中心附近的局部 Taylor 展开和统一二次控制。这里借鉴的是成熟的证明结构：局部密度比、局部归一化及邻域外的尾部各自核验。本章维数增长、井内曲率趋零、协方差异质且能量观察宽度可指数缩小，不能直接套用上述定理。原文命题 4.8 前的极小点用语在局部与全局之间变化，不将未经核实的修补作为前提。

Yingdong Lu，*Non-Asymptotic Concentration of Magnetization in the Curie-Weiss Model at Subcritical Temperatures*，[arXiv:2303.00227v1](https://arxiv.org/abs/2303.00227v1)。原 PDF 122555 字节，SHA256 `aaea9ab2d39ffda9e138d91aab865545ea41c3d047ec6e3e71e41e2852466ac4`，5 页，arXiv 日期 2023-03-01。定理 2 针对固定 $\beta>1,h\ne0$ 的平稳 Metropolis–Hastings 磁化过程，声称 Ornstein–Uhlenbeck 型过程极限；该动力学结论不覆盖本章静态、对称、条件化的增长数组。其引理 4 的残差下界只在 $[M_1,M_2]$ 内成立，引理 5 随后的事件包含未在该步支付区间外的概率；因此本文不采用这一步浓缩推断。原抽取的 Hamiltonian、磁化归一化、SDE 与生成元、引理 6 重复表达式还存在未采用的不一致。这里保留明确的适用边界，不据此宣判原文全部结论。

两份原 PDF 的抽取分别为 45013、12732 字节，抽取警告分别为 120247、33399 字节。核对范围为第一篇的模型、定理 3.1/3.4/3.5、注记 3.2、命题 4.8 及其证明，以及第二篇的完整抽取正文；不声称复核第一篇全部证明。高斯条件化、二次型行列式、实指数倾斜、Fourier 反演、隐函数求导和多井 Laplace 方法均为成熟工具。本章新增推导是精确鞍点前因子的两次参数导数、移动尺度上的可积密度比和相对计数回接；不能对第 137 章速度尺度的误差直接求导来替代它们。

原物理输出导致 $2\sqrt\eta\{r_*(Q,y)-r_*(Q,0)\}=y/\sqrt{2C_2}+o(1)$。该局部位移在主导双阱作用量中不可见，因此仅用主导井位置不足以断言零均值局部高斯极限。正文保留精确中心后才取极限，不增加 $\eta$ 或噪声的速率限制。第 137 章结论保持原范围；本章不主张离散与连续律的全变差收敛、增长测试阶数、熵导数、全局相图或全球原创性。

## 谱边界第 140 章补充：共同残差核与精确格点局部化

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 140 章在原固定幅度、$\beta\in(1/2,1)$、原取整序列和完整选择后验中，将加权方差熵结论推进到 $\rho_Q\asymp\exp(-Q^{1/4})$。同一整数元组上的中心惊异有符号质量，经同一个残差核取得不含逆噪声的全输出比较；随后只对精确格点辅助律作 Poisson 局部化和两次实温度求导。前一步的多项式误差不被重复计入后一步的谐波体积。

Alex Dytso、H. Vincent Poor、Shlomo Shamai (Shitz)，*A General Derivative Identity for the Conditional Mean Estimator in Gaussian Noise and Some Applications*，[arXiv:2104.01883v1](https://arxiv.org/abs/2104.01883v1)。核对原始版本中的主导数定理、附录 A 的 Bayes／商求导证明，以及条件多元累积量生成函数定理和证明。主定理假设 $Y=X+N$，$N$ 是独立非退化 Gaussian，$U-X-Y$ 成 Markov 链，并要求每个输出处 $\mathbb E[\|U\|\mid Y=y]$ 与 $\mathbb E[\|U\|\|X\|\mid Y=y]$ 有限；其结论是输出 Jacobian 等于 $K_N^{-1}\operatorname{Cov}(X,U\mid Y=y)$。源文件版本为 `2104.01883v1`，原始归档 SHA256 `07cf4ec3b4ae66ea6082537e96c060baa4accb13fd0edf7f86856ff2b4b562db`，主 TeX `Camera-Ready_v4.tex` SHA256 `ad005a76dfafcfeb9688390e40137cf3a6a4cb7572f9690b41652789270c9c16`。

在本卷有限计数实验中，可以取 $X=T$、$U$ 为只依赖计数的惊异标记；但该公式含 $\sigma^{-2}$，不直接给超窄噪声下的一致估计。完整后验惊异中的 $W=s+G^2/2$ 不能直接代入这个 Markov 前提：同一残差给 $\operatorname{Cov}(W,(Y-T)^2\mid T)=\sigma^2>0$。文献的输入条件累积量和输出导数，也不同于本章在固定物理输出处取归一化惊异倾斜导数。因此它承担成熟工具归属及迁移边界，本章的固定输出方差恒等式和一致带标记估计由正文直接证明。

格点 Gaussian 的 theta 表示、实矩求导及 Gauss／Poisson 工具继续归属第 111、138 章已列的 Agostini–Amendola、Ling–Luzzi–Belfiore–Stehlé 及相关原始文献；标量平坦度不能自动提供两次导数。第 140 章保留全部原外部计数、经验中心、有限 $A,\Lambda,C_x,m_x$ 及同一测量残差，证明全频轴误差为实际别名和加上 $(1+\rho_Q^{-1})e^{-c\sqrt Q}$ 与格点正规化的更小指数项。扩大过渡宽度和 Gaussian 谐波截止后，至多九个共同有理响应事件控制所有半整数谐波，整个加权 $L^1$、条件均值平方和尾部才得以回接。

本章是已有共同核与格点方法在同一实际模型中的新组合及估计，不以有限文献检索宣称全局原创。结论分别在原 pair/path 数据概率下对规定大小的确定支持一致；没有零噪声、必要阈值、原始环境期望、任意更强窄带宽或计算效率结论。

## 追加：弱外场的双尺度响应与少数相相对估计

对应理论卷第 141 章。在第 139 章同一辅助完整乘积计数律中加入 $hD$，对每个固定 $K$、$|h|\le K\sqrt\eta$、固定输出紧集、$\eta\to0$ 以及任意缓慢发散的 $t=\eta/\sqrt\delta$，得到配分函数比 $\cosh(hr_*)\exp(h^2/(8\eta))(1+o(1))$、两侧均为相对误差的相权重，以及井内变量 $W-h/(2\sqrt\eta)$ 的条件标准高斯极限，包含每个固定连续多项式增长测试。中心始终是第 139 章保留有限经验谱、有限噪声与物理输出的精确 $r_*(Q,y)$；原严格半指数噪声余量、pair/path 实际数据概率和确定支持一致性保持原范围。该结论尚未转移到固定总数选择律 $P$。

Pierre Gaspard，*Fluctuation relations for equilibrium states with broken discrete symmetries*，[arXiv:1207.4409v1](https://arxiv.org/abs/1207.4409v1)，原 PDF 日期标记为 2012-07-18，22 页、699057 字节，SHA256 `a812cbe2520a30caa3b3012595df33b56b810d33d838c404d78897ac6a831d72`。其式 (21)–(26) 通过有限配分和中的变量替换证明精确关系 $P_B(M)/P_B(-M)=\exp(2\beta BM)$。前提是构型空间和参考和在某个对合下不变、零场 Hamiltonian 不变、观测量 $M$ 为奇函数，外场线性耦合为 $-BM$。这些对称条件适用于本文中心高斯参考积分；原校准二项数组的非中心能量、格点和重数未必具有精确反号对合，故不能据此宣称原始计数的有限精确反射律。式 (40) 的配分函数比属于成熟的指数族恒等式。

Gaspard 第 VII 节式 (106) 的陡降展开保留两个局部稳定根，式 (112) 后说明只保留一峰会丢失生成函数对称性。该方法提示必须支付少数相，但原文未给出曲率趋零、少数相质量指数缩小及窄输出条件化下所需的统一相对误差。正文另证逐侧尾界 $t^{p+1}\exp(-ct^2+C_Kt)$，再以同一输出、同一实际电荷上的加倍 $\eta$ 支配回接计数。原抽取式 (13) 的自由能导数符号与定义 (2)、(10) 及式 (15) 不一致；该未采用的表达式不作前提，也不据此裁定整篇论文。

Somabha Mukherjee、Tianyu Liu、Bhaswar B. Bhattacharya，*Moderate Deviation and Berry-Esseen Bounds in the p-Spin Curie-Weiss Model*，[arXiv:2403.14122v1](https://arxiv.org/abs/2403.14122v1)，原 PDF 日期标记为 2024-03-21，22 页、313949 字节，SHA256 `ac68117f47588982ab9bf98ea0476ca482e0934068f28161da87eeb27248479f`。其模型为固定 $p\ge3$、固定参数的齐次 p-spin Curie–Weiss 律。定理 2(2) 在共存曲线上条件于一个固定孤立极大点邻域，给出 $x\le C N^{1/6}$ 内的相对高斯尾估计；该极大点的二阶导数严格为负。定理 3(2) 给出相应的条件 Kolmogorov 界。第 4.1 节使用定理 5 的交换对工具，逐项要求有界增量、条件方差接近 1、小回归余项以及有界条件二阶矩。

上述回归系数、缩放和邻域常数依赖固定极大点的曲率，原定理未陈述曲率趋零及双阱合并时的统一性；本文也没有构造满足该交换对条件的原始多群组窄似然计数数组。因此这些相对尾定理不能直接代替本章的逐相指数可积性和计数比较。其“相对尾”与弱收敛、绝对误差之间的区别与本章少数相问题相符，但方法对应不等于已完成迁移。原抽取中严格极大点脚注与共存用语，以及式 (4.8) 前二阶矩中间表达式的符号，均不作为本章证明前提。

Daniel Gandolfo、Jean Ruiz、Marc Wouts 的 arXiv:0811.2735v1 及其版本边界见第 139 章对应归属。定理 3.5 在固定共存点附近、参数扰动为 $1/n$ 量级时给出共存权重；其固定维数和非退化极限 Hessian 不覆盖本文增长数组、消失曲率和可指数缩小的观察宽度。高斯指数倾斜、双峰 Laplace 法、双曲余弦配分因子和 logistic 权重均为成熟内容。本章 `repo-derived` 的承重补充是逐侧指数尾界、加倍 $\eta$ 的共同条件支配、相对于每一侧的完整计数比较，以及零点质量和符号切换的相对控制。

新文献核对范围为 Gaspard 的对称关系完整证明、有限配分恒等式与 Curie–Weiss 双峰讨论，以及 Mukherjee–Liu–Bhattacharya 的模型、极大点分类、定理 1/2/3 陈述和定理 2(1)(2) 的完整证明，包括所用定理 5 条件；未声称核对两文全部证明或数值例子。两份抽取分别为 57532、54139 字节，警告分别为 131747、111682 字节；不把抽取无误当作前提。已检文献未直接提供本章完整模型接口，这只是有范围的适用性判断，不是全球原创性证明。

两种外场尺度相差 $\sqrt\eta r_*\asymp t\to\infty$：$h=b/r_*$ 改变两井权重但不产生极限井内位移；固定 $c\ne0$ 的 $h=c\sqrt\eta$ 产生局部位移 $c/2$，且少数相概率为 $\exp(-2|c|\sqrt\eta r_*)(1+o(1))$。后者仍保留其自身条件高斯极限。物理输出修正满足 $h\{r_*(Q,y)-r_*(Q,0)\}=h\,y/(2\sqrt{2\eta C_2})+o(1)$，在第二尺度影响相权重的有限因子。本文不以主导中心替换指数中的精确中心，不对旧渐近误差求导，不推出增长场强、增长测试阶数、全局相图或选择律 $P$ 的结论。

## 谱边界第 142 章补充：加宽谐波带与二次 Weyl 极大估计的迁移边界

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 142 章在原固定幅度、$\beta\in(1/2,1)$、原取整序列及完整选择后验下，将加权方差熵结论推进到 $\rho_Q\asymp\exp(-Q^{3/4})$。原始相对一行／两行律给出 $|j|\le Q^{7/8}$ 上的同时占据下界；加宽的半整数带外获得足够多的逐因子 Gauss 收缩，带内则保留每个偏移处的双格能量。展开阶数和辅助双标签池固定，原数组及证明所用占据块随 $Q$ 增长。

Alex Barron，*An L4 maximal estimate for quadratic Weyl sums*，[arXiv:2011.09885v4](https://arxiv.org/abs/2011.09885v4)。核对该版本主定理、Section 2 的有理矩形构造、其调用的 Bourgain 界及相关证明段落。主定理对无权和 $\sum_{n=1}^N e^{2\pi i(nx+n^2t)}$ 给出 $L^4_x([0,1])$ 下的 $t\in(0,1)$ 极大估计 $C_\epsilon N^{3/4+\epsilon}$；这里的积分是 Lebesgue 积分。证明中的一维矩形族要求水平交叠至多二次，并按既约有理逼近分组。所引 Bourgain 界要求 $1\le q\le N$、$\gcd(a,q)=1$、$|t-a/q|\le1/(qN)$，并一致于线性变量；相应界及局部时间估计的前人成果归属沿用原文。原始归档 21,289 字节，SHA256 `0274d9a049b1fb7e1faf5a9e473f985a7b669703d40f3e26b135b72038f08a60`；所核对主 TeX 68,428 字节，SHA256 `d752aa6226520d5d2b8cf78f0b82bd0243b906ce1f0a379e7c23b86fee917e3f`。

该文的 Lebesgue 线性变量、无权有限和与本卷共同数据生成的非同分布 Gaussian 格点乘积并不相同；两阶惊异标记亦需另行处理。因此其极大定理、有理例子和下界均不直接充当本模型的估计或反例。第 142 章所需的一致收缩由有限 Gauss 和的平方差分解、Dirichlet 逼近及实 Gaussian Poisson 求和直接给出，包含偶分母和任意实中心。

Roger Baker，*Lp maximal estimates for quadratic Weyl sums*，[arXiv:2103.05555v1](https://arxiv.org/abs/2103.05555v1)，Section 2 的 Lemmas 1–3 及 Lemma 3 的证明归属承接第 106、109 章已核对材料。Lemma 3(i) 的完全和假设为 $\gcd(q,a_1,a_2)=1$，并将 $C\sqrt q$ 界归于 Estermann；奇分母的求值见其第二部分。本卷使用的正规化 $\sqrt{2/b}$ 界由差变量满足 $b\mid2ah$ 的至多两个选择直接推出，不将奇分母公式外推到偶分母。

Agostini–Amendola 的离散 Gaussian／theta 实矩关系以及 Cellarosi–Marklof 的 theta 变换保留既有归属与假设；正文不使用未证零点条件下的复 theta 对数。Dytso–Poor–Shamai 的条件导数恒等式仍受第 140 章说明的 Markov 边界约束：完整惊异中的同一残差 $G^2/2$ 必须直接求导。

第 142 章是这些工具在原始共同实现中的新组合及定量桥梁：先证明同时占据，再控制加宽带内的位移能量、同一噪声和两次实温度导数，最后支付有符号核、条件均值平方及全部输出尾部。结论分别在原 pair/path 数据概率下对确定支持一致；不声称全局原创、阈值必要性、零噪声或环境期望收敛。

## 谱边界第 143 章补充：条件乘积抽样与逐相相对比较

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 143 章将第 141 章的弱外场结果迁回原完整固定基数选择律。对每个 $\eta\to0$、$\eta/\sqrt\delta\to\infty$ 的确定序列，在原严格半指数噪声条件、紧物理输出和 $|h|\le K\sqrt\eta$ 内，保留第 139 章的精确经验中心。结论包括配分函数比、两个符号概率的相对渐近式和每相内平移后的 Gaussian 波动；任意慢的尺度分离与指数小的少数相均在原量词范围内。

Tatpon Siripraparat、Kritsana Neammanee，*A local limit theorem for Poisson binomial random variables*，ScienceAsia 47 (2021), 111–116，[DOI:10.2306/scienceasia1513-1874.2021.006](https://doi.org/10.2306/scienceasia1513-1874.2021.006)。使用 Theorem 2：独立非同分布 Bernoulli 和的总方差 $d>1$ 时，概率质量与对应正规密度在支持整数上的一致差满足随 $d\to\infty$ 的 $O(d^{-1})$ 界。这里无需方差与标签数成比例，也无需有界中心偏移。原文的误差定义、定理及证明分别位于印刷页 111、112、114–115。原出版 PDF SHA256 `1a6ec512d5621ed33bd58ff52260f80256c3ca662a73711c93a580a81628150a`。该定理分别应用于同一校准后的全部标签及外部标签，给出正文 (143.13)–(143.15)，随后稀有输出和逐相比较由本卷另行支付。

Richard Arratia、Larry Goldstein、Bryan Langholz，*Local central limit theorems, the high-order correlations of rejective sampling and logistic likelihood asymptotics*，Annals of Statistics 33 (2005), 871–914，[DOI:10.1214/009053604000000706](https://doi.org/10.1214/009053604000000706)，核对版本 [arXiv:math/0506300v1](https://arxiv.org/abs/math/0506300v1)，2005-06-15。其作者提供的电子重印本注明排版、页码与期刊不同，不作版本字节等同。所读 PDF 465,316 字节，SHA256 `48d1f6866626e807686ace55c894866fa46acdfb049a26659ed6185f749d83c5`。

Lemma 3.5 及其证明给出正权重、有限可行固定样本数下的精确条件乘积恒等式，直接对应全部标签上的校准 Bernoulli 条件化。其高阶展开不作为本章井位移的估计：Condition 2.1 要求方差至少为 Bernoulli 总数的固定正比例，Theorem 2.1 还使用有界中心偏移；本模型 $d_{\rm all}\asymp q$ 而 $q/M\to0$，井上的整数位移也无需有界。Theorem 3.1 的权重稳定性及采样比例远离零、一的条件不能替代这一稀疏模型。原文条件与 Lemma 3.5 的完整证明已核对；未将整个高阶展开路线宣称为适用。

新推导在完整计数盒上保留 $L_x(k)=\exp(\ell_0-\varepsilon D^2)+r_x(k)$ 的加性误差，避免对极端尾点取未获相对控制的对数。对同一逐相后验积分后，误差为 $O_{\mathbb P}(q^{-1/2}+\delta^5+\eta\delta^4+\delta^5/\eta)$，不含逆噪声或逆少数相概率。条件抽样、局部极限及有限换测度是成熟工具；本章贡献是它们在原完整计数、原能量、同一外部补偿与弱场下的定量连接，不宣称全局原创、增长外场范围或完整相图。

## 谱边界第 144 章补充：端点占优与驻点消失的区分

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 144 章研究原完整选择律的增长正外场 $h=\kappa m_Q\eta^{3/2}/\sqrt\delta$。对每个 $\eta\to0$、$t=\eta/\sqrt\delta\to\infty$ 的确定序列，保留原严格半指数噪声、紧物理输出和支持一致的 pair/path 数据概率。对紧集内 $\kappa>\kappa_c=(2/3)\sqrt{2/3}$，负号条件下 $-hD$ 趋于 $\mathrm{Exp}(1)$，包含每个固定连续多项式增长测试；边界阈值小于驻点消失阈值 $4/(3\sqrt3)$。有限层精确阈值、临界窗口及离散动力学亚稳态均不在结论中。

Nico M. Temme，*Uniform Asymptotic Methods for Integrals*，[arXiv:1308.1547v1](https://arxiv.org/abs/1308.1547v1)。arXiv 标记为 2013-08-07，题页为 2013-08-08。PDF 385,992 字节，SHA256 `93d3557ce4824a823e1fe2b8a3ca1e34a780ad1db46654e9af0f219a81d419a4`。Section 2.1 的 (2.1)–(2.3) 讨论零点及扇形内解析、无穷远指数增长可控的振幅与趋于无穷的大 Laplace 参数；Section 2.2 给出转成 Gaussian 积分后的 Laplace 展开条件；Section 4 开头明确指出额外参数可能影响展开的一致有效性。这里只借鉴端点渐近与参数一致性的成熟方法：本章 $h$ 无须趋于无穷，振幅随数组、有限噪声和 $\eta$ 变化，未从该文取得直接可套用的统一 Watson 公式。所需一阶结论由正文 (144.20)–(144.30) 的局部比值和全局包络证明。Temme 引向 Olver 的一般 Watson 证明未作为本章承重结论。

Paul Cuff、Jian Ding、Oren Louidor、Eyal Lubetzky、Yuval Peres、Allan Sly，*Glauber Dynamics for the mean-field Potts Model*，[arXiv:1204.4503v2](https://arxiv.org/abs/1204.4503v2)，2012-06-11。PDF 3,605,812 字节，SHA256 `5a59fb6d9219f4ae45765664fea300f0acd6dc1a0e8e50bdf392025e78fd9595`。该文完整图 Potts Gibbs 测度、单点 Glauber 转移与混合时间定义是定理的模型前提。Section 1.1 的 (1.1) 及 Theorems 1–4 区分动力学阈值和热力学阈值；Theorem 2 使用 $\beta(n)=\beta_s-\xi(n)$ 及 $n^{2/3}\xi(n)$ 描述混合时间与 cutoff，Section 1.2 解释局部自由能极小值消失的 spinodal 含义。该模型没有本章带噪能量观测及原计数选择条件，故仅作结构比较，未迁移任何混合定理。来源的模型、定理条件与自由能解释已核对，完整混合证明未承担本章推导。

本章保持原有限噪声曲率因子 $\chi_{Q,\sigma}=2C_2/(2C_2+\sigma^2)$，以在零电荷处误差为零的上界支付边界层。直接负号分子保留 $\sigma/h$ 尺度；增长外场只在同一联合估计中付出 $\exp(Ct^2)$，由原计数比较的 $\exp(-bQ^3)$ 裕量支付。最后对同一负号条件律使用第 143 章的全计数盒选择包络，误差为 $O_{\mathbb P}(\delta^5+q^{-1/2}+\delta^6/\eta^3)$，不含逆少数相概率。两场的精确负号分子比还给出正文 (144.43a) 的指数矩结论。局部极限与条件抽样文献沿用第 143 章的版本及范围；模型内连接是本章的推导内容，不宣称全局原创或完整相图。

## 谱边界第 145 章补充：稀疏类别 Poisson 比较与合法标签池放大

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 145 章在原固定幅度、$\beta\in(1/2,1)$、原取整序列及完整选择后验下，将加权方差熵结论推进到每个固定 $c>0$ 的 $\rho_Q\asymp\exp(-cQ^{3/2})$。预选的 $m=\lceil\log Q\rceil$ 个不交真实标签对只用于证明：实际数据中至少一个池落在具有固定正概率的有利矩形。随后对每个固定池，在其自身合法外部条件域下界定“坏且有利”的交集，再取有限并。不存在将事后选中的隐藏分配重新当作固定池条件律的步骤。

Federico Pianoforte、Riccardo Turin，*Multivariate Poisson and Poisson process approximations with applications to Bernoulli sums and U-statistics*，[arXiv:2105.01599v2](https://arxiv.org/abs/2105.01599v2)。核对原始 TeX 的整数向量 $\ell^1$ Wasserstein 距离、Theorem 1.1 的可积整数向量／独立 Poisson 目标／同空间耦合及 size-bias 缺陷条件，以及 Section 3.1 的类别向量假设、独立情形推论与相关应用证明。事件指标在整数 $\ell^1$ 距离下为 1-Lipschitz，因此该 Wasserstein 距离支配事件全变差。独立类别向量推论的误差为 $\sum_t(\sum_jp_{t,j})^2$；其维数依赖在求和中显式出现，不要求 Poisson 总均值保持有界。

第 145 章先条件于完整奇偶记录，再将被选中类别的每个时间槽写成取值于 $0,e_1,\ldots,e_{2m}$ 的独立类别向量。路径原始行并不独立，不能直接套用该推论；条件化后的槽位独立性来自原核的精确因子分解。逐槽比较给出 $O(m^2Q^3/M)$，奇偶频数偏差与目标均值校正另付 $O(Q^3M^{-1/3}+mM^{-1/3})$。该比较只作用于有界的“存在有利池”事件，不替换完整后验、经验中心、惊异矩或共用残差。

原始归档 17,295 字节，SHA256 `6050a143ed440fa652d8407ce0eece086cddba261c79055d0d55b0eaad97858a`；所核对 TeX 53,893 字节，SHA256 `83dc7d594e3f53a7b47e3d4d7a5a175d9bc935d66c61cbd6b603d87c9be92c9c`。该版本依赖情形证明中有一处显示式将前文 size-bias 恒等式的 $\ell_i-1$ 写为 $\ell_i-i$；这里保留这一原文缺陷的适用边界，不依赖该段。正文 (145.10) 直接计算单槽事件全变差 $p(1-e^{-p})\le p^2$，经独立最大耦合与求和得到所需界，因而不以未核验的一般 Stein 证明补足模型论证。

经典 Poisson 近似与 Stirling 不作为新内容。本章的模型内推导在于：将真实槽位联合律、有利池存在性、每个固定池的合法算术交集和同一全数组的三标签删除校准接合；再用原始相对一行／两行律证明 $|j|\le Q^{13/8}$ 上的同时占据下界，支付扩大频率带内的两阶实温度标记、位移双格能量及全部输出尾部。Gauss／Poisson、theta、Weyl 及条件导数文献保留既有归属与限制。有限检索不证明全局原创性或更强结果不存在；结论不扩张至增长 $c$、必要性、零噪声或原始环境期望收敛。

## 谱边界第 146 章补充：有限相权重、局部宽度与共存中心

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 146 章在原完整选择计数后验中，以精确有限剖面 $F(r)=\ell_y(r^2)-\ell_y(0)-hr$ 的内部最大点 $r_-$、曲率 $K=-F''(r_-)$ 定义 $\Lambda=F(r_-)+\log h+\tfrac12\log(2\pi/K)$。在有界 $\Lambda$ 和紧输出范围，负号条件律分为指数边界层与 Gaussian 内部阱，内部权重趋于 $e^\Lambda/(1+e^\Lambda)$。等高点处内部阱的宽度大于边界层，需要正向外场位移才能等权；无量纲外场 $\kappa$ 相对于精确有限等高点的位移主项为 $\log t/(m^2\sqrt{2/3}\,t^2)$。任意缓慢 $t\to\infty$、$\eta\to0$ 和原严格噪声余量均保留。

Christian Borgs、Roman Kotecký，*Surface Induced Finite Size Effects for First Order Phase Transitions*，[arXiv:cond-mat/9501074v3](https://arxiv.org/abs/cond-mat/9501074v3)。核对 Section 3.2、完整 Theorem 3.1 及 (3.5)–(3.21)。模型要求 $d\ge2$ 的有限格子、固定有限相数、匹配轮廓表示、内部与边界面上的平移不变性；轮廓权与基态能量对参数为 $C^6$，满足 Peierls 及导数界 (3.7)–(3.9)、边界偏好限制 (3.11)，且有效衰减常数 (3.17) 为正。定理保留体积、表面、边和角贡献，给出有限相自由能指数和与相应权重 (3.20)。

该文说明次主自由能对有限相权重的重要性，但没有为本卷的收缩曲率、各向异性噪声和计数后验提供可直接应用的定理。本卷没有建立满足其假设的轮廓／Peierls 表示；负电荷半轴的端点也不是该文的格子表面相，其表面位移尺度不能替换本章宽度比产生的对数位移。原 PDF 519,936 字节，SHA256 `bd64a6bbf27b3caba749ed6bf5266da597ffeaf08b555958b8f16a905c16c25a`，来源日期 1995-01-20。文字抽取含字体警告，非交叠条件的一个交集符号与散文存在冲突，未用该符号作推导前提。完整轮廓证明不在本次核对范围。

A. Fernandez、E. A. Spence、A. S. Fokas，*Uniform asymptotics as a stationary point approaches an endpoint*，[arXiv:1707.07927v2](https://arxiv.org/abs/1707.07927v2)。核对开篇 Definition 1.1、(1.1)–(1.17)、完整 Theorem 1.1、Remark 1.2 及局部／全局换元讨论。其积分具有振幅 $(1-z)^{-1/2}z^{\sigma-1/2}$、特定对数振荡相位、固定 $0<\delta<1$ 和 $1/2\le\sigma<1$、随大参数变化的指定 $\lambda$ 区间，以及 (1.4)–(1.5) 限制的复射线角度。文中的 $\delta,\sigma,t$ 与本卷参数含义不同。定理针对该积分给出驻点接近端点时的一致 Fresnel 型主项。

该文指出，换元后的振幅依赖大参数和端点参数时，需要逐模型证明一致误差。本章的两个位置按局部尺度仍相隔发散，且积分为正的数组依赖剖面，因此不导入该 Fresnel 定理或一般化的无条件误差保证。本章直接证明前因子导数和共同尾界。原 PDF 424,462 字节，SHA256 `b688475265e9ad344276baa0f86f9feea101596627710173e0e91f0c7c92f3af`；arXiv 页眉标 2018-01-02，标题页标 2021-06-13，原因未验证。抽取文本对驻点符号的叙述存在歧义，未据此建立数学前提；后续完整证明与全阶结果未作为已核验输入。

端点 Laplace、内部 Gaussian 主项、两个正贡献相加及 logistic 正规化属于经典方法。第 146 章的模型内内容是保留有限经验／噪声项的竞争坐标，以及同一实现上的导数、尾部、逐区域计数比较和完整选择修正。Temme 关于固定振幅的假设不自动覆盖当前变化剖面；Siripraparat–Neammanee 的总方差局部界与 Arratia–Goldstein–Langholz 的条件乘积表示仍按第 143 章的精确范围使用。有限文献核对不证明全局原创性，不把静态共存律称作动力学相变。

## 谱边界第 147 章补充：揭示总数后的条件核与稀有池放大

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 147 章在原始 pair/path 实验、固定参数和完整选择计数后验下，给出每条确定序列 $Q^{3/2}\le R=o(Q^2)$、$\rho\asymp e^{-R}$ 的加权方差熵极限。它先依据各池总数选池，再揭示隐藏拆分；有限分割与条件乘积积分证明所选核精确保留。试验池数满足 $\log m=o(Q)$，算术投影的 $CQ^{-5/2}$ 误差只支付一次，分离宽度 $L=10(R+\sqrt{Q^3\log Q})+20\log Q$ 支付下端点拆分尾部。

Qingwei Liu、Aihua Xia，*On moderate deviations in Poisson approximation*，[arXiv:1906.10016v2](https://arxiv.org/abs/1906.10016v2)。原始 TeX 的 main-results 部分要求 LD2 局部依赖及相应条件原子界，或指定 size-bias 耦合；结论是移位整数变量的相对 Poisson 右尾界，包含明确 Stein 因子、均值／方差调整及左尾余项。size-bias 定理及其证明、独立 Poisson-binomial 专门化均已核对。这些一维右尾结论不提供不同池的联合关系，不能逐池应用后相乘替代原始多项分布。第 147 章通过逐槽类别耦合单独证明有界事件的联合全变差界，并用精确率函数的 Taylor 积分不等式与 Stirling 下界处理增长偏移，未假定中等偏差渐近的高阶余项消失。

该版本原始归档 192,213 字节，SHA256 `64974443e8aeef6f12657d7bf2ba0d11b2bb0f30ecc40e2edaba5b24983999eb`；所核对 TeX 71,512 字节，SHA256 `b0ad6ae79ca03bfd78d97f42eeed4fc4e3a66636a11713a6b913ad55b0ce71a7`。本文不借用文中的数值图例或未迁移的相对尾近似。

Renan Gross，*Noise sensitivity from fractional query algorithms and the axis-aligned Laplacian*，[arXiv:2201.10350v1](https://arxiv.org/abs/2201.10350v1)。原文把分数查询写成乘积输入上的适应过程；除坐标鞅外，还要求每个坐标子集的乘积是鞅，停止时刻适应于已揭示信息。均匀布尔输入上的 revealment 定理控制固定 Fourier 层权重；其完整陈述与证明已核对。该条件结构启发“先选盒子、后开盒子”的描述，但真正迁移到原计数模型的是 (147.9)–(147.10) 的精确条件核，原文没有给出本模型的后验相位随机性或超窄带宽结论。

原始归档 476,635 字节，SHA256 `97504ef766713ea797a8652756c631ea9ff0c77afcb23e830da845b5fb7a4b5d`；主 TeX 101,043 字节，SHA256 `a2357a001103efc408bb013a7ca65fffed6064733474c7695b5c7c5a3441a732`。该版本轴向更新显示式把增量前状态误写为新时刻状态；插值平方展开把交叉项写成负号，而该项在所取期望下为零。这里保留这两个源文边界，不使用它们作为已验证恒等式。

经典条件分布、Poisson 近似、Stirling 与 Gauss／Poisson 求和不列作新理论。本章新增的模型内组合是总数可测的稀有池选择、无池数放大的隐藏拆分控制、原始相对行律给出的 $\lfloor Q\sqrt R\rfloor$ 占据块，以及同一数组上两阶实温度标记、有符号惊异矩、非线性条件均值平方、完整选择律与全部输出的回接。原有 Weyl、theta 与条件导数文献的限制保持：没有独立经验相位、复 theta 无零点前提或整后验 Gaussian 替换。结论限于逐序列次二次对数尺度；有限搜索不证明全局原创性或二次尺度结果不存在。

## 谱边界第 148 章补充：有限共存的首项 Laplace 修正

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 148 章在原始完整选择计数律上证明 $\log(N_P^I/N_P^B)=\Lambda+C_I-C_B+o(t^{-2})$。这里 $C_B=2\ell_y'(0)/h^2$，$C_I=F^{(4)}(r_-)/(8K^2)+5F^{(3)}(r_-)^2/(24K^3)$，均取同一实现的精确有限噪声剖面。条件包括 $\eta\to0$、$t=\eta/\sqrt\delta\to\infty$ 任意缓慢、有界竞争坐标、紧输出范围，以及原严格噪声余量。有限经验参数 $m^2=2V^4/C_2$ 无须收敛；$t^2(C_I-C_B)+37/(8m^2)\to0$。实际等质量外场比精确 $\Lambda=0$ 外场低 $37/(8m^2r_Wt^2)+o((r_Wt^2)^{-1})$。

William D. Kirwin，*Higher Asymptotics of Laplace’s Approximation*，[arXiv:0810.1700v2](https://arxiv.org/abs/0810.1700v2)，版本日期 2010-06-05。核对开篇对内部与边界极小点的区分、Theorem 1.1、Theorem 2.1 的假设及系数定义，以及附录一维首个修正系数。Theorem 1.1 要求区域包含作为内点的唯一非退化极小点、$f\in C^{N+2}$、$g\in C^N$，以及某个正参数下 Laplace 积分收敛。Theorem 2.1 改用径向渐近展开、主项正性和极小点之外的分离条件。论文明确不处理边界极小点。

其一维常振幅系数经极小值到极大值的符号转换，给出本章 $C_I$ 中的四阶项和三阶平方项。这是经典系数的归属；固定函数定理不能自动提供变化数组、收缩曲率、移动内部阱与指数窄噪声的共同余项。本章直接建立精确 Fourier 前因子的高阶导数和可积余项，不依赖逐个 $Q$ 套用固定函数定理。原 PDF 为 320,051 字节，SHA256 `fbd709d2f4fa3d08076ecc1213b42646095869ddb7b03ef9d5fe7e7743e4e7af`。文字抽取存在 CFF Type1 字体解码警告；抽取的高阶余项指数及附录高阶排版不作为数学输入。一般定理的完整证明未作为已核验或直接应用的结果。

Gergő Nemes，*An explicit formula for the coefficients in Laplace’s method*，[arXiv:1207.5222v2](https://arxiv.org/abs/1207.5222v2)，版本日期 2013-04-04。核对引言、完整 Theorem 1.1 及其证明概要，以及 Section 2 到 (2.4) 的系数推导。该文归于 Erdélyi 的 Theorem 1.1 要求唯一端点极小值、每个端点邻域之外的正间隙、端点附近 $f'$ 与 $g$ 的连续性、具有正主指数的 $f,g$ 渐近展开、可逐项求导的 $f$ 展开，以及充分大参数下的绝对收敛。证明概要以 $f(x)-f(a)$ 换元、逆转局部级数并用 Watson 引理，另行控制剩余积分区间。Section 2 解释 Perron／Wojdyło 系数表示。

本章的剖面随 $Q$ 变化，$h$ 未必趋于无穷，且另一内部阱同时贡献质量，因此不直接套用该固定端点定理。以 $x=hr$ 归一化后，本章证明共同包络及 $O(t^{-4})$ 的边界积分余项；$\int_0^\infty x^2e^{-x}\,dx=2$ 与由此得到的端点系数属于经典计算。原 PDF 为 206,643 字节，SHA256 `6d828445701d81369f3cce02747838ada8a7b159b16452619964ebc83d698840`。抽取存在字体编码警告；后续势多项式结果及所引书籍中的完整渐近证明未作为本章的定理级替代。

第 148 章的仓内推导是变化剖面的精确导数控制、同一实倾斜上的 $O(\delta^4)$ 非中心相对密度比较、相对于两个小区域各自质量的计数与完整选择误差，以及不求导未知计数余项的等质量外场反演。Borgs–Kotecký 的轮廓／Peierls 和格子条件未在本模型中建立；Temme 与 Fernandez–Spence–Fokas 的适用边界保留第 144、146 章的说明。Siripraparat–Neammanee 的异质 Bernoulli 总方差局部界与 Arratia–Goldstein–Langholz 的条件乘积表示按第 143 章使用。有限检索不证明全局原创性；以上是普通数学推导，尚未经过 Lean 形式化认证。

## 谱边界第 149 章补充：可调有理弧与细化对偶网格

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 149 章对每个固定 $c>0$，在原始确定支持上一致地证明 $\rho\asymp e^{-cQ^2}$ 下完整选择计数后验的加权方差熵极限；pair 与 path 分别使用其实际数据律。固定宏观占据块提供至少 $aQ^2$ 个因子，弧外收缩选为 $\eta=\exp[-(c+2)/a]$。分母截止 $B_\eta$ 与公共倍数 $D$ 在取 $Q\to\infty$ 前固定；全部有理弧保留精确 Gauss 权重与外部二次相位，细化对偶网格的逐坐标和为 $1+O_D(e^{-c_DQ^{3600}})$，因此没有 $D^{|J|}$ 损失。

Francesco Cellarosi、Jens Marklof，*Quadratic Weyl Sums, Automorphic Functions, and Invariance Principles*，[arXiv:1501.07661v2](https://arxiv.org/abs/1501.07661v2)。已核对原始 TeX 的上半平面 Jacobi 恒等式、Schwartz 权重和式、含两个移位的广义 theta 函数、变换公式、尖点展开及其证明，以及不变性原理的条件。本文一维因子对应 $z=2\theta+i/(2\pi d)$；复线性变量的虚部承载实均值，实部承载经验线性相位，并明确除去 Gaussian 归一化。有限有理剩余类分解后再作 Gaussian Fourier 积分，是确定性恒等式的专门化；(149.38)–(149.46) 所需两阶实温度导数和变化数组界仍由本章逐项推导。

该文的不变性原理要求实参数具有绝对连续分布，并对固定系数施加指定的无理性条件。原始计数生成的经验中心没有由本文证明这种分布，故不引入其随机过程极限、相位均匀性或尾分布。尖截断变换的条件收敛问题也不替代这里逐个有限 $Q$ 的绝对收敛 Gaussian 和。所核对原始归档 8,052,728 字节，SHA256 `6055e60c27e27a45875eba07fce12b1663380b3caf3d70e15a7de7d6096843ea`；主 TeX 179,340 字节，SHA256 `4cb9a9ee0368997043e15bb4911c825c887cb3156e24c62eff2d9ea3ecfd1fd7`。本次核对的是上述确定性接口及相关原文条件，不宣称重新检查整篇所有定理。

Kai-Min Chung、Daniel Dadush、Feng-Hao Liu、Chris Peikert，*On the Lattice Smoothing Parameter Problem*，[arXiv:1412.7979v1](https://arxiv.org/abs/1412.7979v1)。已核对 Gaussian 质量与对偶平滑参数定义、小质量缩放引理及证明、对称平移界、Voronoi 刻画及证明。平滑参数以非零对偶晶格 Gaussian 质量不超过 $\varepsilon$ 定义；缩放引理先要求原质量小于 $\varepsilon<1$，然后用非负项的幂和不等式。Voronoi 刻画适用于 Euclidean 晶格与对称铺砌单元，使用半空间 Gaussian 尾及对称平移不等式。

这些条件不直接适用于从完整计数元组到标量 $T$ 的非线性映射、复二次核或条件惊异标记。第 149 章先精确分解并作 Poisson 变换，绝对误差才成为矩形对偶网格上的正 Gaussian 和；(149.40) 直接验证精度，(149.10)、(149.41) 以正 Poisson 系数控制所有平移。未将无移位的非零质量前提静默用于任意移位网格，也未从“噪声很小”类比推出后验结论。

该版本原始 TeX 的 Voronoi 半空间定义将内积 `pr(y,y)` 误写为 `pr(y,x)`；其后证明使用正确半空间。源文还保留摘要 $\varepsilon$ 范围的编辑问题、Gaussian 尾参考文献待补注记及其他部分的重复标签。这些均不作为已验证前提。原始归档 40,685 字节，SHA256 `1a8974d60c0f6d6a0ba958f76788d8c612ef15b42c5c76facc3ead3b96c9a5a8`；提取 TeX 139,562 字节，SHA256 `20020f403a37eed90836cd697663c2ad159bb4f71b0c625ab518151658732cfd`。不引用未核对的复杂性结论或数值图例。

模型内组合承接第 68 章的相对行律、第 120、147 章的条件槽位律、第 132 章的固定偏移 Bernoulli 比、第 134 章的互素投影、第 138 章的共享有理值，以及第 101、111、142、145、147 章的带标记完整后验回接。新关系是将任意固定收缩要求、有限有理共振和同一数组的算术能量控制组合起来，同时保留两阶实导数、有符号矩、条件均值平方和全部输出。没有独立经验相位、整后验 Gaussian 替换或复 theta 无零点假设。文献方法归属与仓内综合推导分列；增长的 $c_Q$、必要阈值和零噪声仍未解决，有限搜索不证明全球原创性。

## 谱边界第 150 章补充：带标记 Laplace 积分与有限相响应

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 150 章在第 148 章的原始范围内，建立负号条件后验的电荷标记回接，并据此得到精确有限剖面的均值、方差与局部唯一敏感度峰。核心是逐区域归一化前的带标记原始计数估计；未通过求导未受控余项来获得响应结论。原始 $t=\eta/\sqrt\delta\to\infty$ 可任意慢，保留完整选择律、经验系数、同一输出与噪声的严格指数余量。

Anya Katsevich，*The Laplace asymptotic expansion in high dimensions*，[arXiv:2406.12706v3](https://arxiv.org/abs/2406.12706v3)。原 PDF 的 arXiv 版本标记为 2025 年 6 月 12 日，首页日期为 6 月 13 日，两者分别保留。已核对假设 2.1–2.3、注记 2.4–2.5（含联合尾部界 (2.8)）、定义 2.6–2.11、完整定理 2.12 和注记 2.13。假设要求唯一全局极小点、正定 Hessian、振幅的 $C^{2L}$ 与相位的 $C^{2L+2}$ 局部正则性，以及整体尾部控制。定理将带振幅积分的误差分成局部 Taylor 误差、Gaussian 截断和外部尾部；系数可由 Gaussian 期望表示，界同时依赖相位与振幅的导数。

本模型的整个负号剖面有两个竞争区域，不满足该定理对整个剖面的单一全局极小点要求。逐区域应用还须验证随数组变化的导数、振幅与尾部界。第 150 章在实际局部变量中直接证明这些界，并单独处理非中心插值、窄噪声计数单元与完整选择律。该文用于系数和方法归属，不被宣称为本模型的现成定理；其完整一般证明和后续应用章节未在此次核对中使用。PDF 757,590 字节，SHA256 `ee891c6035366249a08e23ee6ea71553466bf1aaa83788717105fdf54dda2742`；47 页提取文本 121,141 字节，提取器警告为空，但仍有控制字形与 NUL，故不宣称提取文本无损。

Christian Borgs、Roman Kotecký，*Surface Induced Finite Size Effects for First Order Phase Transitions*，[arXiv:cond-mat/9501074v3](https://arxiv.org/abs/cond-mat/9501074v3)。第 146 章已引用其相共存框架；这里进一步核对第 3.2 节、完整定理 3.1，以及第 6 节的响应、峰定位和引理 6.3 的敏感度证明至 (6.48)。定理作用于维数 $d\ge2$ 的有限格点轮廓表示，要求沿边界面的平移性质、轮廓权重与基态能量的六阶场导数、Peierls 衰减和受控边界／体能量差。有效轮廓衰减为正时，给出分配函数至六阶和混合响应至五阶的误差界。这些前提未在本噪声计数数组中建立，不能直接导入该定理。

原文 (6.7)–(6.8) 分别给出两相均值响应与敏感度；引理 6.3 用导数控制、定位和严格负的二阶导数证明峰唯一性，并给出相对于等质量中心的系数 $6$。此系数是经典有限相几何。第 150 章按 $\exp(-hR_c)$ 的原始符号约定重新由第三、第四累积量确定峰的方向，得到 $h_{\rm pk}=h_{\rm equal}^P-6/(K_Wr_W^3)+o((r_Wt^2)^{-1})$；新内容在于带标记计数回接与消失曲率下的定量控制，不在于创造该通用系数。

该 PDF 519,936 字节，SHA256 `bd64a6bbf27b3caba749ed6bf5266da597ffeaf08b555958b8f16a905c16c25a`，与此前原文逐字一致。67 页提取文本 127,604 字节，保留 446,420 字节字体编码警告；轮廓“不交叠”行仍有与文字不一致的不等号字形，本文结论不依赖该歧义。后续 Binder 累积量计算未被使用。Kirwin、Nemes 的普通内点／端点系数归属及第 143 章的异质 Bernoulli 局部概率条件保持原范围。

本章的峰是固定输出下、负号条件后验的局部峰；不声称未条件化响应、整个场轴上的唯一峰、动力学亚稳态、熵阶导数、增长参数扩展或全局原创性。精确有限中心、有限噪声和经验 $m_Q$ 先于所有极限保留，不能用极限四次剖面替代窄窗口中的场坐标。

## 谱边界第 151 章补充：增长的既约分母与原始模型的共同响应

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 151 章对每个确定的 $Q^2\le R=o(Q^3)$ 序列证明 $\rho\asymp e^{-R}$ 下完整选择计数后验的加权方差熵极限，分别适用于实际 pair/path 数据律并在确定支持上一致。分母截止满足 $\log\mathfrak b=O(1+R/Q^2)=o(Q)$；不同既约有理弧保持分离。非零弧只对指数占据块作 Gauss–Poisson 展开，零弧恢复完整连续 $J$ 参考律，全部外部二次相位、两个实标记与共用残差始终保留。

Francesco Cellarosi、Tariq Osman，*Bounds for Smooth Theta Sums with Rational Parameters*，[arXiv:2306.11119v2](https://arxiv.org/abs/2306.11119v2)。已核对原始 TeX 的引言、固定移位一致界及完整证明、共同模群轨道距离定理及证明、正则权重主定理及其证明。其和式为 $S_N^f(x;\alpha,\beta)=\sum_{n\in\mathbb Z^k}f(n/N)e^{2\pi i[(\|n\|^2/2+\beta\cdot n)x+\alpha\cdot n]}$。一般充分条件是 $m_k(\alpha,-\beta)>0$：同一模群轨道上与两个相应整数尖点集合的距离下确界为正。结论 $|S_N^f|\ll N^{k/2}$ 的常数依赖维数、该下确界、权重衰减指标 $\eta>k$、权重半范数及 $\beta$ 的平移；仅在增加 $N\ge\|\beta\|$ 后才能去掉显示的平移因子，轨道距离仍保留其依赖。

固定移位引理要求上半平面高度 $y\ge1/2$ 和 $\theta_k(\xi_2)>0$，显式常数为 $2^{(2\eta-k)/4}\sum_{n\in\mathbb Z^k}\|n-\xi_2\|^{-\eta}$。其后注记指出，移位靠近整数晶格时该常数增大。因此该文不能用作变化经验中心的无条件统一界。具体有理族要求至少一个坐标对为 $(a/(2m),b/(2m))$，其中 $\gcd(a,b,m)=1$ 且 $a,b,m$ 均为奇数；原始经验中心未被证明满足此条件。其有理分类的证明引用作者较早工作的若干命题；这些命题未被另行核验，也不作为本章模型结论的前提。

本章的对应关系先固定每条既约有理弧，在宏观占据块上精确展开二次剩余类和对偶网格，保留所有未展开坐标的精确相位。随后分别验证共同经验响应和对偶精度。分母、频率与稀有池数均增长，但不会成为原数据概率的逐项并集因子；(151.28) 把整个频带约束到至多九个有理值，(151.36)–(151.37) 则直接控制正 Gaussian 网格和。Cellarosi–Osman 的轨道界不提供这两个实际模型桥梁，也不提供惊异与噪声的两阶标记回接。

原文引言的经典 theta 定义在二次指数中印作 $\pi n^2w$，缺少通常上半平面收敛公式中的 $i$；不将该印刷式用作收敛恒等式。该版本还含编辑注释、注释掉的候选论证及 $k/n$ 记号变化，原始字节保留。这些旁注、图例、未核对的重尾分类或数值优化不作为本章前提。原始归档 3,218,923 字节，SHA256 `0603c35bd156758857c8cfae8e49df4ff0bd91d08a3b9fa6ae410ffa00aef7e3`；一致界 TeX 6,875 字节，SHA256 `97c61944cc2da89fe0f368d20010ea66cfc8ad365ca5e70766893b1d99eec796`；共同轨道定理 TeX 17,954 字节，SHA256 `8901b7227e62a199e39b88fb9f7671253003cf15b709db122cc317a0f00cd9e8`；轨道与主定理 TeX 10,553 字节，SHA256 `45699b8e99e449116e7f3cbf5c58457a02a8fc144b9a84f9d742ec55aa97c940`。

第 149 章对 Cellarosi–Marklof 确定性 theta 变换与 Chung–Dadush–Liu–Peikert 正对偶 Gaussian 质量的归属及限制继续适用。仓内新增综合是分离有理弧、按频区选择展开坐标、次立方偏移的总数可测选池、同一数组的算术估计与完整后验回接之间的连接。结论保留精确有限噪声校正和 $C_xm_x$；不证明立方尺度、零噪声、必要阈值、锐性或原环境期望收敛。有限检索与普通数学推导均不等于全球原创性证书或 Lean 认证。

## 谱边界第 152 章补充：有限相消去与原始计数的复零点

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 152 章从原始负号选择计数和出发，通过同一区域上的精确实场平移建立指数矩控制。此后得到固定缩放复域内的整函数展开、每个固定奇数 $\pi i$ 位置的简单零点及有限位移，并与第 150 章的实条件敏感度峰相联系。指数标记界保留任意慢的 $t\to\infty$、有限噪声中心、实际 pair/path 数据律及确定支持的一致性；固定多项式矩不被当作指数矩的替代证明。

M. Biskup、C. Borgs、J. T. Chayes、L. J. Kleinwaks、R. Kotecký，*Partition function zeros at first-order phase transitions: A general analysis*，[arXiv:math-ph/0304007v2](https://arxiv.org/abs/math-ph/0304007v2)。已核对原始首页、完整假设 A 和 B、稳定／近稳定区域定义、注记 2、完整定理 2.2–2.3 及尺度条件 (2.19)、Rouché 定理 4.1，以及第 4.2 节至三个技术引理 4.3–4.5 的完整陈述和零点比较 (4.29)。一般相图与技术引理的完整证明、局部 Lee–Yang 对称定理未被导入。原 PDF 标明收稿 2003 年 4 月 3 日、接受 2004 年 3 月 31 日，arXiv 版本戳为 2004 年 5 月 7 日。

假设 A 要求有限相函数的最大模一致正、实变量二阶连续可微、稳定区域上的解析性、共存处对数斜率分离，以及多相共存处的严格凸多边形条件。定理 2.2 只需 A 的前三项和 B；定理 2.3 使用全部 A 与 B。假设 B 另要求近稳定区域上的解析非零有限体积相近似、相函数及导数的指数逼近、斜率分离，以及复分配函数余项和有限阶导数的指数控制。该框架下，两相零点由等模与奇数相位差方程逼近；尺度条件为 $\liminf L^d\gamma_L/\log L>4d$ 与 $\limsup L^{d-1}\gamma_L<2\tau$，不能替换成本模型的 $\eta,t,\sigma$ 条件。

本模型的实际区域变换 $M_B,M_I$ 是局部两振幅的对应对象，但本章没有建立该文的全局相函数、格点周期边界、轮廓条件或指数有限体积误差。第 152 章直接证明的是固定缩放紧集上的 $O_{\mathrm{Prob}}(t^{-3})$ 解析余项。Rouché 定理 4.1 要求有界分段光滑区域邻域上的解析性和边界严格模不等式；本章以整函数有限和、极限函数的正边界最小模及统一余项界履行这些条件。第 4.2 节强调的主两相和下界与余项上界必须共同使用，不能只凭一个误差上界宣称无额外零点。

原 PDF 为 494,908 字节，SHA256 `f5a6233564fa4004a8027a4443419df87c377119df703ca25b9ef877c84f171c`。52 页提取文本为 152,798 字节，保留 200,969 字节 CFF Type1 字体解码警告，未声称字形无损。检索元数据中伴随论文的交叉编号存在回指本篇的情况；归属按已读原 PDF，而非该交叉编号。另一条 Pirogov–Sinai 伴随论文元数据未被用作本计数律符合其假设的证据。

Katsevich 的 *The Laplace asymptotic expansion in high dimensions*（[arXiv:2406.12706v3](https://arxiv.org/abs/2406.12706v3)）假设 2.3 与注记 2.4–2.5 控制振幅乘密度的尾部，与本章指数标记问题相对应；单独的固定多项式振幅展开并不履行该义务。其单全局极小点前提也不自动覆盖此处竞争的端点与内点。Borgs–Kotecký 的 *Surface Induced Finite Size Effects for First Order Phase Transitions*（[arXiv:cond-mat/9501074v3](https://arxiv.org/abs/cond-mat/9501074v3)）第 6 节至 (6.8) 给出经典两相实响应关系；第 150 章的系数 $6$ 继续归属该成熟有限相机制，两篇原始条件与提取边界沿用第 150 章说明。

同一实现上的关系为：第一共轭对相对于实际等质量场的实位移是 $-\pi^2/(2K_Wr_W^3)$，敏感度峰的实位移是 $-6/(K_Wr_W^3)$，误差均为 $o_{\mathrm{Prob}}((r_Wt^2)^{-1})$；其比值才趋于 $12/\pi^2$。改用精确剖面等质量中心 $h_W$ 时，共同有限质量修正不能删除，因此不是同一个比值。新增内容在于原始计数的指数标记回接及其与有限剖面零点／实响应的连接，不在于创造一般两相抵消机制。本章未证明增长编号、全局最近零点、圆定理、全局相图或原环境期望收敛，也未作 Lean 或全球原创性认证。

## 谱边界第 153 章补充：精确格点率与共同选池预算

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 153 章给出原始选择计数后验在 $\rho\asymp e^{-cQ^3}$ 下的显式正充分区间。预先选择的同一总数对 $x=(x_+,x_-)$ 同时控制大偏差率 $I(x)$ 与分数位移 $\ell(x)$；共同条件槽位律、池供给、有理值间隔、响应曲率和两阶标记回接逐项履行其条件，未把独立比较 Poisson 行当作实际路径行。

Valentin Féray、Pierre-Loïc Méliot、Ashkan Nikeghbali，*Mod-phi convergence I: Normality zones and precise deviations*，[arXiv:1304.2934v4](https://arxiv.org/abs/1304.2934v4)。已核对原始 TeX 的 mod-$\phi$ 定义、Legendre–Fenchel／Poisson 率函数讨论、带倾斜格点 Fourier 反演引理及证明，以及主格点精确偏差定理（原标签 `thm:mainlattice`）的完整陈述和证明。生成函数须在一个共同复带上存在，参考律是非退化无限可分律，$e^{-t_n\eta(z)}\varphi_n(z)$ 须局部一致趋于解析残差 $\psi(z)$，且 $\psi$ 在该复带的实部不消失。主格点定理还要求复带包含零、参考律的最小格点为 $\mathbb Z$、$O(t_n^{-v})$ 的收敛速度、固定内部偏差位置 $x$ 与整数 $t_nx$。

该定理给出指数率、$t_n^{-1/2}$ 前因子和固定阶修正。证明在固定实倾斜下先作 $[-\pi,\pi]$ Fourier 反演，再使用离零频率的严格收缩和 Gaussian 鞍点积分；常数依赖该固定倾斜与紧轮廓。它不直接提供指数增长的实际约束占据向量上的一致近似，也不提供 $e^{-cQ^3}$ 后验带宽或惊异／噪声的两阶标记结论。单行和双行比较不能代替共同复带假设。

单个比较变量 $\operatorname{Pois}(v\lambda)$ 的对应是精确的：$\eta(z)=v(e^z-1)$、$t_n=\lambda$、$\psi=1$，正位置 $x$ 的率函数为 $J_v(x)=x\log(x/v)-x+v$，最优倾斜为 $\log(x/v)$。第 153 章为处理所有确定取整，直接证明 $\Pr\{\operatorname{Pois}(v\lambda)=\lfloor x\lambda\rfloor\}\ge k_v(x)\lambda^{-1/2}e^{-\lambda J_v(x)}$ 的显式界；原文精确偏差框架用于归属与对应，不被当作实际多池律已经 Poisson 化的证明。

同一总数对的最小率由 $\Psi(s)=\sum_\epsilon v_\epsilon(e^{sd_\epsilon}-1-sd_\epsilon)$ 给出，$x_\epsilon(s)=v_\epsilon e^{sd_\epsilon}$、$\ell=\Psi'(s)$。精确差式 $I(x)-I(x(s))=\sum_\epsilon J_{x_\epsilon(s)}(x_\epsilon)$ 只在相同分数位移约束下使用。正可行点和 $5\log Q+O(1)$ 的试验数额外开销均在正文中解析建立；有限正区间是模型内的充分结果，不声称最优性或必要性。

原始归档为 312,525 字节，SHA256 `571a3db83d28686f776e8a1b542e63782c3220fd34bac22b2dadfcc60a2db64e`；主 TeX 335,779 字节，SHA256 `714ea7a213ccb25e4dc420e0ee0d1134e5407be67cef182221e56cbdc0b1a927`；文献文件 17,440 字节，SHA256 `8effbae78f5c53b9c00e12c838ad147cbffd42a6c4d72257d405bf826aaf40a0`。原文 Poisson 率的分段式在 $x>0$ 之后将其余情况写成无穷，而下半连续延拓在 $x=0$ 的值为 $v$；本章只选严格正的 $x_\epsilon$。主格点定理前的均值等式使用极限残差导数 $\psi'$ 代替有限 $n$ 的残差导数，本文不使用该有限等式。原始草稿注释和非格点旁论保持原文身份，不作为本模型前提。

原始第 68 章的相对单／双行概率与精确计数线率仅在其合法范围使用；选池总数的共同比较由本章另行证明。第 151 章的分离有理弧与完整后验回接保留原文归属，新的立方率预算逐项核对增长参数后才使用这些接口。正文区分精确率可行集的弱包含和最终区间的严格扩大；有限搜索未证明全球原创性，普通数学推导未取得 Lean 认证。

## 谱边界第 154 章补充：有界局部频率与增长编号零点

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 154 章在原始完整选择计数律上，同时定位 $|2k+1|\le ct$ 的复零点。实际区域方差差决定二次分支，第三累积量差给出首个偏度修正；同一复矩形上的解析余项控制整批零点，并通过明确边界约定给出精确计数。固定多项式矩和实变量渐近式均未被当作复振幅或复导数的证明。

Kyungchul Song，*A Uniform-in-P Edgeworth Expansion under Weak Cramér Conditions*，[arXiv:1806.01431v2](https://arxiv.org/abs/1806.01431v2)。已核对原始首页、引言的独立三角阵设定、完整定义 2.1、第 2.2 节的标准化与带符号 Edgeworth 测度，以及完整定理 2.1 和推论 2.1 及其说明。arXiv 版本戳为 2019 年 8 月 13 日，稿件首页日期为 8 月 14 日，二者分别保留。全文证明与后续 bootstrap／重抽样应用未被读取或导入。

定义 2.1 的弱及平均弱 Cramér 条件要求共同常数 $b,c,R>0$，使所有 $\|u\|>R$ 的特征函数模或平均模均不超过 $1-c/\|u\|^b$。定理 2.1 处理独立、均值为零的三角阵向量，要求正定平均协方差、整数阶 $s\ge3$ 的一致矩界、平均弱 Cramér 条件、$0<b<2/\max(s-3,1)$ 和指定的 $R$ 下界。误差由 $n^{-(s-2)/2}(1+M_s(f))$ 与相应 Gaussian 连续模共同控制，常数仅依赖定理列出的统一参数。推论 2.1 将其用于凸集指标函数；它不是无条件的全测试函数总变差结论。

本模型的区域电荷经完整选择与能量权重条件化后，并非独立条件坐标之和。原始电荷又具有 $1/B$ 格点步长，其高频特征函数模会精确回归，因此不能直接宣称上述所有高频的 Cramér 条件成立。第 154 章只需重标度井内变量的有界频率，直接积分局部密度余项，并在原始格点回接时控制标记的单元变化与共同尾部。这个对应保留该文的一致振幅要求，同时不导入未经证明的独立性或非格点假设。

原 PDF 为 280,903 字节，SHA256 `0b2e34b275c033d06c5e3a800f46d5b06c5ee15ff01ea8226932849f79a708a0`；27 页提取文本为 50,169 字节，保留 211,707 字节 CFF Type1 字体解码警告。定理条件按可读原文核对，提取成功不代表字形无损；元数据只用于定位原文。

Biskup、Borgs、Chayes、Kleinwaks、Kotecký，*Partition function zeros at first-order phase transitions: A general analysis*，[arXiv:math-ph/0304007v2](https://arxiv.org/abs/math-ph/0304007v2)，沿用第 152 章已核对的原始 PDF，SHA256 `f5a6233564fa4004a8027a4443419df87c377119df703ca25b9ef877c84f171c`。本次重新核对完整假设 A、B、定理 2.3 与 (2.16)–(2.19)、Rouché 定理 4.1 及引理 4.3–4.5 的陈述；技术引理全文证明未被导入。该框架的等模／奇数相位差对应本章的两个区域振幅，但其有限体积解析近似、指数复余项与格点尺度条件并不自动成立。本章直接建立区域非零性、相位单射和边界计数，并在每次 Rouché 比较时同时给出主项下界与余项上界。

Katsevich，*The Laplace asymptotic expansion in high dimensions*，[arXiv:2406.12706v3](https://arxiv.org/abs/2406.12706v3)，原 PDF SHA256 `ee891c6035366249a08e23ee6ea71553466bf1aaa83788717105fdf54dda2742`。已核对的假设 2.1–2.3、定理 2.12 范围保持不变；本次重读注记 2.5 与 (2.7)，其振幅乘密度的联合尾部条件对应这里对复标记模的控制。单全局极小点定理不自动覆盖竞争的端点与内点。Borgs–Kotecký 的 [cond-mat/9501074v3](https://arxiv.org/abs/cond-mat/9501074v3) 继续只在第 150、152 章列明的轮廓／Peierls 条件与有限相响应范围内归属，未新增定理应用。

原始计数回接后的相位预测保留实际有限系数。在 $k\asymp t$ 时，二次分支迭代与第三累积量都影响 $t^{-1}$ 级虚位移；固定编号公式直接代入增长编号会遗漏该项。正文分别陈述精确预测和极限曲线解释，未以未知速率的经验系数收敛代替所需精度。零点结果局限于指定矩形、编号与边界间隔，不声称全球原创性或 Lean 认证。

## 谱边界第 155 章补充：共同总数、Poisson 亲和度与被遮住的率约束

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 155 章把增长维分类占据向量归约到一个总数，再按同一实际奇偶记录比较随机强度与确定强度。联合误差为 $8m/M+\sqrt{48m/M}$；用于稀有总数选择后，隐藏二项分配仍由原始精确条件律给出。新的率预算扩大总数目标集合，但原始 $\beta>1/2$ 与分数位移关系使现有带宽端点保持为 $c_q/4-5\kappa/2$。

Lucien Le Cam，*An approximation theorem for the Poisson binomial distribution*，Pacific Journal of Mathematics **10**(4), 1181–1197 (1960)，[DOI:10.2140/pjm.1960.10.1181](https://doi.org/10.2140/pjm.1960.10.1181)。已核对原始 PDF 的引言、范数约定、第 5 节质量比值与 Stirling 方法、定理 2 假设及第 6 节注记 2。该文的范数是对 $|f|\le1$ 的积分上确界，等于正文事件总变差的两倍；独立 Bernoulli 和的均值和须有限。引言给出与最大成功概率同阶、试验数一致的界，而非仅有成功概率平方和的界。

原 PDF 的文本层缺失部分显示公式并损坏个别字形，故命题 5、定理 2 中未完整提取的精确系数不作已核对前提。正文 (155.11) 独立写出整数试验数的充分界 $d_{\rm TV}(\operatorname{Bin}(n,p),\operatorname{Pois}(np))\le2p$（$0\le p\le1/4$）及所有零均值、小均值情形，归属其经典质量比值方法，不主张最优常数。原 PDF 为 1,418,189 字节，SHA256 `755631d00899d876e7ccbc33c112f912676496995cf3555d98dc3268df8d3216`；提取文本 31,138 字节，SHA256 `029f6a91c30e41f016dd8626c7c41e45e882c22c9e0605d373d6893f3bc34c33`。

Le Cam 的注记 2 给出一般复合跳跃测度不能统一获得同样改善的边界，涉及有理独立的跳跃位置。正文的适用结构更具体：分类试验具有同一个概率向量，选中总数条件下与独立 Poisson 向量具有完全相同的多项分配核，且不同总数的纤维互不相交。因此向量总变差精确等于总数的总变差；这一结构在实际路径的两个奇偶槽位类型内分别验证，未借用任意标记和的结论。

Lasse Leskelä，*Information divergences and likelihood ratios of Poisson processes and point patterns*，[arXiv:2404.00294v1](https://arxiv.org/abs/2404.00294v1)。已核对版本化原始 TeX 的 Hellinger 定义、Poisson Rényi 定理、Hellinger 推论及证明、有限强度证明（包含 $\alpha\in(0,1)$ 分支与零密度区域）以及条件标记定义。强度测度采用 $H^2(\mu,\nu)=\tfrac12\int(\sqrt f-\sqrt g)^2$，并有 $H^2(P_\mu,P_\nu)=1-e^{-H^2(\mu,\nu)}$。原定理在可测空间上的 $\sigma$ 有限强度下成立；本章每个有限 $Q$ 的 $4m$ 个坐标给出有限强度测度，维数增长和零条件强度均不违反假设。

有限向量对应保留准确的二分之一：$\operatorname{Aff}(\bigotimes_i\operatorname{Pois}(\mu_i),\bigotimes_i\operatorname{Pois}(\nu_i))=\exp[-\tfrac12\sum_i(\sqrt{\mu_i}-\sqrt{\nu_i})^2]$。正文也由指数级数直接核对该式。对同一个实际奇偶记录取混合，再以其一阶相依计数的二阶矩支付随机均值差，是本模型的后续推导；该文不保证原始行独立，也不保证进一步条件化于全部池掩码后的 Poisson 比较。后一步使用原始精确分配核。

版本化源归档为 46,152 字节，SHA256 `529bd2052ae36e884e1ea18080115112fd12b57e6039f7fd5c6e23b63f2facbc`；主 TeX 为 148,388 字节，SHA256 `5a359eac75e106ff54583d4ba5fa1c1d529fb8992155bc7bc8e9c2a1e420f59e`。稿件的动态日期和注释备选文本不替代固定版本身份。

Barbour–Hall，*On the rate of Poisson convergence* (1984)，[DOI:10.1017/S0305004100061806](https://doi.org/10.1017/S0305004100061806)，仅核到书目信息，原始证明未取得；其最优 Chen–Stein 因子不作为正文前提。第 153 章所列 Féray–Méliot–Nikeghbali 的精确格点偏差范围保持不变，本章复用正总数位置的显式 Stirling 界和共同分数率函数，未将单行精确偏差升级为原始增长向量定理。经典工具、实际模型联合接口和带宽端点的解析比较分别归属；有限文献核对不构成全球原创性证明。

## 谱边界第 156 章补充：递增局部频率与复鞍点的相对误差条件

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 156 章将原始选择计数的零点范围从固定倍数的 $t$ 推进到 $t\sqrt{\log t}$。固定局部指数标记的原始计数回接、二阶局部密度展开与明确的振幅下界共同给出相对误差，再用于区域非零性、简单零点定位和精确计数。固定正比例的 $t^2$ 范围仍需新的解析和相对误差控制。

T. Bennett、C. J. Howls、G. Nemes、A. B. Olde Daalhuis，*Globally Exact Asymptotics for Integrals with Arbitrary Order Saddles*，[arXiv:1710.10073v2](https://arxiv.org/abs/1710.10073v2)，[DOI:10.1137/17M1154217](https://doi.org/10.1137/17M1154217)。首版提交为 2017 年 10 月 27 日，核对版本戳为 2018 年 2 月 8 日，出版年为 2018 年。原 PDF 为 5,524,442 字节，SHA256 `06e285acd9772ea2f15dab1a31640cccf0f862fe99ae89c86a852ca3ef876634`；34 页提取文本为 89,480 字节，无提取警告，但图形标签含控制字形，未据此宣称排版无损。

已核对引言、第 2 节解析域、临界点阶数、下降路径、相邻鞍点及角域，第 3 节 (9)–(23) 的系数和轮廓推导，以及第 5 节 (40)–(43) 和完整第 5.1 节简单鞍点界 (44)。后续超渐近展开全文和附录 B、C 未作为证明导入。正文引用这些条件来定位尚缺接口，未用该文定理认证本计数阵列的复鞍点估计。

其作用量 $f$ 与振幅 $g$ 须在相应下降路径域 $\Delta^{(n)}$ 的闭包上解析；路径假定终止于无穷远，且 $|f|\to\infty$。相邻鞍点集合非空且有限，初始角域避免下降路径命中另一鞍点。轮廓展开另要求 $g/f^{(N+1)/\omega_n}=o(1/|t|)$、变形区域不穿越分母极点，以及每条相邻轮廓上的绝对可积条件 (22)。$(f-f_n)^{1/\omega_n}$ 的分支由路径固定，精确余项含相邻鞍点的贡献。

界 (42)、(44) 同时包含到 Stokes 方向的角距及振幅绝对值的轮廓积分，不能将其视为与解析域、相邻鞍点几何无关的统一相对误差界。第 156 章在实剖面上已有的 $C^6$ 与 Fourier 界，并不自动给出解析延拓、零自由前因子或合法变形轮廓；原始非中心项和完整选择因子也仅有实包络比较。所缺的是在指数小区域振幅下仍可用的相对原计数回接。

Biskup、Borgs、Chayes、Kleinwaks、Kotecký 的 *Partition function zeros at first-order phase transitions: A general analysis*，[math-ph/0304007v2](https://arxiv.org/abs/math-ph/0304007v2)，沿用第 152、154 章核对的假设 A、B、定理 2.3 及 Rouché／零点分离范围；原 PDF SHA256 `f5a6233564fa4004a8027a4443419df87c377119df703ca25b9ef877c84f171c`。其解析非零有限体积相近似、分离的对数斜率和复余项条件尚未成为本模型的已知前提。正文的精确两区域因子分解体现相同的等模／奇数相位差结构，所需非零性与计数则直接证明。

Katsevich，*The Laplace asymptotic expansion in high dimensions*，[2406.12706v3](https://arxiv.org/abs/2406.12706v3)，原 PDF SHA256 `ee891c6035366249a08e23ee6ea71553466bf1aaa83788717105fdf54dda2742`，继续在已核对的假设 2.1–2.3、定理 2.12 与注记 2.5 振幅乘密度的联合尾部条件内归属；单全局极小点假设未被移植到整个端点／内点混合。Borgs–Kotecký 的 [cond-mat/9501074v3](https://arxiv.org/abs/cond-mat/9501074v3) 保持第 150、152 章列明的轮廓／Peierls 和有限相响应范围，本章未增加定理级应用。

Song，*A Uniform-in-P Edgeworth Expansion under Weak Cramér Conditions*，[1806.01431v2](https://arxiv.org/abs/1806.01431v2)，原 PDF SHA256 `0b2e34b275c033d06c5e3a800f46d5b06c5ee15ff01ea8226932849f79a708a0`，沿用第 154 章完整定义 2.1、定理 2.1、推论 2.1 的范围及提取警告。独立三角阵、正协方差、一致矩和所有充分高频的共同弱 Cramér 条件不能直接用于本选择条件下的格点电荷。本章在 $O(\sqrt{\log t})$ 的局部频率内直接积分密度余项，并支付实际格点标记的单元变化。

Gaussian 变换、局部密度展开、Rouché 方法和相竞争图景为经典工具；第 156 章的新增模型推导在原始同元组上建立固定指数包络，明确支付 $t^{-\rho}$ 振幅下界下的相对误差，并保留完整有限噪声剖面。有限原文核对不证明全球原创性；实包络不能控制指数小 Fourier 振幅的例子也不构成原计数模型的反例。

## 谱边界第 157 章补充：分母归一化、聚集与双频带原模型控制

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 157 章保留有理值容差 $A+B/|p|$。不同值的间距与各自分母相乘后，充分分离条件是 $8AH^2+8BH<1$；随后在高频带用 $|p|$ 的下端点控制精确响应。两个选择池属于同一个原始经验数组，通过精确联合隐藏核分别建立两条条件切片。充分带宽区间 $0<c<7c_q/20-5\kappa/2$ 包含 $3c_q/10$，并经两阶标记、完整选择和全输出尾部回到原后验定理。

Victor Beresnevich，*Rational points near manifolds and metric Diophantine approximation*，[arXiv:0904.0474v1](https://arxiv.org/abs/0904.0474v1)，正式发表 DOI [10.4007/annals.2012.175.1.5](https://doi.org/10.4007/annals.2012.175.1.5)。本章使用固定 v1 原文核对背景与迁移边界，未以发表元数据替代版本正文。源归档 49,952 字节，SHA256 `e6d24608a15e0dd405449f7cbb118de8da61524805cc71a315f6487363e9401b`；提取 TeX 167,804 字节，SHA256 `1c16c4bb829a515ce718fba24d29dc82addd76f2dd82b5aac5e384b49e483fa3`。

原文定义的有理点集保留原始互素条件、分母带 $\delta Q<q\le Q$ 及 $|qf_l(a/q)-b_l|\le\psi$。在解析非退化流形、固定参数区域和 $C_0Q^{-1/m}<\psi<C_0^{-1}$ 下，定理 1 给出 Lebesgue 覆盖下界，推论 1 给出有理点数下界；$C_0,Q_0$ 依赖所选球。这里的坐标误差是 $\psi/q$，不能在需要分母精度时直接替换为 $\psi$。

这些结论不提供本章所需的条件二项概率上界：计数方向、测度、厚度和曲线常数的范围均不同。特别是本章响应随 $Q$ 变化且呈指数平坦，不能把固定流形常数宣称为该族的一致常数。原文高阶相切的聚集例子说明仅有解析非退化不足以反转其下界；它不是本章经验中心的反例。v1 在该例子中列出整数元组时未逐项重述互素限制，因此这里不直接借用其数量估计。

第 157.2 节的有理值引理直接用两个实际整数分母证明，不要求表示互素，也不限制分子大小。低频带需要较强曲率，高频带可使用较高的平台与更小的分母容差；两者通过共同总数选择与原始精确隐藏核组合，而非通过文献的 Lebesgue 泛性结论组合。第 155 章所列 Le Cam、Leskelä 的总变差及 Poisson 亲和度范围保持不变；第 153 章的精确总数率、标记 Fourier 和同核回接继续供给其余前提。

模型贡献是明确的联合构造和条件改进，经典数论间距与概率工具仍分别归属。本章只给出充分区间；不把旧方法约束失效说成物理必要性，也不以有限范围检索声称全球原创。

## 谱边界第 158 章补充：实局部质量误差与复能量轮廓的不同职责

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 158 章保留完整选择比中的有限作用量 $e^{\ell_0-\epsilon D^2}$、非中心向量及全部低计数元组。指定解析比较量与原计数归一化量的差在 $|h|\le Hh_{\rm sc}$ 上为 $\sigma P_H(Q)e^{-b_0Q^3+C_Ht^2}$；负能量轮廓及其 Fourier 尾部单独证明。区域非零性和 $t^2$ 零点计数仍未解决。

Tatpon Siripraparat、Kritsana Neammanee，*A local limit theorem for Poisson binomial random variables*，ScienceAsia **47** (2021), 111–116，[DOI:10.2306/scienceasia1513-1874.2021.006](https://doi.org/10.2306/scienceasia1513-1874.2021.006)。核对原始定义及完整定理 2：独立 Bernoulli 变量可以具有不同成功概率，只要求其和的方差 $d>1$，统一整数质量误差为 $O(d^{-1})$。其 $\sigma$ 表示 Bernoulli 和的标准差，不能与本模型物理噪声同名量混用；不要求所有成功概率远离零或方差与标签数成比例。

该定理应用于原始校准独立标签中的完整总数和外部总数，二者方差均与 $q$ 同阶。完整总数的均值恰为 $q$，从而分母局部质量有 $cq^{-1/2}$ 下界。正文先在实际整数计数上相除，得到 $L_x(k)=e^{\ell_0-\epsilon D_k^2}+O(q^{-1/2})$ 的全箱一致分解；随后才作复场标记。加性余项和保留的指数作用量职责不同，不能以 $L_x-1$ 的较弱多项式包络替换后再声称指数精度。

原 PDF 154,428 字节，SHA256 `1a6ec512d5621ed33bd58ff52260f80256c3ca662a73711c93a580a81628150a`；提取文本 16,116 字节，SHA256 `14560b523acf3695ff527c767c7dd332c91a9929639a8ba850f9f08ad3ab706f`。文本含字体和控制字符提取缺陷，保留 1,077 字节警告流；不声称逐字排版无误。本章核对并使用定理完整陈述及其假设，未重读该文全部证明。

John Kolassa、Jixin Li，*Multivariate saddlepoint approximations in tail probability and conditional inference*，Bernoulli **16**(4) (2010), 1191–1207，[DOI:10.3150/09-BEJ237](https://doi.org/10.3150/09-BEJ237)，[arXiv:1011.5775v1](https://arxiv.org/abs/1011.5775v1)。固定版本为电子重印，分页和排版与正式刊版存在差异。核对其引言、反演式 (2.1)、条件式 (4.1)、引理 4.1 的完整陈述与证明、相邻分母式 (4.3) 和单位格点修正 (4.8)。连续轮廓无界，单位格点轮廓虚部范围为 $\pi$，极点因子分别为 $\tau$ 和 $2\sinh(\tau/2)$。

该文以固定维独立同分布随机向量的样本均值为对象，需要累积量生成函数及相应鞍点条件，给出的相对误差控制针对实统计量紧集。引理 4.1 使用 Watson 展开后的解析余项和共同实倾斜／正态尾项比较积分比值；这不能自动延拓到复振幅的零点附近。本章不借它推出区域非零性，也不声称读完第 3 节全部展开证明。正文的精确有限系数公式与合法负能量半平面由直接计算给出，复鞍点所需的下界仍单独列为未解条件。

该 v1 PDF 243,038 字节，SHA256 `5d656b7446f7e5b5e67424e51a85c8cd24d78d27b16697bdf36adee9bfff67e5`；提取文本 42,535 字节，SHA256 `25be04e4f51bb29e35f4747571e5d31136d782586fe9ba40fd4c1043f0549b96`，保留 138,035 字节字体警告流。本章复用固定原文，不将新检索次数视为新知识。

第 156 章所列 Bennett–Howls–Nemes–Olde Daalhuis 的解析作用量、相邻鞍点、下降轮廓和角域要求仍未自动满足。精确 erfc 端点函数、低元组和与能量积分均可能出现复零点；只有其基本 Gaussian 因子在所证半平面中非零。经典工具、原计数回接和未解决的复几何分别陈述，有限文献核对不构成全球原创性证明。

## 谱边界第 159 章补充：精确指数族率与三频带共同供给

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 159 章从原 Liouville 幅度关系推出 $r>4/5$、$\log(1+r)>4/7$，再保留 Poisson 精确率 $J_v(x)=x\log(x/v)-x+v$。对实际选取的同一总数对，积分上界给 $I(\ell)<1981c_q/2000$，从而三个频带的稀有总数能在同一数组中共同取得。结合精确联合隐藏核，充分带宽范围扩到 $0<c<163c_q/400$，包含 $2c_q/5$；原完整选择律及后验方差的加权 $L^1$ 返回保持原定义。

László Györfi、Peter Harremoës、Gábor Tusnády，*Some Refinements of Large Deviation Tail Probabilities*，[arXiv:1205.1005v1](https://arxiv.org/abs/1205.1005v1)，[指定版本原 TeX](https://arxiv.org/e-print/1205.1005v1)。源归档 5,938 字节，SHA256 `62f4b581dba341f23724d80fd417427c2e20ea71d19527a583290bc801fa4aa2`；提取 TeX 19,664 字节，SHA256 `c0c8d218195c3aea5ec0e4529440b0f5467425f55f86fb7c7e7057ecd450c46b`。本章核对完整 v1 正文、证明和参考文献，未从其参考文献引入未检查的定理。

原文针对固定基准律的独立同分布变量，要求矩母函数在零邻域有限、固定阈值位于指数族均值范围内部且严格高于基准均值。它写出散度 $D(x)=\widehat\theta(x)x-\log Z(\widehat\theta(x))$，非格点定理使用 Bahadur–Rao 尾部前因子和固定 $1/n$ 阈值校正；格点定理用 $(1-e^{-d\widehat\theta})/d$ 替换对应项，并要求阈值为可达样本均值。二项推论明确保留 $\lceil n\mu\rceil/n$ 的取整。

对基准 $\operatorname{Pois}(v)$，$\log Z(\theta)=v(e^\theta-1)$、$\widehat\theta(x)=\log(x/v)$，上述散度就是 $J_v(x)$。本章 $\lambda=Q^3$ 是整数，因此 Poisson 总数可写为 $\lambda$ 个同基准变量之和，最大格距为一。但原文的尾部渐近不等于本章的取整点概率下界，也不处理指数增长的候选池、实际路径依赖或选池后的联合隐藏核。尤其本章负号总数保持在自身均值处，不满足严格上尾条件。式 (159.14) 的含取整点概率须由有限 Stirling 单独证明，其余联合条件由第 155 章的共同总数比较承担。

原文讨论中的更强非渐近不等式仍属猜想性建议，数值表不作为本章证据。这里使用精确散度关系辨别真正稀有率与二次近似；幅度推论、带符号余项积分上界和三层参数是本模型的推导。第 157 章所核对的 Beresnevich 流形计数下界仍不提供本章条件二项概率上界；初等分母分离引理保持原证明和适用范围。

三组总数、尾宽、频带和校准必须在一个共同实现中满足所有严格不等式。单独扩展供给集合或分别优化三个频带都不能替代这一义务。经典概率、数论间距和 Fourier 工具分别保留其归属；本章只给充分范围，不声称端点最优、物理必要性或经全球文献检索确认的原创性。

## 谱边界第 160 章补充：非中心能量扇区与局部零点曲线

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 160 章在原始完整选择计数上，保留非中心向量、精确低计数组、有限选择二次作用量及物理噪声，建立固定局部复场域中的两区域相对振幅。所得有限剖面预测同时覆盖固定正比例 $t^2$ 个简单零点，未缩放相位误差为 $O(t^{-2})$，并在指定逆相位矩形中给出无额外零点的精确计数。固定邻域和指标系数可以依赖于共同紧性类；全局延拓与最大范围未定。

N. M. Temme，*Uniform Asymptotic Methods for Integrals*，[arXiv:1308.1547v1](https://arxiv.org/abs/1308.1547v1)。核对第 2.2 节变换后 Gaussian 积分的解析性、扇区增长、角度条件 $\cos(\theta+2\tau)>0$ 及适用扇区 (2.12)，第 2.3 节无奇点的解析路径条件，第 4.1 节至 (4.9) 的条带假设、移动极点减除和 erfc 表示，以及 (4.18) 的显示渐近式和紧邻例子。后者没有被扩充为复 erfc 无零点定理。

该文的固定解析振幅和条带条件不能自动覆盖本模型的增长维数非中心数组及任意小物理噪声。正文先取 $\pi/4<\theta<\pi/2$ 的固定扇区射线，避开正实行列式切割，同时保留 $\operatorname{Re}(w^2)<0$ 的噪声衰减；其 (160.17)–(160.22) 直接验证尾部、解析性与相对余项。实 erfc 值为正没有被用于推出复剖面非零。

该 v1 PDF 385,992 字节，SHA256 `93d3557ce4824a823e1fe2b8a3ca1e34a780ad1db46654e9af0f219a81d419a4`；提取文本 65,088 字节，SHA256 `777cfc81a2025a5eeca5c92b5c4fc143c0d64f38d7973775287ed5e0279ec209`。保留 131,738 字节提取警告流，不把提取文本当作排版无误的原件。

A. Fernandez、E. A. Spence、A. S. Fokas，*Uniform asymptotics as a stationary point approaches an endpoint*，[arXiv:1707.07927v2](https://arxiv.org/abs/1707.07927v2)。固定 PDF 显示 v2 的 2018 年 1 月 2 日标记，另含 2021 年 6 月 13 日内部日期，二者按原文保留。核对完整引言、定理 1.1 及紧邻注释，包括指定 $J_B$ 积分、对数切割、参数域 (1.1)、固定源参数与允许角度 (1.4)–(1.5)；另核对第 2.1 节解析域和单驻点条件、第 2.2 节坐标变换 (2.2)–(2.5)、第 2.3 节至引理 2.1 的陈述和证明开头。余下分部积分证明及后续全阶定理没有被援引为已转移结果。

该文明确区分形式 Bleistein 变换和参数依赖振幅所需的统一误差。定理 1.1 的相对余项属于其特定 $J_B$ 积分、非负实 $\omega$ 范围及相应 $\lambda$ 范围，不能直接成为本复杂数组的复振幅结论。其 $\delta,\sigma$ 是源文固定参数，与本模型网格尺度和物理噪声不同。提取文本在 (1.10) 附近有负驻点显示式与正轴散文描述的符号张力；正文不依赖该散文符号，所有作用量与相位符号均由本模型精确式直接微分确定。

该 PDF 424,462 字节，SHA256 `b688475265e9ad344276baa0f86f9feea101596627710173e0e91f0c7c92f3af`；提取文本 70,394 字节，SHA256 `25955cbc33b82c837c53756453f524ad334efaf78b01622c7f05d2ba80e286b2`，保留 147,798 字节字体警告流。正文用已证统一半径的局部解析逆映射，再分别支付连接轮廓和无界电荷尾部；没有假定源文全局坐标变换自动适用。

Gaussian 反演、解析隐函数、Morse 坐标、端点与鞍点系数、两振幅抵消和 Rouché 计数均归属经典方法。新增综合是同一原始选择计数上的非中心能量扇区估计、完整低元组混合的解析非零性，以及未加强噪声和序列条件的区域相对回接。有限文献核对不构成全球原创性证明。

## 谱边界第 161 章补充：精确率的统一余量与四频带共同核

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 161 章从原幅度约束得到 $r>99/100$、$\log(1+r)>17/25$，并对同一总数对证明 $0<\ell\le23c_q/25$ 时 $I(\ell)<169c_q/170$。四组总数、隐藏分配宽度、频带端点与三标签校准同时满足严格余量；由一个共同数组的调和事件返回完整原后验，充分区间扩到 $0<c<183c_q/400$，包含 $9c_q/20$。端点和必要性未定。

László Györfi、Peter Harremoës、Gábor Tusnády，*Some Refinements of Large Deviation Tail Probabilities*，[arXiv:1205.1005v1](https://arxiv.org/abs/1205.1005v1)。复用第 159 章核对的固定原 TeX，重新核对指数族的完整设定、精确散度关系、格点定理及其证明。源归档 5,938 字节，SHA256 `62f4b581dba341f23724d80fd417427c2e20ea71d19527a583290bc801fa4aa2`；TeX 19,664 字节，SHA256 `c0c8d218195c3aea5ec0e4529440b0f5467425f55f86fb7c7e7057ecd450c46b`。

源文假定固定基准律的独立同分布变量、零邻域有限的矩母函数以及均值范围内部的固定阈值。对基准 $\operatorname{Pois}(v)$，指数族散度就是 $J_v(x)=x\log(x/v)-x+v$；本章整数 $\lambda=Q^3$ 使总数对应于 $\lambda$ 个同基准变量之和，格距为一。格点尾部定理要求阈值严格高于均值且可达，其前因子校正不提供本章的取整点下界，也不处理增长维数或选择后的联合律。本章负号总数保持在其均值处，故 (161.14) 仍由有限 Stirling 直接证明。

Lasse Leskelä，*Information divergences and likelihood ratios of Poisson processes and point patterns*，[arXiv:2404.00294v1](https://arxiv.org/abs/2404.00294v1)。复用第 155 章的固定原件，核对 Poisson Hellinger 推论、Rényi 证明接口、有限强度证明及标记过程的定义和推论。其有限测度证明采用共同支配强度，保留零强度集合，并通过 Laplace 泛函得到有限格点上的精确亲和度 $\exp[-\frac12\sum_i(\sqrt{\mu_i}-\sqrt{\nu_i})^2]$；维数可以任意有限。

该亲和度承担 (161.19) 的共同条件均值比较，涵盖零或较小的条件类型计数；它不制造实际路径的条件独立性。源文标记过程定义本身就要求给定位置后的独立标记，本章必须先由原始时槽分解证明 (161.20)，再在同一原始奇偶记录上积分条件比较。稀有标记选择没有引入其概率的倒数，也没有把各池的边缘最优值当成同时实现。

第 157 章核对的 Beresnevich 固定解析流形覆盖下界不提供这里的指数薄条件二项概率上界。正文继续使用保留分母的初等有理值分离，包含任意分子、两种符号、非本原表示和重复有理值。原幅度解析推论、精确率上界及显式四层可行点属于本模型的综合推导；有限文献检索不构成全球原创性或最优性证明。

## 谱边界第 162 章补充：区域零点、轮廓邻接与切口抵消

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 162 章区分精确驻点相位的解析延拓、区域振幅的非零性和总和实际零点。固定边界区域在一个显式、依赖切分位置的场值附近出现双端点竞争；原始选择计数的区域零点具有同时简单性、无额外零点计数和 $O(t^{-2})$ 未缩放相位精度。共享切口项在相邻区域中符号相反，因此这一障碍不能被当作总零点曲线的内在终点。

T. Bennett、C. J. Howls、G. Nemes、A. B. Olde Daalhuis，*Globally Exact Asymptotics for Integrals with Arbitrary Order Saddles*，[arXiv:1710.10073v2](https://arxiv.org/abs/1710.10073v2)。核对标题、摘要与引言开头，第 2 节关于临界阶数、陡降路径、解析域 $\Delta^{(n)}$、无穷远增长、邻接关系、角区间 (7) 及初始单邻接鞍点条件，式 (20)–(22) 附近的收敛／变形条件，第 4.1 节 Stokes 余项讨论开头，以及完整附录 C。其余超渐近构造、数值例子、计算程序和附录 A、B 没有作为本章已转移的结果。

源文要求相位与振幅在有关域的闭包上解析，相位模在该域的无穷远趋于无穷，所考察陡降路径通向无穷而非奇点，邻接鞍点集合有限非空，并满足开放角区间上的收敛及式 (22) 的轮廓可积性。变形还须避开扫过区域中的分母零点，并控制归一化振幅的衰减。附录 C 的逆作用量映射位于指定作用量曲面；相同临界值的相位并不能代替积分轮廓和映射分支的判定。

正文的极限四次作用量是整函数，可以直接分类其驻点和必要对齐条件；精确有限剖面则只在已证紧域上具有解析非零性。本章没有证明源文所需的全局 $\Delta^{(n)}$、全部邻接循环或随数组变化的一致余项，故该原文不承担总和的两振幅公式。虚轴上较大上方鞍点的排除来自原始正权计数的模上界；区域双端点定理只使用有界实区间、两个端点的正实衰减斜率及已证中段作用量间隙。

固定 PDF 为 5,524,442 字节，SHA256 `06e285acd9772ea2f15dab1a31640cccf0f862fe99ae89c86a852ca3ef876634`；提取文本为 89,480 字节，SHA256 `dc55582ddf86c76e6362cf8437ebd92651c8a5e1250f5e7021704587bb9916c4`。文本含 NUL／控制字形，空警告流不表示排版完整；解释边界按上述原文假设保留。

代数求根、解析逆映射、端点 Laplace 展开、分部积分与 Rouché 计数保留经典归属。本章新增组合是同一原始选择数组上的实际区域零点及切分障碍，并明确它不能替代非局部总零点定理。第 160 章的局部总零点结果保持有效；总和的轮廓系数、抵消后的相对下界及实际转换仍未定。

## 谱边界第 163 章补充：约束率极小点与带符号频带边界

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 163 章给出严格有限频带构造的充要边界。两个 Poisson 总数在同一分数约束下具有唯一正有限极小点；负分数总数对 $(1,\alpha_L)$ 同时满足分数 $-\phi$ 与率 $1-\alpha_L+\alpha_L\log\alpha_L<67/100$，从而在整个所需范围取得统一供给余量。至多 $n$ 个频带的边界为 $(c_q/2-5\kappa)(1-2^{-n})$，固定有限频带的并集使完整原后验方差定理适用于每个固定 $0<c<99c_q/200$。该边界属于构造；物理必要阈值仍未定。

László Györfi、Peter Harremoës、Gábor Tusnády，*Some Refinements of Large Deviation Tail Probabilities*，[arXiv:1205.1005v1](https://arxiv.org/abs/1205.1005v1)。复用已核对的固定原 TeX，核对指数族设定、精确散度恒等式及格点定理和证明。源归档 5,938 字节，SHA256 `62f4b581dba341f23724d80fd417427c2e20ea71d19527a583290bc801fa4aa2`；TeX 19,664 字节，SHA256 `c0c8d218195c3aea5ec0e4529440b0f5467425f55f86fb7c7e7057ecd450c46b`。

原文以固定基准律的 iid 变量、零邻域有限矩母函数及均值范围内部参数为条件，写出 $D=\widehat\theta\mu-\log Z(\widehat\theta)$。上尾定理另要求阈值高于原均值，格点定理要求可达性和跨度前因子。本模型两个 Poisson 坐标具有所有实指数矩，中心化累积量 $K$ 直接给出精确对偶；负倾斜和两坐标等式约束由 (163.8) 的散度分解直接证明，没有从正倾斜上尾公式外推。

每个 Poisson 坐标的格距为一，Liouville 加权后的标量分数却不能当作格距一的随机变量。正文使用两个分别取整的计数点，并由有限 Stirling 得到 (163.24) 的点概率下界；尾渐近不能代替该点下界，也不能自动提供指数多试验池的联合有效性。共同数组近似和适应选择后的合法条件核由第 155 章及 (163.26)–(163.27) 承担。

Lasse Leskelä，*Information divergences and likelihood ratios of Poisson processes and point patterns*，[arXiv:2404.00294v1](https://arxiv.org/abs/2404.00294v1)。已核对的有限格点亲和度 $\exp[-\frac12\sum_i(\sqrt{\mu_i}-\sqrt{\nu_i})^2]$ 不含固定维数惩罚；标记过程则要求合法条件标记核，不能制造依赖隐藏分配的选择之后的独立性。本章在揭示原奇偶记录和总数之后保留精确核，以同一个实际数组的条件描述证明各频带界。

有理点和凸曲面文献没有被替代性地用于这个指数薄的共同目标事件。正文继续保留全部投影原像、正负分子、非本原表示和重复有理值，以精确分母分离和带符号响应曲率控制同一事件。指数族对偶和递推求解属于经典方法；新增综合在于实际可达到的约束率、负分数供给和完整原模型的两阶标记回接。有限文献检索没有证明全球原创性或物理最优性。

## 谱边界第 164 章补充：总轮廓、鞍点系数与非局部零点

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 164 章在 $\mathcal D=\{2u-2u^3:u=\alpha-i\beta,\ \beta>0,\ \alpha>\sqrt{2\beta^2+2/3}\}$ 的固定紧子域内证明原始总量的两振幅展开。其完整有限相位给同时简单零点、无额外零点计数及 $O(t^{-2})$ 未缩放误差，覆盖全部固定有限正相位弧。第 162 章的区域障碍依然存在，但合成总积分后不再限制这条总零点延拓。

T. Bennett、C. J. Howls、G. Nemes、A. B. Olde Daalhuis，*Globally Exact Asymptotics for Integrals with Arbitrary Order Saddles*，[arXiv:1710.10073v2](https://arxiv.org/abs/1710.10073v2)。本章核对第 2 节的解析域、邻接与角区间假设，式 (20)–(22) 周围的条件、完整附录 C，以及第 8 节 swallowtail 例子至该节结尾。固定 PDF 为 5,524,442 字节，SHA256 `06e285acd9772ea2f15dab1a31640cccf0f862fe99ae89c86a852ca3ef876634`；提取文本为 89,480 字节，SHA256 `dc55582ddf86c76e6362cf8437ebd92651c8a5e1250f5e7021704587bb9916c4`。文本含 NUL／控制字形，空警告流不代表排版完整。

源文要求相关域闭包上的解析性、相位模在无穷远的增长、通向无穷的陡降路径、有限非空的邻接集合、初始每条邻接轮廓的单鞍点条件、开放角区间上的收敛、归一化振幅衰减、扫过区域中的分母非零和式 (22) 的可积性。附录 C 将逆作用量奇点放在适当的作用量曲面上。第 8 节引入未知邻接系数，在其特定轮廓框架下取 $0$ 或 $1$，并用指定五次相位的高阶数值近似推断系数，说明还可几何确认；这些数值推断没有移用于本模型。

正文直接以有界矩形的 Cauchy 恒等式确定各段方向，以统一竖直下降和水平作用量间隙确定端点、内部鞍点的系数均为 $+1$，再控制回接段和原实尾。复变形始终留在已证解析域内；没有建立或借用未核验的全局作用量曲面、无穷远复轮廓或全局 Stokes 乘子定理。相位对齐本身不承担可达性或系数判定。

第 158 章的选择系数／计数单元返回与第 160 章的精确非中心噪声剖面是本章复用的前提。Cauchy、解析隐函数、Gaussian／端点展开和 Rouché 计数保留经典归属；模型内新增联系是显式总轮廓域及其向同一原始选择数组的相对振幅转移。物理场中的总零点预测与切分无关，区域坐标的中心和尺度仍依赖其定义。随数组增长的区域、其他全局零点族和最大延拓范围没有被结算；有限来源检查不作全球原创性声明。

## 谱边界第 165 章补充：精确后验直线与联合算术条件

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 165 章给出固定单一隐藏对时的完整外部后验混合身份，证明任意多个外部经验中心都沿同一仿射直线响应。共同分母的整数行列式进一步把全部共振三元组压入唯一平面，并得到保留联合截距与方向的条件概率界。$\gamma<c<3\gamma/2$ 仅是已核对的条件接口：原数据律下的例外事件概率仍未界定，第 163 章的无条件范围没有被扩展。

Victor Beresnevich，*Rational points near manifolds and metric Diophantine approximation*，[arXiv:0904.0474v1](https://arxiv.org/abs/0904.0474v1)，[原 TeX](https://arxiv.org/e-print/0904.0474v1)。所核对原 TeX 为 167,804 字节，SHA256 `1c16c4bb829a515ce718fba24d29dc82addd76f2dd82b5aac5e384b49e483fa3`。核对解析非退化性、主有理点定理的尺度和互素归一化、覆盖／下计数推论，以及证明中的楔积、原始子格和定量非发散条件。

原文将解析非退化性写成不包含在任何真仿射子空间内，等价于 $1,f_1,\ldots,f_n$ 的线性独立。主定理使用局部紧球及依赖几何的常数，厚度范围为 $C_0Q_{\rm den}^{-1/\mathrm{codim}}<\psi<C_0^{-1}$，并保留 $|q_{\rm den}f-a|\le\psi$ 的尺度与互素条件。覆盖推论导出的是 Lebesgue 测度意义的下计数；它没有给出本章需要的条件离散上小球概率界。

原证明中的格子步骤要求每个原始子格的楔积与解析良性控制，以及一致正的上确界下界 $\rho$。这些显示条件用于定位当前迁移缺口；所引定量非发散定理的另一篇原始来源未被独立借入。固定曲面的常数不能作为当前指数扁平条件响应的一致常数，Lebesgue 测度不能换成原二项投影律，下计数也不能充当上计数。

本章精确混合、叉积高度、整数行列式和两整数点强凸性证明均在正文给出，属于经典有限代数与凸性方法在原后验上的应用。第 155、163 章已核对的联合选择、条件分配、精确约束率及完整标记返回继续承担其原范围内的前提。新增联系是单一响应方向的精确识别，以及不丢失共同实现的平面／直线交段条件；没有引入独立经验相位或声称实际例外事件概率已趋零。

多隐藏对的正多项式身份说明后续需要控制哪些共同协方差小行列式，但它本身不是非退化性或更宽后验定理。有限来源核对不构成全球原创性认证；所有较宽结论保持同一句作用域内的概率前提。

## 谱边界第 166 章补充：增长参数域与相对渐近的统一性

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 166 章以 $b_Q=\eta+\sigma^2+t^{-1}+\sqrt\delta$、$R_Q=b_Q^{-1/1000}$ 和 $\Omega_Q=R_Q^4$ 给出原始选择计数零点的显式增长窗口。在原许可序列上，$\Omega_Q\to\infty$；精确有限相位在该域内同时定位全部简单零点，给出无额外零点计数及 $O(t^{-2})$ 未缩放误差。最大增长范围仍未确定。

A. Fernandez、E. A. Spence、A. S. Fokas，*Uniform asymptotics as a stationary point approaches an endpoint*，[arXiv:1707.07927v2](https://arxiv.org/abs/1707.07927v2)。固定 PDF 为 424,462 字节，SHA256 `b688475265e9ad344276baa0f86f9feea101596627710173e0e91f0c7c92f3af`；提取文本为 70,394 字节，SHA256 `25955cbc33b82c837c53756453f524ad334efaf78b01622c7f05d2ba80e286b2`。提取警告流为 147,798 字节，SHA256 `fcf0d7ff42d583ef38823497f18a666d3bc9affe7c1254b2ca5df45d2c262aac`。原件页眉显示 v2、2018 年 1 月 2 日，标题页文字另含 2021 年 6 月 13 日；保留这两个实际日期，不推断未经核对的修订关系。

所用范围是定义 1.1、条件 (1.1)–(1.5)、参数相关 Jacobian 的说明、定理 1.1、定理 1.3 的陈述、引理 3.1–3.2、引理 3.4，以及引理 3.5–3.6 的完整证明至 (3.28)。第 4 节开头概述用于辨明范围，其后全阶计算没有用于本文。源文的 $\delta\in(0,1)$ 与 $\sigma\in[1/2,1)$ 是指定积分的固定参数，与本文的 $\delta=Q^{-1/2}$ 和趋零测量噪声不同。其 $\lambda$ 位于 $t^{\delta-1}/(1-t^{\delta-1})$ 与 $t^{1-\delta}-1$ 之间；相位割线为 $(-\infty,0]$ 和 $[1,\infty)$，积分射线角须满足显式的参数相关衰减条件。定理 1.3 另取源文 $\sigma=1/2$ 并限制分割尺度，这些条件没有转施给原数组。

引理 3.6 分别证明变换振幅导数的局部统一界和远处多项式增长界；配合引理 3.4 及 (3.27) 的领先振幅下界，才允许把尾项除以领先项。参数相关换元本身不保证统一余项。本文据此明确区分固定域估计与增长域估计，并重新证明原数组的能量预解式域、完整低计数组的非零性、缩放 Jacobian 控制和增长场计数返回。任何 $Q$ 的多项式因子都由 $Q^3$ 指数余量支付，不要求任意缓慢的 $t^2$ 去压住它。

第 158 章提供完整选择系数与计数单元接口，第 160 章提供精确非中心剖面，第 162 章区分区域零点与总零点，第 164 章提供总积分矩形的固定域结构。经典 Laplace、Cauchy、解析隐函数和 Rouché 方法保留原归属；新增推导在于这些接口在同一原数组的显式增长域上的定量兼容。源文不直接证明本模型的选择计数结论，有限来源核对亦不构成全球原创性认证。

## 谱边界第 167 章补充：补偿尺度与联合响应退化

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 167 章证明原计数线相邻似然差由补偿项主导，将同一生成平面的截距与方向联系到实际计数的整数线性组合，并证明固定多个隐藏对的归一化协方差行列式在原共同数组上指数衰减。这个方法反例针对明确的多项式横截性前提；原例外事件的概率和更宽原后验定理仍未得到。

Alex Dytso、H. Vincent Poor、Shlomo Shamai (Shitz)，*A General Derivative Identity for the Conditional Mean Estimator in Gaussian Noise and Some Applications*，[arXiv:2104.01883v1](https://arxiv.org/abs/2104.01883v1)，[原 TeX](https://arxiv.org/e-print/2104.01883v1)。所核对 `Camera-Ready_v4.tex` 为 203,510 字节，SHA256 `ad005a76dfafcfeb9688390e40137cf3a6a4cb7572f9690b41652789270c9c16`。主定理假设 $Y=X+N$，其中 $N$ 独立且为正定协方差的 Gaussian 噪声，并要求 $U-X-Y$ Markov 关系及所列条件矩可积性。结论将条件均值 Jacobian 写成逆噪声协方差与条件协方差的乘积；原证明中的 Gaussian 似然微分、Bayes 公式、score 身份及积分可交换条件均在核对范围内。

该身份不蕴含协方差或其小行列式的定量正下界。本章对 $\theta_i=\log S_i$ 的响应来自有限完整支持后验的正和微分，未把原离散分配替换为 Gaussian 观测通道，也未引入原文数值微分、模拟或增长阶数结论。式 (167.23) 的有限和证明与后续交换配对一起保留共同归一化，行列式的尺度由原补偿关系另行推出。

László Györfi、Peter Harremoës、Gábor Tusnády，*Some Refinements of Large Deviation Tail Probabilities*，[arXiv:1205.1005v1](https://arxiv.org/abs/1205.1005v1)，[原 TeX](https://arxiv.org/e-print/1205.1005v1)。所核对 `gyorfi1205v1.tex` 为 19,664 字节，SHA256 `c0c8d218195c3aea5ec0e4529440b0f5467425f55f86fb7c7e7057ecd450c46b`。固定 iid 基准律在零附近有有限矩母函数，倾斜均值位于内部；归一化配分函数和精确散度身份继续用于理解第 163 章已证明的稀有总数率。原文的一维尾估计不提供本章所需的共同计数／校准模整数律，不能替代原取整点下界或共同向量条件律。

第 165 章核对的 Beresnevich 解析非退化性及原始子格下界仍保留其范围。当前指数退化进一步说明，固定几何的多项式非退化常数不能直接迁移到该共同数组的响应。经典有限指数族、交换配对和行列式工具的归属不变；原补偿尺度、共同平面约束及含原选择代价的响应上界是本卷的具体综合推导。有限来源核对不构成全球原创性认证。

## 谱边界第 168 章补充：联合切线截距与剩余类

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 168 章以精确 Gamma 曲线建立同层联合截距／剩余类判据，给出任意薄条命中的切线表示、较大辅助分母的充分条件及固定曲线的截距单独失效反例。Taylor、Dirichlet 抽屉原理、模算术与紧性属经典工具；当前原模型的联合实现仍未证明。

Beresnevich、Vaughan、Velani，*Inhomogeneous Diophantine approximation on planar curves*，[arXiv:0903.2817v1](https://arxiv.org/abs/0903.2817v1)。核对原 TeX 的计数定义、标签 thm6 的覆盖定理及几何数论／Taylor 证明。分母在 $R<q\le2R$ 中变化；常数满足 $C_1=3c_2/(c_1c_0^8)$、$c_0<1/6$、$k_1^3>c_2C_1^2$，并要求 $\delta\ge k_1/R$。对曲率随 $N$ 增长的移动对偶曲线 $N\mathcal L$，这些常数尚无所需一致性；原定理也没有指定 $N$ 或联合原始剩余类的下命中。原证明末尾 Taylor 行的固定因子差异不用于本章任何数值常数。

Li、Li、Wu，[arXiv:2409.18635v1](https://arxiv.org/abs/2409.18635v1)。核对定义、维数定理、Cartesian 乘积下构造及 lacunary 情形证明。其自由平面坐标或附 gcd 条件的同标量限制，不是带原两侧有符号位移的 $(u,\Psi(u))$；误差乘积小不能推出两项同时小。其引用的矩阵环面缩靶预印本未取得可用原文，未作为本章依据。

Guo，[arXiv:1010.4923v2](https://arxiv.org/abs/1010.4923v2)。核对 Remark 6.5(1) 及第 6 节的频率分解、格陪集估计。非零曲率下固定方向的 $O(t^{19/29})$ 误差界支持第 86 章凸壳上界，不提供本章所需的薄条下命中。

Howard、Trifonov，*Bounding the number of lattice points near a convex curve*，[arXiv:2207.09532v1](https://arxiv.org/abs/2207.09532v1)，2023 年发表版 DOI [10.7169/facm/2087](https://doi.org/10.7169/facm/2087)。核对近曲线定理、thm:near_open 及三角面积／非共线证明。假设包含

$$
\delta<\frac{d_\Lambda^2}{2\{R_2+d_\Lambda+\sqrt{(R_2+d_\Lambda)^2-d_\Lambda^2}\}},
\qquad A_\Lambda/2-\mathscr L\delta-\tfrac32\delta^2>0.
$$

结论为上计数。固定内弧经 $N$ 放大时，$R_1,R_2,\mathscr L\asymp N$；整数格上的第一条件要求厚度 $O(N^{-1})$，小于当前的 $N^{-1/2}$。缩短弧只改变长度项，不能消去曲率半径条件，因此该结果不解决原尺度下的存在问题。

Adamczewski、Bugeaud，*On the complexity of algebraic numbers I. Expansions in integer bases*，Annals of Mathematics 165 (2007), 547–565，[发表版 PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v165-n2-p04.pdf)。核对第 4 节绝对值规范及 554–555 页 Theorem E：允许基域外的代数线性形式系数，结论仍为有限个真基域子空间。这支持第 93、99 章采用的表述；原文归属 Evertse 的深层定理证明未另行核验，第 168 章的新判据不依赖该代数排除。

Pollington、Velani、Zafeiropoulos、Zorin，*Inhomogeneous Diophantine Approximation on M_0-sets with restricted denominators*，[arXiv:1906.01151v1](https://arxiv.org/abs/1906.01151v1)。核对收敛定理 mainCONV、Lemma 2 lem2、Fourier 上包络及 Borel–Cantelli 证明，关键估计为

$$
\mu(E_q^\gamma)\le3\psi(q)+3\sup_{k\ge1}|\widehat\mu(kq)|.
$$

在原稀疏根分母上，正的对数 Fourier 衰减使根重现宽度的上包络可求和；这是根坐标中的边界，不是参数坐标中的断言，也不推出 $E_2$ 为空。上述文献范围与本章初等联合判据的证明依赖区分保留；无全局检索完整性或原创性声明。

## 谱边界第 169 章补充：完整谱条件能量与相对窗口质量

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 169 章保留完整有限谱、选择系数、非中心位移、所有低频组合和原物理噪声，在固定非零重标电荷区间证明条件能量的相对鞍点公式，并返回原完整选择计数律的稀有窗口。它没有证明该场尺度上的总电荷轮廓或振荡零点。

Bernard Bercu、Jean-François Bony、Vincent Bruneau，*Spectrum of the product of Toeplitz matrices with application in probability*，[arXiv:0712.1302v1](https://arxiv.org/abs/0712.1302v1)，2007-12-10。原 PDF 为 209,617 字节，SHA256 `d843e4467b8a5e5b819b1c551a0ab81c4499c8c51643e0751e258bbc6f8edea0`。核对引言、Lemma 2.1、Theorems 2.3–2.4、Example 2.6，以及第 3 节至 Corollary 3.1、Remark 3.2。原文假设连续实 Toeplitz 符号 $f,g$ 且 $g\ge0$，Gaussian 过程中心化、平稳，协方差为 Toeplitz$(g)$。它先控制极端特征值，再以完整对数谱变换得到实大偏差原理；率函数的仿射延拓受谱极端控制，Example 2.6 区分极端谱点与乘积符号的值域。

这些条件不能把当前条件高频协方差识别为 Toeplitz 乘积，原文也没有给出非中心三角阵列在衰减物理噪声下的复相对密度或零点定理。迁移的是同时保留对数谱变换与可用谱域的结构；本章式 (169.14)–(169.16)、(169.29)–(169.34) 对原有限数组直接证明对应关系，未从原文推定其秩一非中心项。

Philippe Mounaix、Satya N. Majumdar、Abhimanyu Banerjee，*Bose-Einstein Condensation of a Gaussian Random Field in the Thermodynamic Limit*，[arXiv:1111.3229v2](https://arxiv.org/abs/1111.3229v2)，版本日期 2012-01-30；所保留 PDF 标题页同时显示 September 6, 2021。原 PDF 为 640,657 字节，SHA256 `c1c39f1d9a5b6565fce475f553cd19b08be3f7e6bb99b4b930aedc6abf9f3282`。核对标题、引言和第 II 节至式 (23)，包括精确模式律、Laplace 乘积、Bromwich 域以及式 (19) 的不同极限次序。

原文研究周期盒中的中心齐次 Gaussian 场，假设唯一主导的零 Fourier 模式、具有指定低频幂律的极限径向谱，并采用固定强度的热力学极限。当前完整选择计数律未满足这些已验前提。原文的 $\epsilon$ 区分实、复场，与本章有限外部选择系数不同；其反演轮廓位于 Laplace 奇点右侧，变形须保留解析域，式 (19) 的有限红外修正依赖极限次序。这些事实支持完整经验谱及支持域检查，不证明本章总电荷轮廓或凝聚转变，后续未核对的凝聚推导未被采用。

Gaussian 配方、行列式／Sherman–Morrison 身份、谱交错及鞍点方法的经典归属保留。本章模型综合的边界是条件能量复邻域、带原噪声的相对返回与有限谱解释；实大偏差原理不替代相对振荡估计，局部窗口不替代总幅度。所引用版本的提取文本及其字形限制未被当作额外定理，有限来源核对不声称检索穷尽或全球原创。

## 谱边界第 170 章补充：条件计数与完整校准的共同稳定性

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 170 章在同一原始数组构造中心／相邻组条件交换，得到共同二项计数、统一最大公因数概率界及完整选择校准的二阶误差。满足 $\phi-c_q>\gamma-2e$ 时，它控制第 165 章异常事件的 $J=0$ 分支；$J\ne0$ 的联合概率估计仍未解决，没有据此扩展原物理带宽。

Lasse Leskelä，*Information divergences and likelihood ratios of Poisson processes and point patterns*，[arXiv:2404.00294v1](https://arxiv.org/abs/2404.00294v1)。原始 TeX 为 148,388 字节，SHA256 5a359eac75e106ff54583d4ba5fa1c1d529fb8992155bc7bc8e9c2a1e420f59e；原始归档为 46,152 字节，SHA256 529bd2052ae36e884e1ea18080115112fd12b57e6039f7fd5c6e23b63f2facbc。核对源码标签 the:PPPRenyi、the:PoissonHellinger、the:PoissonRenyiFinite 和 sec:MarkedPPP，包括有限强度证明中 $\alpha=1/2$ 的似然比／Laplace 泛函计算与零密度支撑处理。

原文采用 $\sigma$ 有限强度的 Poisson 点过程，以及给定位置后条件独立的概率标记核。规范化为 $H^2(\lambda,\mu)=\tfrac12\int(\sqrt f-\sqrt g)^2$ 和 $H^2(P_\lambda,P_\mu)=1-\exp[-H^2(\lambda,\mu)]$；有限离散空间的亲和度即 $\exp[-\tfrac12\sum_i(\sqrt{\mu_i}-\sqrt{\nu_i})^2]$，允许零强度。第 155 章已在共同随机均值上使用该关系；第 170 章复用其未条件化供给范围，不把它提升为 Markov 行独立或依赖标记选择后的独立性。

式 (170.11) 的完整范围 $0\le h\le k/2$ 使用 $\log(1-x)\ge-3x$、$0\le x\le2/3$。奇偶因子分解与有限选择分割建立实际条件核；正系数比较保留所有标签和完整 $q$ 约束，未在大量删除后应用固定删除渐近。有限 Fourier 滤波和除数界控制同一个条件守恒总数，不为数据生成的法向量假定独立分布。

Poisson 亲和度、条件乘积限制、Stirling、Fourier 剩余类公式和除数估计保留经典归属。本章的综合贡献限于原模型的共同计数／校准关系与有条件的零组合分支。Györfi 的尾近似未被用来代替中心附近的精确取整下界；既有 Le Cam 文本层缺陷不支撑未经核对的更强结论。未取得的校准分布、统一随机相位或非零分支概率均不归于文献，有限核对不表示检索穷尽或全球原创。

## 谱边界第 171 章补充：全谱总振幅的精确分离与无零区域

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 171 章在 $h=H/\sqrt\delta$ 的全谱尺度上，先补齐整条电荷实线，再控制补入半线。原始负号总归一化量在负实轴附近一个固定宽度的显式复矩形中无零点，并有 $O(\delta)$ 相对及未缩放相位误差；实际实参数后验集中在 $\delta D^2$ 远离零的范围。振荡共存区的非零零点计数和相位反演仍未解决。

Nico M. Temme，*Uniform Asymptotic Methods for Integrals*，[arXiv:1308.1547v1](https://arxiv.org/abs/1308.1547v1)，提交于 2013-08-07，PDF 首页日期为 2013-08-08。原始 PDF 为 385,992 字节，SHA256 93d3557ce4824a823e1fe2b8a3ca1e34a780ad1db46654e9af0f219a81d419a4。保留文本为 65,088 字节，SHA256 777cfc81a2025a5eeca5c92b5c4fc143c0d64f38d7973775287ed5e0279ec209；文字提取仍有字形与间距缺陷。

核对范围为第 2.2 节至扇形条件 (2.12)、第 2.3 节的轮廓条件、Remark 3.1、第 4 节与第 4.1 节至 (4.9) 的分解和一致性范围；第 4.1.1 节至 (4.15) 的例子不承担本章估计。式 (4.2)–(4.9) 假定振幅在条带内解析、$\Re\omega>0$，起初还取 $\Re\alpha>0$，先分离极点项再处理正则 Gaussian 积分；跨极点的解析延拓需要轮廓变更或留数处理，一致性限于解析条带的内部区域。第 2.2 节还要求无穷远增长控制，旋转角同时满足解析域与 Gaussian 衰减条件。Remark 3.1 说明，仅有实变量光滑渐近不足以控制指数小的振荡积分。

精确恒等式 $\operatorname{erfc}(-z)=2-\operatorname{erfc}(z)$ 与本章的整线／补半线分离同形，但不自动提供三角数组、有限非中心谱、物理噪声及选择计数的统一界。本章独立给出系数为一的整线电荷积分、位于 $\Re s<-\xi/2$ 的合法局部能量变形、条件 Fourier 尾界及补半线的指数相对代价；未导入未经核对定义域的复 erfc 尾估计。原始计数误差中的同一个 $\sigma$ 仅在总振幅下界成立后约去。

Gaussian、秩一线性代数、解析鞍点与 Rouché 方法保留经典归属。Temme 引用的 van der Waerden 论文和 De Bruijn 著作未在此次核对中作为独立原始来源使用。本章的模型综合保留第 169 章与第 166 章的原范围，不把实能量鞍点无折叠提升为复共存零曲线的全局延拓，不把辅助精度零点称为原有限配分函数的奇点。有限文献核对不表示检索穷尽或全球原创。

## 谱边界第 172 章补充：固定超稀疏分母、解析值与实际双根分离

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 172 章在原始 $Q_n$ 上构造增长阶 Taylor 预测，证明二次项与整数保持至少 $1/(2D_n)$ 的距离，$D_n=Q_n^{o(1)}$。结合完整实际分组的定量相对比较，它给出双根均值最佳共同绝对对数界的对数指数一、与原始 $\vartheta$ 代数独立的根组合类，以及每个参数区间内紧致不可数的排除族。原始 $E_2$ 的存在或空性仍未解决。

Boris Adamczewski，*Transcendance « à la Liouville » de certains nombres réels*，C. R. Acad. Sci. Paris, Ser. I 338 (2004), 511–514，[DOI 10.1016/j.crma.2004.02.002](https://doi.org/10.1016/j.crma.2004.02.002)，[四页原始 PDF](https://comptes-rendus.academie-sciences.fr/mathematique/item/10.1016/j.crma.2004.02.002.pdf)。其定理与证明研究 lacunary 幂级数在 Pisot 或 Salem 数倒数处的取值，使用代数高度和多处 Roth 定理。这里的固定输入 $\vartheta$ 超越，故该定理不证明本章的代数独立性。可借鉴的是同时控制逼近尾与逼近数高度的要求；本章以原始有理前缀上的整数多项式另给完整证明。原始 PDF 为 99,149 字节，SHA256 83997f1fdbe8312bb4e39504bdb1e3f92edd64e4fbca038c309c0014feb7592b；保留提取文本存在字体处理警告，原 PDF 是核对来源。

Marques–Ramirez，*On transcendental analytic functions mapping an uncountable class of U-numbers into Liouville numbers*，[arXiv:1408.0844v2](https://arxiv.org/abs/1408.0844v2)，[原始 TeX](https://arxiv.org/e-print/1408.0844v2)。完整定义和证明中的 ultra-number 假设要求三重指数高度尺度的逼近；该条件未在本章固定输入上建立。论文控制代数参数处的像分母，并不直接给出本章原始分母下的二次项障碍。其印刷证明中的映射 $\psi(x)=x/[2(1+x^2)]$ 还存在明确的中间断言限制：$\psi(-1)=-1/4$，故不能将所有所述实代数数送入 $[0,1/2]$；若 $\alpha=(3+\sqrt5)/2$，则 $\alpha^2-3\alpha+1=0$ 且 $\psi(\alpha)=1/6$，故精确次数二并未保留。这些例子反驳的是相应中间范围与次数断言，不是对整篇存在定理的反驳。本章未导入或修补该论文的定理。保留原始对象为 9,691 字节，SHA256 0550d3332612d44e8ff013b703dc116f66c19c7e31cb48c4b1a8f0a46275f3a1。

Diego Marques，*Mahler's Problem on Liouville Numbers*，[arXiv:2609.14202v2](https://arxiv.org/abs/2609.14202v2)，[原始 TeX](https://arxiv.org/e-print/2609.14202v2)。核对范围为局部定理陈述、双高度计数设置、安全中心证明和相关嵌套区间选择。预印本的陈述自由选取一个 Liouville 输入，使其解析像具有有界无理性指数；安全中心的既约分母位于 $Q\le q<2Q$ 的块内，后续源尺度也随构造选择。它不指定这里的 $\vartheta$ 或 $Q_n^2$，不能提供固定原始层的下界命中。完整行列式计数证明及预印本的全局结论未作独立核验，也未作本章前提。保留原始对象为 34,558 字节，SHA256 d8abf13acd7b51976f3257c2fe491be51f2be4482263f00e2a33f74935d2a536。

有理根、整数整除、Taylor 展开、Liouville 逼近和紧致性保留经典归属。新的模型综合由第 172 章自给证明承担；有限文献核对不表示检索穷尽或全球原创。标量类的代数独立性并不排除同一参数的其他根组合满足既有障碍，也不证明同步参数不存在。

## 谱边界第 173 章补充：原始计数方块与依赖数据的法向

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 173 章在同一实际 pair 或 path 数组内构造两类配对切换，证明整数可逆的计数关系、揭示块商后的平均条件余数总变差界，以及按块宽 $g$ 支付的完整有限 $q$ 后验校准误差。对原始 $\beta\ge3/5$，它给出宽于生成法向高度的计数方块，并排除实际长区间事件中的同号法向。反号自适应法向的实际方块占比仍未得到趋零界，更宽物理带宽上的完整结论仍未解决。

Mark Rudelson 与 Roman Vershynin，*The Littlewood-Offord Problem and invertibility of random matrices*，[arXiv:math/0703503v1](https://arxiv.org/abs/math/0703503v1)，[原始源文件](https://arxiv.org/src/math/0703503v1)。保留的 gzip 原始对象为 28,055 字节，SHA256 ac056c937b948497233c09c14fbdb537bd832356e4d51766aa619abef643f03a；解压出的单个 TeX 为 95,346 字节，SHA256 0f68b7155f97b36df324442b8e9f32f0dbd84919931a8618c9391976d6f93698。该版本的原有注释、排版和草稿文字保留，来源不是期刊终版的替代认证。

核对范围包括 Essential LCD 定义、Small Ball Probability 的基本及精确版本、特征函数／Esseen 归约、算术返回集的间距与密度证明、random normal 与 strong distance 假设，以及张量化、level-set net 和最后一列条件化的完整操作性推导。原始标签包括 `t: small ball intro`、`t: small ball precise`、`Esseen`、`l: scattered`、`rec via LCD`、`random normal`、`l: single`、`l: level` 与 `strong conditioning`。

精确小球定理要求独立同分布的中心化、方差一随机变量，其三阶绝对矩有界于 $B$；系数向量预先固定且 $1\le|a_k|\le K$，并要求 $0<\alpha<1/(6K)$、$0<\kappa_{\mathrm{source}}<n$。常数显式含有 $BK^3$，余项含 $\exp(-c\alpha^2\kappa_{\mathrm{source}}/B^2)$。Essential LCD 要求除规定数量的坐标外，其缩放值接近非零整数。它不是对观察完同一批和项以后再选取系数的统一定理。

随机法向结论通过独立坐标矩阵的层集覆盖得到算术信息：先对 $n-1$ 个独立标量小球事件张量化，再支付网格大小；最终距离估计还条件化于前 $n-1$ 列并使用独立的最后一列。本章的法向由同一个校准计数数组的共振三元组生成，没有相应的独立末列或逐行矩阵模型。其系数也可能为零或有增长的比值；重复系数结构未被证明具有大的 LCD。因此这些定理及其常数均未直接移植到本章的自适应法向事件。

第 173 章直接证明原始条件乘积核和商余数总变差关系，再分别控制法向选择所留下的概率缺口。它复用第 155 章的无条件供给比较、第 165、167 章的完整后验与平面接口，以及第 170 章合法范围内的零分支结果。所有揭示视图属于同一实际数组；数学分析中的配对坐标仍保留在物理观测与完整后验中。经典方法保留原归属，新的模型综合及剩余式 (173.34) 的边界由正文承担；有限来源核对不表示全球原创或检索穷尽。

## 谱边界第 174 章补充：有限电荷截断、端点展开与共同误差相消

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 174 章给出全谱场尺度上原始负号总归一化量的右半平面端点公式。有限电荷截断使重组后的表示可解析地跨过附加精度零点，完整电荷尾仍按同一个原始噪声因子支付。一个明确非空区域内，整线项与补入半线项均指数大于其差；总差具有 $O(\delta)$ 相对及未缩放相位误差，且无零点。幸存原始电荷是 $\sqrt\delta$ 的端点尺度，非四次振荡零曲线与相位反演仍未解决。

A. Fernandez、E. A. Spence 与 A. S. Fokas，*Uniform asymptotics as a stationary point approaches an endpoint*，[保留原始 PDF](https://arxiv.org/pdf/1707.07927v2)。PDF 横幅标为 arXiv:1707.07927v2、2018-01-02，而保留首页文本显示 2021-06-13；这两个日期读数的差异未作版本调和。原始 PDF 为 424,462 字节，SHA256 b688475265e9ad344276baa0f86f9feea101596627710173e0e91f0c7c92f3af；保留文本为 70,394 字节，SHA256 25955cbc33b82c837c53756453f524ad334efaf78b01622c7f05d2ba80e286b2。文本仍有字形与间距缺陷。

核对范围包括 Definition 1.1 的相位及支割、参数区间 (1.1)、角度与衰减条件 (1.4)–(1.5)、Theorem 1.1 与 Remark 1.2；Theorem 1.3 的 $\sigma=1/2$ 限制、分割尺度 (1.22) 以及一致展开和有序一致渐近展开的区别；第 2.1 节的解析、单驻点、多项式振幅及收敛射线条件，第 2.2 节的全局映射和第 2.3 节至 Lemma 2.1；Lemmas 3.5–3.6 的局部变动与加权外部控制陈述；第 4.1–4.3 节至 Lemma 4.1 的陈述和起始论证，以及 Corollary 4.2、Lemma 4.2 的角度及符号论证。这不是对每一页或全部证明的核验。

该论文要求逐项证明二次端点变换所产生的参数依赖振幅具有一致余项界。其第 4 节分别处理有限和无穷轮廓，先建立相位导数及衰减界，再合并误差。本章沿用这一区分：有限电荷区间移除额外表示奇点，再对同一电荷条件下的能量 Fourier 尾及完整电荷尾给界。论文的特定对数相位、固定 $\delta$ 和 $\sigma$、参数区间、单驻点和轮廓角限制不等于这里的有限非中心谱与物理 $\sigma\to0$，其定理没有被直接移植。

保留提取文本在式 (1.10) 附近写“positive real axis”，而所列公式在非负 $\Lambda$ 时带负号；Lemma 4.2 附近的提取微分文字亦未作为本章轮廓的依据。未验证这些方向或链式微分问题来自原 PDF 排版还是提取，因为未取得能区分二者的独立读数；两处均不承担本章证明。本文使用的解析条件和关于参数一致余项的限制在已核对文字中明确给出。Bleistein、Erdelyi、Olver 等被引原始著作未作本章直接定理来源。

本章的新增综合是有限电荷组合、精度零点另一侧的有限能量鞍点、无逆噪声损失的尾界及共同误差下的完整总差公式。经典方法保留其归属；有限文献核对不表示全球原创、检索穷尽或提取无误。

## 谱边界第 175 章补充：实际均值的有理阶乘基准与共同中心边界

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 175 章由原幅度方程推出幅度超越及充分晚原始层上补偿得分对全部非负整数计数对的单射性。完整得分组恰对应单个计数对后，原局部比较成为固定截断内处处有效的相对误差界。对索引 $j>k$，两个同层实际均值的比值低于同一个有理阶乘基准，参考系数比值则高于它；首项补偿修正在相邻索引也大于实际行比较误差。不存在精确等系数的非对角整数共同中心，但非零宽近似条带中的原始同步仍未解决。

Faruk Temur，*Discrete fractional integrals, lattice points on short arcs, and diophantine approximation*，[arXiv:2012.10784v1](https://arxiv.org/abs/2012.10784v1)，[原始源文件](https://arxiv.org/e-print/2012.10784v1)。保留的原始对象为 24,895 字节，SHA256 3a916e4fcbcf43ff006730ac5a52a00aa355e77a627ce395f836a3dfada137dc。核对 Theorem 3 及其证明：对整数 $a$、非平方的 $-a$ 和 $\lambda>1/2$，它一致控制精确方程 $am^2+n^2=N$ 上的加权和。证明以不可取的二次剩余类、大筛和二进分层取得上界。这是整数二次曲线的集中上界，没有给当前移动超越 Gamma 曲线的正下界。短弧猜想与后续有限性讨论只用于定位关系；其中更深的 Schmidt／Pell 论证未移植。

Nicolas Brisebarre 与 Guillaume Hanrot，*Integer points close to a transcendental curve: an algorithmic approach*，[arXiv:2606.04858v1](https://arxiv.org/abs/2606.04858v1)，[原始源文件](https://arxiv.org/e-print/2606.04858v1)。保留的原始对象为 244,666 字节，SHA256 0ec90dee2859e5fded1cd6190ab4bc8192829116ec525bcd436a4d7d2e1df036。原始问题 `probgen` 允许固定正整数 $u,v,w$ 并寻找 $|f(X/u)-Y/v|<1/w$。核对该定义、`algo:2variables`、辅助小多项式的正确性证明、成功推论及失败条件，以及 `thm:cplx2D` 的复杂度证明。

该算法用整数小量关系把解限制为两个辅助整数多项式的共同零点；在结式非零时，消元可给候选列表。短向量不足或结式为零时算法可以失败，成功产生的列表也可以为空。复杂度结论固定函数及区间，并保留启发式互素条件。它没有断言候选数为正，也没有给原始稀疏指定层中的后继共同命中。本章未运行该算法，未验证当前变化 Gamma 族满足其全部解析条件；核对范围以外的行列式／插值发展和实验结论不作为前提。

第 175 章的证明不依赖上述两篇论文的定理，而使用明确写出的代数整数范数、有理函数阶数、Taylor 与阶乘赋值论证，并复用原模型卷定理 17.2 和式 (72.8) 的实际路径／平稳对比较。文献用于辨明精确格点、候选枚举和正下界之间的差别。当前模型综合不构成全球原创或检索穷尽声明；原始 $E_2$ 的存在、空性及统一有限 $H$ 的无限同步分支仍未解决。

## 谱边界第 176 章补充：自适应法向量与同时整数直线计数

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 176 章在同一原始计数方块上同时计数所有本原方向，利用每条整数直线的格点间距随高度增长，将主要概率代价从 $K^2/g$ 降到 $K/g$。法向量允许依赖被计数的两枚余数。对原始 $\beta\ge3/5$，由此控制一段指数增长的小约化 $J$ 范围；更大的约化整数生成事件与完整物理带宽扩展仍未解决。

Mark Rudelson 与 Roman Vershynin，*The Littlewood–Offord Problem and invertibility of random matrices*，[arXiv:math/0703503v1](https://arxiv.org/abs/math/0703503v1)，[原始源文件](https://arxiv.org/src/math/0703503v1)。保留的原始对象为 28,055 字节，SHA256 ac056c937b948497233c09c14fbdb537bd832356e4d51766aa619abef643f03a；原始 TeX 为 95,346 字节，SHA256 0f68b7155f97b36df324442b8e9f32f0dbd84919931a8618c9391976d6f93698。

核对该版本的小球概率定理、递归集合的间距与密度证明、随机法向量的假设，以及单向量、网、层集和最终条件化的证明。小球定理要求独立同分布的中心化方差一变量、有界三阶绝对矩，以及固定的系数向量；其常数与系数高度、矩界和辅助参数有关。递归间距证明始终使用同一固定向量，并不允许事后由被观察变量选择系数而保持原界。

随机法向量论证另用独立坐标矩阵、独立行及相应矩和范数控制；最终距离证明在揭示前若干列后使用独立的末列。当前法向量却由同一个计数方块生成，尚无这样的独立末列，也没有证明它的重复系数具有所需的大最小公分母。因此该论文没有直接控制第 176 章仍剩余的大约化整数事件，更不能在指数增长的高度下省略依赖常数。

第 176.3 节用本原二元整数方程的完整步长证明直接建立所需的有限并集界，随后应用第 173 章已经证明的实际联合分布与平均条件总变差控制。上述论文提供算术间距和随机法向量之间的研究关系，其成熟定理未被冒领为当前模型的新证明。新综合及文献适用范围均限于正文所列量词；不含全球原创性、检索穷尽、锐性或原始物理反例的声明。

## 谱边界第 177 章补充：可达鞍点、端点定向系数与有限谱相位

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 177 章在固定的非零全谱场区域内证明原始负号总归一化量的两项相干振幅展开。能量鞍点在一个包含端点的复电荷圆盘上得到相对控制；有限矩形的端点与鞍点定向系数均为 $+1$，连接段和实电荷尾分别有明确界。有限谱相位给出逆像区域内的简单零点、连续标签与无额外零点结论。误差控制保留同一个原始噪声，未声明全局延拓、最早 Stokes 转换或最近零点。

T. Bennett、C. J. Howls、G. Nemes 与 A. B. Olde Daalhuis，*Globally exact asymptotics for integrals with arbitrary order saddles*，[arXiv:1710.10073v2](https://arxiv.org/abs/1710.10073v2)，2018 年 2 月 8 日版本，[原始 PDF](https://arxiv.org/pdf/1710.10073v2)。保留 PDF 为 5,524,442 字节，SHA256 06e285acd9772ea2f15dab1a31640cccf0f862fe99ae89c86a852ca3ef876634；原抽取文本为 89,480 字节，SHA256 dc55582ddf86c76e6362cf8437ebd92651c8a5e1250f5e7021704587bb9916c4。抽取中的字形、间距与 NUL 缺陷不由空诊断流消除。

核对引言、第二节的解析域与无穷远轮廓条件、相邻鞍点定义、角遭遇区间、定向和精确余项表示，以及附录 C 中边界路径取得相反定向的证明。其逆映射 $s=f(t)-f_n$ 在对应 Riemann 面上延拓；“障碍仅来自鞍点像的分支点”使用域闭包上的全纯性和沿域中无穷远的 $|f(t)|\to\infty$。主要设置还要求收敛的无穷远端轮廓、有限个相邻鞍点、遭遇前的角区间，以及相应轮廓上的单鞍点条件。

这些全局条件没有在当前有限谱、正谱极点、精确低元组对数和电荷端点并存的模型中建立。相位对齐本身也不能决定轮廓系数。第 177 章直接使用一个有界矩形，证明水平段的二次实部衰减和端点段的单调衰减，逐段给出定向系数，并另付完整实尾。因此所需的是正文写出的局部构造和原始概率律回接，不是对该论文全局结论的无条件调用。

原始 full-$q$ 系数回接、非中心条件圆盘、有限谱相位及共同噪声因子的统一误差属于本章的模型综合。经典解析工具和定向机制保持原文归属；其他已引文献只在既有核对范围内使用。本章不以形式鞍点、有限阶累积量或图形证据替代实际可达性，也不宣称全球原创、检索穷尽或 Lean 形式认证。

## 谱边界第 178 章补充：原始校准的离散随机性与固定总数选择

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 178 章构造一个不改变任何计数线重数的原始标签池。合法揭示后，其类别计数为精确二项变量；完整外部后验校准量对每次类别变化有统一的 $q^{-1}$ 级精确间距。由此得到原子小球界，并对原始 $\beta\ge2/3$ 排除一类大 $|J|$、小约化截距分母的实际生成平面。其余实际事件与物理带宽扩展仍未解决。

Hélène Boistard、Hendrik P. Lopuhaä 与 Anne Ruiz-Gazen，*Approximation of rejective sampling inclusion probabilities and application to high order correlations*，[arXiv:1207.5654v1](https://arxiv.org/abs/1207.5654v1)，[原始源文件](https://arxiv.org/src/1207.5654v1)。保留源对象为 13,365 字节，SHA256 258b7a04a6e18116eb0d9a8e8ae290f84b94622cc05f85bab55c546eecf9953b；原始 TeX 为 40,204 字节，SHA256 54c68cc91f9e753e985112b4e57d09d30b57232b2c0aab0e1fc5a1bcb6842218。

核对该版本的拒绝抽样条件、固定阶包含概率展开，以及中心概率比、有限删除引起的均值与方差位移、固定阶累积量和正中心归一化的证明。辅助 Bernoulli 概率之和须等于条件化的整数，方差和须趋于无穷；包含阶数固定，误差对该阶数的索引一致。原文并未证明自适应数据校准量的反集中，也没有为增长删除阶数提供本章所需的一致误差。

本章使用正权重与 Bernoulli odds 的精确对应，每次只比较一对标签及一个锚；所需四个固定偏移的 $O(D_o^{-2})$ 比值界使用第 132 章的直接 Fourier 推导。该证明以二阶及以上固定阶累积量由方差控制为依据，不使用原文“any positive integer m”字样来主张第一累积量与方差之比普遍有界。第 145、163 章的局部公式在同一外部数组上比较两个有限分配，不对余项求导。

合法线外标签池、完整外部校准的精确单步间距、可测条件小球界，以及对自适应截距的有理值并集是第 178 章的模型综合。经典固定总数选择、二项原子界及有理值计数保留其既有归属。另一个历史文件名含 Petrov 的材料，经标题核对实际署名 Mitalauskas 与 Statulevičius，且 OCR 有损；本章未从该材料采用定理或常数。

本文献核对限于上述版本与条件，不构成检索穷尽或全球原创声明。理论正文没有把扩大事件与实际事件混同，也没有将已经排除的一类截距视为完整物理定理的证明；本补充不宣称 Lean 形式认证。

## 谱边界第 179 章补充：跨尺度相位延拓与零点整数标签

[谱边界卷](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md) 第 179 章用同一个精确有限剖面连接共存尺度和固定全谱尺度的原始负号总量零点。移动电荷尺度的加权余项、定向轮廓、保留原始噪声的尾界与收缩腰部上的相位逆映射共同给出连续的 $2N_Q$ 个简单零点；两端标签偏移为零，原始 $d(h-h_0)$ 坐标误差为 $O(t^{-2})$。结论限于所给连接域。

M. Biskup、C. Borgs、J. T. Chayes、L. J. Kleinwaks 与 R. Kotecký，*Partition function zeros at first-order phase transitions: A general analysis*，[arXiv:math-ph/0304007v2](https://arxiv.org/abs/math-ph/0304007v2)，2004 年 5 月 7 日版本，[原始 PDF](https://arxiv.org/pdf/math-ph/0304007v2)。保留 PDF 为 494,908 字节，SHA256 f5a6233564fa4004a8027a4443419df87c377119df703ca25b9ef877c84f171c；抽取文本为 152,798 字节，SHA256 affc5ec42248ec23a040fee1d1aeac573c604a2ec957c246d11d6f2ac618deff。字体与间距缺陷保留，非零抽取诊断不作无损来源声明。

核对 Assumption A(1)–(4)、Assumption B(1)–(4)、Remark 2、Theorem 2.3 的窗口条件 (2.19)，以及 Lemma 4.3 在第五节中构造对数分支与整数根标签的证明 (5.25)–(5.34)。主要条件包括正的相位包络、稳定区域中的全纯性、竞争相位对数导数的分离、非消失的有限体积相位近似、函数及其导数的指数相对误差，以及远离多相区域的指定窗口。原文通过控制振幅比的像及对数导数来选定分支，不能事后以观测零点拟合整数标签。

原文的固定导数常数与指数误差并未直接给出本章随尺度 $l$ 变化的逆映射和轮廓界。本章在同一实际数组中证明这些界，再以精确剖面恒等式和近一解析因子匹配两个既有区域。除去共同非零因子的做法也必须先证明本章端点振幅的下界；它本身不证明该下界或有向轮廓系数。

该版本抽取文本在 (5.31)、(5.32) 定义 $\varphi=\log F_L$、$\theta=\log(F_L/F)$ 后，后续文字使用的相位和号与这两个定义不一致。尚未判定这是抽取问题还是原排印问题；本章不采用该处符号等式，其振幅比、对数分支及相位差均在正文独立推导。既有原文边界保持原状。

本章新增的是模型中的加权跨尺度控制、连接域的单值逆相位与实际标签对应；经典解析工具和文献定理保留原归属。没有将一个局部连接结果提升为全局最大延拓、首次 Stokes 转换、最近零点或 Lean 形式认证，也不宣称全球原创与检索穷尽。

## 谱边界卷第 180 章补充：增长阶相对概率与实际均值 Poisson 逼近

对应 [谱边界卷第 180 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。归属为 `repo-derived`：精确有限秩路径生成函数、原始混合行类型与第 175 章全局得分单射性共同给出完整群的增长阶相对点概率估计，再经碰撞控制、实际均值校准和有限阶反演，得到均值总和至多 $\log q_*/128$ 的联合 Poisson 全变差界。该窗口在固定内部参数区间上为 $Q^3$ 阶；各均值可达 $Q^8$ 的一致逼近、非有界熵矩转移及 $E_2$ 同步问题仍未解决。

A. D. Barbour 与 A. V. Gnedin，*Small counts in the infinite occupancy scheme*，原文版本 [arXiv:0809.4387v1](https://arxiv.org/abs/0809.4387v1)，Lemma 2.1、Proposition 2.2 及其证明给出独立投球模型的定量去 Poisson 化。其尾箱界为 $\pi_k+2k\exp(-np_k/10)$，要求 $m\le np_k/2$。独立箱分配与剩余箱耦合不能直接替代本卷原始相关路径；Poisson 化箱占据数也不自动使“具有某占据数的箱数”相互独立且服从 Poisson 律。

Julia Eaton、Anant P. Godbole 与 Betsy Sinclair，*Competition between Discrete Random Variables, with Applications to Occupancy Problems*，原文版本 [arXiv:0806.1007v1](https://arxiv.org/abs/0806.1007v1)，以强制指定独立球进入一箱并条件重分配其余球构造耦合，多元占据结论使用均匀独立分配与 $n/N\to0$。本文所需的原始比例是 $T/(2M)=Q^3\to\infty$，事件带两种转移标记，路径观察相邻相关；原文耦合与误差界不作为本章原始路径定理的前提。

Nickos Papadatos，*On corrected Poisson approximations for sums of independent indicators*，原文版本 [arXiv:2304.10314v2](https://arxiv.org/abs/2304.10314v2)，讨论独立指标、阶乘矩距离与修正 Poisson 律。距离含 $\frac12\sum_m2^m|\Delta m_m|/m!$；其全变差控制在具有适当指数矩的类中成立，所引反演证明由原文归于 Afendras–Papadatos，修正律的相关现象归于 Barbour–Hall。原文展示的误差同样含 $e^{2\lambda}$。本章不将阶乘矩反演或该指数损失声称为新方法，不借用未核对的引文证明；正文给出有限多元反演、余项与原始路径增长阶输入的完整连接。

上述版本的相关模型、条件与所述原文证明已作有界核对；此归属不宣称全球原创或文献穷尽。实质新增部分是同一实际路径的增长阶系数控制、两种行类型的碰撞界与精确实际均值下的定量组合。

## 谱边界卷第 181 章补充：完整条件纤维的系数稳定性与实际法向量

对应 [谱边界卷第 181 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。归属为 `repo-derived`：对同一原始离线标签池的全部配置，保留精确校准量 $p(V)$，从原始正系数比得到 $d=-v/D+O(q^{-2})$，再证明 $d,h_0,h_1$ 的联合稳定界、原始谐波容差下的候选集夹逼，以及达到秩二时同一法向量的识别。原始参数满足 $\phi>c+\gamma+\kappa$ 时可控制完整谐波范围，此条件包括全部原始 $\beta\ge3/5$。余项中的自适应标量族概率尚无趋零界；这不扩展第 163 章已证明的物理带宽范围。

Hélène Boistard、Hendrik P. Lopuhaä 与 Anne Ruiz-Gazen，*Approximation of rejective sampling inclusion probabilities and application to high order correlations*，原文版本 [arXiv:1207.5654v1](https://arxiv.org/abs/1207.5654v1)，研究独立 Bernoulli 指标在总数为 $n$ 条件下的包含概率，其中 $\sum p_i=n$、$d=\sum p_i(1-p_i)\to\infty$。主包含定理固定 $k$，误差对所选指标一致；Bayes 证明比较具有固定均值、方差及累积量偏移的正中心概率。原文条件与对应证明已作有界核对。它不提供原始自适应法向量的分布或条件校准量的横向响应。

本章实际使用第 132 章已给出的统一局部比值证明，明确核对固定偏移 $[-3,1]$、最多四个固定删除、方差下界和正归一化常数。所需累积量界只用于阶数至少二；不将原文 “any positive integer m” 的表述当作一致的一阶累积量与方差比较。配置间误差通过两个端点的绝对余项相减控制，未对渐近余项求导，也未把固定阶展开升级为随 $Q$ 增长的删除数。

有限 Bernoulli 条件化、根稳定性、整数行列式与二维张成空间的比较是既有方法。本章新增的是这些关系在同一原始数组和指数谐波尺度下的定量组合。双标签池在该容差下的额外系数变化仍低于分辨尺度；这仅限制此表示的直接用法，不是物理后验反例。此归属不宣称文献穷尽或全球原创。

## 谱边界卷第 182 章补充：有限谱 Schur 曲率与原始实窗口

对应 [谱边界卷第 182 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。归属为 `repo-derived`：保留实际非中心向量与全部低群的有限混合，得到电荷 Hessian 中的精确项 $\operatorname{Var}_w(c_L)/S(s)^2$，与能量曲率的 Schur 补共同控制显式负能量区间上的唯一实分支。该区间到达零点处行列式 Taylor 级数不收敛的谱尺度；实剖面曲率及原始计数窗口的相对近似均在该实际区间上证明。此结果不提供新的复积分贡献系数、等振幅域或总零点数。

Bernard Bercu、Jean-François Bony、Vincent Bruneau，*Spectrum of the product of Toeplitz matrices with application in probability*，[arXiv:0712.1302v1](https://arxiv.org/abs/0712.1302v1)，2007-12-10。本章所用文献比较核对 Theorems 2.3–2.4 及第 3 节的行列式累积量、率函数与 Corollary 3.1。谱定理涉及连续实符号及非负 $g$；Gaussian 应用假设中心化平稳过程、有界正且非零的谱密度 $g$ 和连续实测试符号 $f$。极端谱点可以使率函数出现仿射部分，不能仅以符号乘积的值域代替完整谱域。

本章条件协方差是有限对角矩阵减去秩一项，没有假设平稳 Toeplitz 表示或确定极限符号。原文的实大偏差原理不提供此处的非中心低群混合、窄噪声下的相对余项、复贡献系数或常数阶相位；其 Corollary 3.1 调用的参考文献 [1] 未在本次比较中核读，因此没有将依赖该来源的结论作为本章证明。有限 Gaussian 条件化、log-sum Hessian、Schur 补、Fourier 反演和实参数鞍点展开均为经典方法；正文直接证明所需的有限数组关系及原始律回接。

文献核对的范围限于上述版本与段落，保留既有提取字形及未读证明边界，不宣称文献穷尽或全球原创。新增组合的实质在于精确混合方差、实际能量根、完整实积分控制与原始计数窗口属于同一个实现，且除原有噪声保留量外不另加速率假设。

## 谱边界卷第 183 章补充：精确条件标签与增长均值联合 Poisson 定律

对应 [谱边界卷第 183 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。归属为 `repo-derived`：完整三类轨迹下的标签乘积律、原始两步重置给出的总数方差界，以及同一标签序列上的增删耦合，共同给出一个或两个完整得分群的联合全变差界。第 175 章提供完整群识别，第 180 章提供一行相对概率的实际均值校准；本章的新连接使误差对均值仅多项式增长，覆盖各实际均值至多 $Q^8$ 的窗口。该结论分别适用于原始 pair 与依赖 path，且在固定内部参数紧区间、确定支持及原始内部指标弧上一致。

A. D. Barbour，*Univariate approximations in the infinite occupancy scheme*，[arXiv:0902.0879v1](https://arxiv.org/abs/0902.0879v1)。原始 TeX 的模型、两条主定理及第 2 节条件构造与论证方向已核对。原文将独立球放入固定概率的无限箱，对单个计数采用由均值与方差确定的平移 Poisson 近似；$r$ 次占据数定理保留 $n\ge\max(n_0,e^{r/4},2r)$ 等条件，不给本章随层变化的双计数目标提供统一常数。其构造先以 $p_j/P_0$ 分配，再独立以概率 $P_0$ 稀疏化，在分配总数给定后得到独立 Binomial 变量。之后还需要条件方差及条件均值的 Stein 误差估计。原文引用的 Röllin 定理、独立 Bernoulli 既有界及后续详细估计未在此作为未读前提引入。

A. D. Barbour 与 A. V. Gnedin，*Small counts in the infinite occupancy scheme*，[arXiv:0809.4387v1](https://arxiv.org/abs/0809.4387v1)。Lemma 2.1、Proposition 2.2 及其证明的条件 $m\le np_k/2$，用于先排除高概率箱，再以 $\pi_k+2k\exp(-np_k/10)$ 比较剩余多项数组与 Poisson 化数组。其证明调用的 Le Cam/Michel 数组比较界没有直接承担本章依赖路径的证明；正文另行推导目标统计量的增删代价、同排类别互斥与精确均值校准。

Poisson 化、条件化与共同序列耦合是成熟方法。本章保留同一原始三类轨迹的四个相关总数，只对给定类别后的具体标签使用已证明的独立性，不把原始路径行替换成独立行。新界不要求群均值有正下界，但全变差只控制有界检验，不能据此转移非有界熵矩；亦不证明指定双均值的同层实现或算术同步。文献比较限于上述原始版本与已核对段落，不宣称全球原创或检索穷尽。

## 谱边界卷第 184 章补充：中心化非中心能量轮廓与复剖面管域

对应 [谱边界卷第 184 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。归属为 `repo-derived`：围绕实际能量鞍点中心化的精确高斯恒等式，使非中心项在 $\pi/3\le|\theta|\le\pi/2$ 射线上实部非正；保留谱块的行列式衰减随后支付完整无限能量轮廓。正文由此证明固定复宽度的连通剖面管域、解析能量根的拼接、精确低模混合非零性与相对 $O(\delta)$ 误差，并在第 179 章的小电荷域与第 182 章的 Taylor 域外实分支之间建立实际开重叠。轮廓微分中的因子 $i$ 与反演前因子的 $1/i$ 相消；共同的原始噪声归一化保留到以 $g(0)$ 归一化后才相消。

Nico M. Temme，*Uniform Asymptotic Methods for Integrals*，[arXiv:1308.1547v1](https://arxiv.org/abs/1308.1547v1)。该版本 arXiv 标记为 2013 年 8 月 7 日，正文首页日期为 8 月 8 日。核对第 2.1 节的 Watson 解析域、增长假设与严格角域余量，式 (2.12) 周围的旋转后收敛条件，第 2.3 节的解析轮廓及分支避让要求，以及第 4.1 节移动极点的显式分解和一致性域。原文是作者对成熟方法的综述与论述，不是其中所有方法的历史原创证明；其指向的文献 [21]、[5] 及 van der Waerden [39] 未在此作为未读证明前提引入。

第 4.1 节针对在无限条带内解析的振幅及实际极点 $t=i\alpha$，分离显式 erfc 项，并在极点穿越时处理变形或留数；一致性要求 $i\alpha$ 留在条带的严格内部。本章不将端点渐近式中的 $H-a_1$ 直接等同于该实际极点，也不凭 erfc 记号借用周期系数。本文另行证明模型特有的中心化射线界、噪声一致余项及低模混合下界；Temme 的角域与增长假设不能自动完成这些步骤。

高斯变换、Cauchy 变形、Rouché/解析隐函数论和局部鞍点积分均为成熟工具。新连接的结论止于能量轮廓和有限电荷变形：总电荷等幅延拓、总尾相对控制及新零点标签仍待证明。普通理论推导不冒称 Lean 核验或全球原创；文献核对范围限于上述版本及段落。

## 谱边界卷第 185 章补充：无均值上限的原始群联合 Poisson 定律

对应 [谱边界卷第 185 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。归属为 `repo-derived`：第 180 章的显式系数估计在 $h=q$ 的整个信号数组上求和，并支付原始数组及参考数组的尾部；第 183 章的共同标签构造仅改变背景总数，从而产生与仍属实际分布的信号数组独立的参考背景。精确得分关系控制背景目标行质量，共同条件类别核再把多元互斥代价降为每行目标概率。所得定理对各实验自己的实际均值成立，无额外均值上限；全变差仍不自动控制非有界矩。

Louis H. Y. Chen 与 Aihua Xia，*Stein's method, Palm theory and Poisson process approximation*，[arXiv:math/0410169v1](https://arxiv.org/abs/math/0410169v1)，*Annals of Probability* 32(3B), 2545–2569 (2004)，DOI [10.1214/009117904000000027](https://doi.org/10.1214/009117904000000027)。核对原始电子重印版的 Palm/Stein 恒等式、Theorem 2.3 的局部误差分解、第 3 节度量与 Theorem 3.1，以及第 5 节占据模型、Theorem 5.2 和重新分配证明。原文令 $\rho_0\equiv0$ 时给出总点数的全变差；一般归一化匹配度量不是类别向量的完整全变差。其占据模型使用独立球及低阈值事件 $X_i\le m$，不能直接成为本章依赖路径、精确双计数目标的耦合。原文引用的 Stein 因子和方差估计之未核对原始证明，不作为本文输入；提取中存在字体编码诊断，编码不明的公式片段不承担数值常数。

Nickos Papadatos，*On corrected Poisson approximations for sums of independent indicators*，[arXiv:2304.10314v2](https://arxiv.org/abs/2304.10314v2)，沿用第 180 章的文献归属。其独立指示变量 Poisson 界将因子 $(1-e^{-\theta})/\theta$ 归于既有 Chen–Stein 工作，包括 Barbour–Eagleson 与 Barbour–Hall。第 185 章使用稍弱的 $\theta^{-1}\sum_i p_i^2$，并给出完整标量差分证明及共同条件 Multinomial 标记核的提升；这一经典标量界不算本章新结论。Barbour 的 arXiv:0902.0879v1 条件占据构造仍按第 183 章说明其独立球、平移 Poisson 及方差条件边界。

本章新增的是原始信号全数组、只改变背景的共同实现、精确得分质量比及均值一致类别界之间的连接。它不借用点过程度量替代向量全变差，不假定路径行独立，不由单一均值接近代替联合概率证明。文献比较限于上述版本及已核对内容，不宣称全球原创、检索穷尽或 Lean 核验。

## 谱边界卷第 186 章补充：总电荷尾部与有限复轮廓连接

对应 [谱边界卷第 186 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。归属为 `repo-derived`：在第 182、184 章的实际混合分支与复能量管上，选择能量倾斜为 $-M$ 的实现截断，证明整个实电荷尾部及终端复连接段的统一指数界，并用完整选择系数回接原始总量。精确归一化对数保留低频混合和物理噪声；误差相对于非零的 $g(0)\sqrt\delta$ 控制，不宣称总量在抵消区域的相对误差。

T. Bennett、C. J. Howls、G. Nemes 与 A. B. Olde Daalhuis，*Globally Exact Asymptotics for Integrals with Arbitrary Order Saddles*，[arXiv:1710.10073v2](https://arxiv.org/abs/1710.10073v2)，版本日期 2018 年 2 月 8 日；正文另列编辑部收稿日 2017 年 10 月 27 日。核对第 2 节的解析域、角区间 (7)、邻接与方向指标 (8)，第 3 节围绕 (20)–(22) 的轮廓变形与绝对可积条件，第 5.1 节的简单鞍点表示，以及附录 C 的逆映射拓扑和方向证明。原文要求函数在扫过域的闭包解析、相应相位模在无穷远发散、相关最陡路径通向无穷远而非奇点，并有非空有限的邻接鞍点集；余项还要求各邻接路径上的绝对积分及扫过域内无分母零点。这些条件不能由局部能量鞍点或作用量相等替代。已存提取含字形与 NUL 缺陷，空警告文件不表示提取完美；未核对的角余项范围不作输入。

本章不直接移植该文的全局循环系数，而是在已证有限解析域内支付尾部与连接段。深实分支上的振幅失配仅排除指定端点/单鞍点表达式的局部平衡，未确立那里的实际电荷系数、全部竞争鞍点或原始零点不存在。复中段继续延拓仍是开放证明义务；不宣称全球原创、检索穷尽或形式核验。

## 谱边界卷第 187 章补充：原始律指数包络与非有界波动转移

对应 [谱边界卷第 187 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。归属为 `repo-derived`：第 183 章的精确条件标签分配和第 185 章的无均值上限联合全变差，在此由实际依赖总数的指数集中、实倾斜条件概率之分子/分母同阶平滑，以及三段指数加权尾部估计接合。所得实际律指数包络允许最大耦合转移矩母函数和四阶导数；非有界量的支付不来自全变差本身。

Jay Bartroff、Larry Goldstein 与 Ümit Işlak，*Bounded size biased couplings, log concave distributions and concentration of measure for occupancy models*，[arXiv:1402.6769v3](https://arxiv.org/abs/1402.6769v3)。核对原始 TeX 的 size-bias 定义、一般尾界定理 `thm:main` 及其单侧有界耦合条件、配置耦合定理 `+1-1:generally` 与条件律证明、多项分配定理 `thm:multocc`、引理 `lem:multinomial` 的重新分配证明，以及附录中左尾去掉单调条件的论证。多项分配定理分别研究阈值计数 $Y_{\ge}$ 与“不等于指定值”的计数 $Y_{\ne}$；后者使用补集均值，不能直接给稀有精确双计数事件的均值尺度。独立球、单计数占据模型也不等于未经条件化的依赖路径。

原文一般定理将更强尾界归于 Arratia–Baxendale；未核对该被引原始证明，不将其作为本章输入。$Y_{\ne}$ 配置证明末尾印出的 $\mathcal L(Y(N_{\ne}))=\mathcal L(Y_{\ge}^s)$ 与该处目标记号不一致；不把修正后的等式当作本文前提，也不据此否定整篇定理。本章直接证明所需的条件实倾斜界和原始总数集中，未从文章标题、补集操作或未证的有界耦合取得实际律结论。

上述检索与核对仅界定已检查版本的迁移范围；不宣称全球原创或检索穷尽。标准化波动的对数加权绝对值可按本章给定界转移，仍不等于全数据后验熵或完整惊异度的转移；本章不解决 $E_2$。

## 谱边界卷第 188 章补充：实际稀有计数组的无上限相对熵

对应 [谱边界卷第 188 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。归属为 `repo-derived`：第 183 章的同一实际总数条件分配、第 185 章的无均值上限联合全变差和第 187 章的实际指数包络，在此通过新增的联合点概率界接合。结果针对一或两个预先指定的完整原始群，以各实际实验自己的精确均值为独立 Poisson 参考参数，给出 $O(Q^{-3/2}\log Q)$ 相对熵误差。有限参数条件、极小与零均值处理均在正文写明；不覆盖增长维数、全部数据的后验熵或共同层同步。

Ioannis Kontoyiannis、Peter Harremoës、Oliver Johnson，*Entropy and the Law of Small Numbers*，[arXiv:math/0211020v2](https://arxiv.org/abs/math/0211020v2)，[固定版本原始 TeX](https://arxiv.org/src/math/0211020v2)。其 Proposition 1 对可能依赖的 Bernoulli 指标给出

$$
D\!\left(\mathcal L\!\left(\sum_iX_i\right)\middle\|
\operatorname{Pois}\!\left(\sum_ip_i\right)\right)
\le\sum_ip_i^2+\sum_iH(X_i)-H(X_1,\ldots,X_n).
$$

证明用求和的数据处理、联合到乘积律的散度恒等式以及 Bernoulli 到 Poisson 的散度界。右端总相关项对占位指标及依赖 path 不自动为零；在本模型实际达到的中心信号群上，平方和项还可具有 $q/\lambda^2$ 量级，故该界自身不支付本章无均值上限的目标。

同文 Theorem 1 的较强界 $\lambda^{-1}\sum_i p_i^3/(1-p_i)$ 要求独立 Bernoulli 指标。所核对的 Proposition 2、Proposition 3 及卷积条件投影证明保留其独立性与 scaled-Fisher/log-Sobolev 前提；中间卷积引理的显示陈述未重复写出的独立性仍是其卷积证明的条件，不能移植为依赖行指标定理。其引用的 Bobkov–Ledoux 原始 Corollary 4 未独立核对，不承担本章证明。

固定 v2 的 Proposition 2 有限支持证明含字面不一致：写 $P^\varepsilon=(1-\varepsilon)\mathrm{Po}_\lambda+\varepsilon P$，随后却称 $\varepsilon\downarrow0$ 时趋于 $P$，并把尾部系数写作 $\varepsilon$；在已指定 $P(k)=0$ 的地方还写 $P^\varepsilon(k)/P(k)=\varepsilon$。这些行不作隐式修补或本章证明步骤，也不据此否定整条定理。本章的估计由正文的格点平滑与正似然残差直接推出。

文献范围是固定版本所述命题、定理及上述证明接口。其它检索线索不承担定理主张，也不据此声称文献穷尽或全球原创性。经典工具与本模型的新增综合推导分别归属。

## 追加锚（本行以下为增补区）

## 谱边界卷第 189 章补充：全部截止计数组的联合相对熵

对应 [谱边界卷第 189 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。归属为 `repo-derived`：在第 183 章的精确条件分配、第 187 章的实际总数尾界及第 188 章的加权单行概率界之上，证明整个原始截止计数线直方图到精确实际均值乘积 Poisson 律的联合相对熵为 $O(Q^{-1})$。固定 $J\Subset D$、固定 $C_0\ge1$、确定支持，实际 pair/path 分别成立；群数为 $\Theta(Q^2)$，实际均值无附加上下限。条件信息代价在同一实际总数律上积分，有限层条件和异常总数支付均见正文。

Rohit Agrawal，*Finite-Sample Concentration of the Multinomial in Relative Entropy*，[arXiv:1904.02291v4](https://arxiv.org/abs/1904.02291v4)，[固定版本原始 TeX](https://arxiv.org/src/1904.02291v4)，[期刊 DOI](https://doi.org/10.1109/TIT.2020.2996134)。其显示定义 `intro_defn:multidiv` 是独立多项样本的随机经验散度 $V=D(X/n\|p)$；主 MGF 定理给出

$$
\mathbb E e^{tV}\le(1-t/n)^{-(k-1)},\qquad 0\le t<n.
$$

已核对定义、尾定理、MGF 定理、多项到二项归约的完整证明、二项 MGF 证明及两个多项式引理。归约条件于一个多项坐标，使用剩余坐标的精确多项分布与经验散度链式分解；二项步骤使用成功概率上的对数凹性及有限多项式恒等式。经验向量的随机散度与本章两个计数向量分布之间的相对熵是不同对象，该定理不承担本章 (189.1) 的证明前提，也不把其条件多项律移植为无条件 path 行独立性。

固定 v4 的若干字面记法有边界：定义前散文所述方向与显示 $D(X/n\|p)$ 相反；多项归约首个概率向量末项写作 $p_n$，字母表大小为 $k$；`lem:bound-zero-p` 开头的 $G_n(0,x)$ 求和漏写定义及后续系数计算所含的二项系数。这些行不作本章恒等式，也不据此否定整条 MGF 定理。期刊其他版本及该文引用的未核对原始结果不承担这里的推导。

第 188 章所述 Kontoyiannis–Harremoës–Johnson 依赖指标界仍需总相关项；本章以整个条件直方图的估计支付该项所代表的联合信息问题。经典工具与本模型的新增连接分别归属；不主张检索穷尽、全球原创性、全部数据后验熵或共同层同步结论。

## 追加锚（本行以下为增补区）

## 谱边界卷第 190 章补充：原始概率律中的共同近共振

对应 [谱边界卷第 190 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。归属为 `repo-derived`：把原完整选择后验的交换身份与补偿尺度、同一数组上的整数重数及一维鸽巢逼近结合，在每个原固定 $\beta>3/4$、$c>3c_q/2$ 下，证明指定正项 Fourier 总和具有支持一致的正期望下界。pair 与平稳依赖 path 分别成立；实际经验事件概率、非中心项、噪声和谐波截断均在正文支付。结论阻断该正项均值充分判据，不构成原后验方差熵的物理反例。

Francesco Cellarosi、Tariq Osman，*Bounds for Smooth Theta Sums with Rational Parameters*，[arXiv:2306.11119v2](https://arxiv.org/abs/2306.11119v2)，[固定版本原始 TeX](https://arxiv.org/src/2306.11119v2)。核对其完整 Introduction、Uniform Bounds 中 `L2.1Bdd` 引理及所给证明、`remark-size-constant`，以及所给 Gaussian theta 应用推导。该局部引理要求 $\operatorname{dist}(\xi_2,\mathbb Z^k)>0$、$f\in\mathcal S_\eta$、$\eta>k$ 和 $y\ge1/2$；常数显式为

$$
C(k,\xi_2,\eta)
=2^{(2\eta-k)/4}\sum_{n\in\mathbb Z^k}\|n-\xi_2\|^{-\eta}.
$$

证明对 theta 展开取绝对值，应用衰减范数，再求和上述收敛级数；常数在相位趋近格点时发散。这个上界不提供原经验占据分布，也不给第 190 章需要的近共振下界或增长维数下的一致常数。

Introduction 中的光滑权重主定理要求至少一对参数等于 $(a/(2m),b/(2m))$，其中 $a,b,m$ 均为奇数且 $\gcd(a,b,m)=1$，并保留维数、分母、参数及权重的常数依赖。该条件未被证明适用于这里的原经验后验，所以该主定理不承担 (190.18) 的证明前提；其所引重尾分类及随机 Lebesgue 参数结论也不转移。Gaussian 应用中的数值优化和若干显示式的字面归一化记法不用于本章。所核对的局部引理及证明只界定非共振上界的适用边界。

第 190 章实际下界由正文的有限鸽巢证明和仓内原模型关系推出。经典逼近工具、既有原模型关系及本章的新组合分别归属；不宣称新的 theta 定理、原始物理阈值、检索穷尽或 Lean 认证。

## 追加锚（本行以下为增补区）

## 谱边界卷第 191 章补充：无上截断的联合计数信息

对应 [谱边界卷第 191 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。归属为 repo-derived：将原实际行的指数矩、参考质量负对数的二次计数界、直方图阶乘代价及不交群的逐行求和结合，支付整条非负计数线的尾部交叉熵，再接回第 189 章的联合核心估计和精确均值投影。两种原实际 pair/path 律分别成立，保留全部计数、补偿、取整和精确实际均值。固定证明分界不删除目标坐标。结论为联合相对熵 $O_{J,r}(Q^{-1})$；不推断 E2 或完整数据后验熵。

Lasse Leskelä，*Information divergences and likelihood ratios of Poisson processes and point patterns*，[arXiv:2404.00294v2](https://arxiv.org/abs/2404.00294v2)，2024-08-04 版本，[原始 TeX](https://arxiv.org/src/2404.00294v2)。核对其点型和 Poisson 定义、有限强度似然比定理 the:PoissonDensityFinite 及完整证明、the:PPPRenyi 与 the:PoissonKL、有限强度散度引理 the:PoissonRenyiFinite 的完整证明，以及 the:PPPRenyi 的完整分割证明。

有限强度似然比证明把 Poisson 点型展开为 Poisson 个独立位置；散度证明比较两个 Poisson 律，通过共同控制强度及零密度支撑处理绝对连续性，并由 Rényi 极限得到 KL。其一般强度扩展使用两个 Poisson 过程在不交区域上的独立限制和张量化。KL 被积函数为 $f\log(f/g)+g-f$；在有限离散指标集上，它给出 (191.20) 的 Poisson 参考之间的括号和。

该来源的第一个概率律也必须是 Poisson。原依赖直方图不满足这个前提，因此不能把上述括号和当成其近似误差。本章的尾部交叉熵、实际联合熵链和精确均值投影由正文有限质量计算承担；该论文用于文献关系和适用范围定位，不承担 (191.1) 的原实际律误差界。

固定版本原始 TeX 有以下字面差异：Measures 段落在说明 $\lambda\ll\mu$ 时反写了零集蕴含方向；同段密度定义写成 $\mu(A)=\int_A f\,d\mu$，但所描述的是 $\lambda$ 对 $\mu$ 的密度。后续有限绝对连续性证明使用通常方向。有限散度证明的 $\alpha=1$ 交叉引用有两处混用强度与 Poisson 律参数；分割证明的一处标量质量写成 $e^{-sk}s^k/k!$，而前面定义为 $e^{-s}s^k/k!$。这些显示式不被导入为本章身份，也不据此否定整个来源的定理。

Cauchy–Schwarz、Poisson 指数矩、阶乘估计、熵链式身份和均值投影归于经典工具。原两步重置、核心联合信息界与本章新增尾部连接分别归属，不把重新组合自动称为文献原创，也不声称 Lean 认证。

## 追加锚（本行以下为增补区）

## 谱边界卷第 192 章补充：完整乘积共振与平滑参考障碍

对应 [谱边界卷第 192 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。归属为 repo-derived：将原完整计数窗口、共同后验包含概率和整数重数的近周期关系，接到保留实际中心的二项二次型方差估计，得到整个固定频率偏移区间上的精确补群、完整格点乘积和原选取输出特征函数下界。在固定 $\beta>3/4$、$c>3c_q/2$ 下，原实际 pair/path 各自具有支持一致、概率至少 $1/2$ 的事件，使选取输出与既有平滑参考的 $L^1$ 距离至少 $1/3$。该参考比较障碍不构成物理方差熵反例。

Daniele Agostini、Carlos Améndola，*Discrete Gaussian Distributions via Theta Functions*，[arXiv:1801.02373v2](https://arxiv.org/abs/1801.02373v2)，[固定版本原始 TeX](https://arxiv.org/src/1801.02373v2)。核对其 theta 定义、复离散 Gaussian 定义，以及标为 explicitmoments 的特征函数命题和所给完整证明。其记号为 $\mathbf e(z)=\exp(2\pi z)$，矩阵参数位于实部正定的 Siegel 右半空间，并排除归一化 theta 的零除子。特征函数身份为

$$
\mathbb E e^{iv^{\mathsf T}X}
=\frac{\theta(u+iv/(2\pi),B)}{\theta(u,B)}.
$$

证明在绝对收敛格点和中代入线性参数平移，再作局部 Taylor 展开。本章归一化整数 Gaussian 的源参数是 $B=\operatorname{diag}(1/(2\pi d_j))$、$u_j=m_j/(2\pi d_j)$；二者实值且 $B$ 正定，因此归一化分母为严格正实数。实温度 $\tau>0$ 同时乘到两者上；二次 Fourier 因子只作相应虚参数平移，不改变实部正定性。本章不假设复分子非零，也不取其对数。低方差群保留精确二项有限和。

整数线性相位 $\exp(2\pi i k^{\mathsf T}n)$ 对每个格点都是一，故格点周期性不提供任意相位下的一致衰减。原模型必须另外证明经验中心可以达到相应近周期、支付加权误差和原实际事件概率；这部分由第 192 章承担，而非该固定参数 theta 身份。

原文累积量证明的一处求和写为 $\mathbb N^g$，而定义分布和前面的特征函数证明使用 $\mathbb Z^g$；本章使用后者。均值、协方差的全局参数化、最大熵存在性、数值示例及复参数可识别性结论均非本章前提。原文也明确指出这些统计 theta 表达已有计算机科学文献来源；不把经典身份列为本章新意。

原窗口、有限选择补偿和格点比较依次沿用第 68、142、153、167、190 章。新内容是完整复因子的实际概率下界及其原选取输出含义，不是新的 theta 恒等式，也不是物理阈值或 Lean 认证。

## 追加锚（本行以下为增补区）

## 谱边界卷第 193 章补充：偏移计数线与联合信息速率

对应 [谱边界卷第 193 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。归属为 repo-derived：在原实际共同总数允许的二维强度带内，以沿原计数线的 Gaussian 和控制质量及平方距离加权和，连同任意正频率截止下的条件分配平滑，将保留全部坐标、使用精确实际均值的联合 Poisson 相对熵上界收紧为 $O(Q^{-5/2})$。pair 与平稳依赖 path 分别适用；领先系数、匹配下界及最优性未定。

José A. Adell、Alberto Lekuona、Yaming Yu，*Sharp Bounds on the Entropy of the Poisson Law and Related Quantities*，[arXiv:1001.2897v1](https://arxiv.org/abs/1001.2897v1)，2010-01-17，[固定版本原始 TeX](https://arxiv.org/src/1001.2897v1)。原文定义

$$
D(n,p)=D(\operatorname{Bin}(n,p)\|\operatorname{Pois}(np)).
$$

核对范围包括 Theorems 3、4、Theorem 3 的完整有限似然证明、二项 size-bias 与微分身份、标为 lem3 的积分表示、标为 propbi 的有限中心矩上下界及其完整证明。Theorem 4 把 $\mathbb E\log((B_{n-1,s}+1)/(ns))$ 的有限上下界在 $s\in[1-p,1]$ 上积分；条件是 $n,m\in\mathbb N$、$0<p<1$ 及二项律本身。其相关不等式来自对 $x\log x$ 与 $\log(1+x)$ 的有限余项控制。

原文分别给出固定 $p$、$n\to\infty$ 的

$$
D(n,p)=-\frac12[p+\log(1-p)]
       +\frac{p^2}{12(1-p)n}+O(n^{-2}),
$$

以及固定 $\lambda$ 的

$$
D(n,\lambda/n)=\frac{\lambda^2}{4n^2}+O(n^{-3}).
$$

这两种余项不自动适用于本模型中同时变化的标记概率和指数增长的标记均值。它们也不等于原条件分配直方图的联合信息：独立行参考的似然比可化为标记总数的二项似然比，原实际律还须支付共同总数条件化与混合。第 193 章不以这些渐近式作为定理前提，不据此声称原实际领先项。

Kontoyiannis、Harremoës 与 Johnson，[arXiv:math/0211020v2](https://arxiv.org/abs/math/0211020v2)，沿用第 188 章条目。Proposition 1 对依赖指标先支付总相关，再经数据处理比较 Poisson；Theorem 1 及 scaled Fisher information 的卷积论证使用独立加数。原 path 行不满足这一独立前提。此前记录的有限支撑混合表述问题保持原边界，不作为本章前提。第 191 章所引 Leskelä 的 Poisson—Poisson 相对熵公式也不替代本章依赖第一律的比较。

本章复用第 175、183、187–189、191 章。离散 Gaussian 求和和有效线宽是经典方法；新增关系是强度偏移与平方距离权重在原条件分配中的联合支付。不将来源自身的 Poisson 熵、独立行渐近或固定参考公式提升为原模型定理，也不主张全球原创性或 Lean 认证。

## 追加锚（本行以下为增补区）

## 谱边界卷第 194 章补充：完整直方图的匹配信息阶

对应 [谱边界卷第 194 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。归属为 repo-derived：在原振幅、取整、补偿、历史、时长和完整计数线下，对实际 pair 与平稳依赖 path 分别证明精确实际均值乘积 Poisson 参考下的联合相对熵为 $\Theta_{J,r}(Q^{-5})$。新关系是信号词过滤的全数组信息支付、中心化类别似然迁移、同一实际共同总数下的背景混合，以及完整线总计数的方差缺口给出的下界。领先系数仍未确定。

José A. Adell、Alberto Lekuona、Yaming Yu，*Sharp Bounds on the Entropy of the Poisson Law and Related Quantities*，[arXiv:1001.2897v1](https://arxiv.org/abs/1001.2897v1)，2010-01-17，[固定版本原始 TeX](https://arxiv.org/src/1001.2897v1)。复用范围为二项定义、Theorems 3、4、有限微分身份、Lemma 3 的积分身份及完整证明、Proposition `propbi` 及证明。有限积分身份给出

$$
D(\operatorname{Bin}(n,u)\|\operatorname{Pois}(nu))
=n\int_{1-u}^1\mathbb E\log\frac{B_{n-1,s}+1}{ns}\,ds
\le -u-\log(1-u)
\le\frac{u^2}{2(1-u)}.
$$

条件为任意正整数 $n$、$0\le u<1$，零端点按确定律解释。该有限界不需要固定 $u$ 或固定 $nu$，故适用于本模型的移动参数。原文固定参数渐近及其余项未作为本章前提。类别直方图对独立 Poisson 的似然比只依赖标记总数；本章进一步以有界似然的完整 $\chi^2$ 支付和熵变分，连接到有时间依赖的实际信号数组，未把独立参考结论直接当作实际路径结论。

Ioannis Kontoyiannis、Peter Harremoës、Oliver Johnson，*Entropy and the Law of Small Numbers*，[arXiv:math/0211020v2](https://arxiv.org/abs/math/0211020v2)，[固定版本原始 TeX](https://arxiv.org/src/math/0211020v2)。核对 Proposition 1 及完整证明：依赖指标先支付总相关，再作数据处理。这里的实际词序列代价在 (194.6) 独立推导，不假设为零，也不由单行边缘推出全数组 KL。此前条目所载该来源其他有限支撑或 Fisher information 表述边界保持不变，不作为本章前提。

本章复用第 175、180、183、187、191、193 章。经典离散 Gaussian 质量估计、熵变分、条件凸性、数据处理与二项有限积分不主张为新结果。新内容是这些关系在原共同实现中的信息支付，以及同一完整直方图上下界的匹配。没有从总相关上界、单个边缘、Gaussian 近似或纯 TV 比较推断未支付的 KL 系数；不主张全球原创性或 Lean 认证。

## 追加锚（本行以下为增补区）

## 谱边界卷第 195 章补充：任意固定负实场紧区间的原始总量无零邻域

对应 [谱边界卷第 195 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)。归属为 repo-derived：对原始负号完整选择计数总量，在任意固定负实场紧区间周围构造宽度不随层级缩小的复邻域，保留同一有限非中心谱、完整选择插入、物理噪声和精确低群混合，给出非零振幅及 $O(\delta)$ 相对误差。新的连接包括双侧 Stieltjes 鞍点约束、共同电荷条件下的全能量 Fourier 尾界、有限轮廓连接段、低群振幅非消失，以及原始计数的最终相对返回。一个连通域达到实际行列式 Taylor 级数不收敛的鞍点。振荡共存零点及其新标签仍未建立。

William D. Kirwin，*Higher Asymptotics of Laplace's Approximation*，[arXiv:0810.1700v2](https://arxiv.org/abs/0810.1700v2)，原 PDF 版本标记 2010-06-05，[固定版本 PDF](https://arxiv.org/pdf/0810.1700v2)。核对范围为引言中的内部、边界及复渐近区分，Theorem 1.1，Theorem 2.1 的条件和陈述，以及 Lemma 2.3 与中央区域／外部区域局部化的证明部分。实定理要求唯一内部极小值、非退化与规定的局部展开、离开极小值后的正间隙，以及某个正 Laplace 参数下的可积性。边界极值和复陡降需要额外论证。本文没有将这些假设由“存在解析临界点”代替，也未把该固定实积分定理直接用于变化的有限谱与物理噪声。

该 PDF 的文本提取存在 CFF Type1/fontTools 警告；部分高阶指数及字形未独立核清。本章不使用那些高阶系数，不声称已核对全部一般证明。来源仅承担所述假设、局部化结构和经典方法归属。所需复域、实际 Gaussian 循环系数、完整半线及能量尾部、低群非消失和统一相对误差均在正文单独推导，未归于来源的现成结论。

第 169、171、174、179、182、184、186 章按各自范围复用。Gaussian 条件化、Stieltjes 单调性、秩一与 Schur 补身份、Rouché 原理及解析 Laplace 方法属于经典工具。新综合不等于全球原创性；本文不作 Lean 认证，也不从负实场零点排除区推出全部左半平面或振荡区域的结论。

## 追加锚（本行以下为增补区）

## 196. 同一残差标记下的相位信息与物理剖面障碍

对应 `PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md` 第 196 章。Dytso–Poor–Shamai，*A General Derivative Identity for the Conditional Mean Estimator in Gaussian Noise and Some Applications*，arXiv:2104.01883v1（[原始版本](https://arxiv.org/abs/2104.01883v1)），主定理与附录 A 的条件均值求导以 $U-X-Y$ Markov 结构、独立满秩 Gaussian 噪声及相应可积性为条件。原始 TeX 的主定理和完整附录证明已核对；正文所需纯计数标记符合该结构，含同一噪声平方的联合标记不符合。故不将该来源的定理迁移为联合标记的导数、I-MMSE 或噪声单调性结论。

第 100 章的 Gaussian 方差剖面与有限系数、第 142、153 章的带标记选取律比较及第 192 章的完整计数线身份是模型内前置。Poisson 求和、Gaussian 固定矩和正交投影的经典身份在第 196 章按实际参数使用；新增关系是可测相位、两个宏观观测和中心联合惊奇量在同一选取律下的 Gram 估计，及其导出的条件均值平方增益。低群、外部对称系数、精确中心及同一个残差均保留。

物理结论只断言：原 $\beta>4/5$ 下，对 $c_1=7c_q/4,c_2=2c_q$，同一原始数组上，两个通道的积分修正偏差之最大值以概率趋于一有固定正下界，最大加权剖面误差也有固定下界；pair/path 分别对确定性支持一致。它不指定一个对所有支持统一失败的指数，不反驳每个指数，不否定紧邻 $\gamma=99c_q/200$ 的正区间。有限来源核对不构成全球原创性判断，普通推导不冒充 Lean 认证。

## 追加锚（本行以下为增补区）

## 197. 完整直方图信息首项与移动均值下的 Charlier 展开

对应 `PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md` 第 197 章。Adell–Lekuona–Yu，arXiv:1001.2897v1（[原始版本](https://arxiv.org/abs/1001.2897v1)），原文标识 `thm4` 的定理及完整积分／中心矩证明提供有限 binomial 相对熵界。固定概率或固定均值的印刷渐近不自动提供移动概率、指数增长均值或原依赖向量的结论。

Harremoës–Johnson–Kontoyiannis，*Thinning, Entropy and the Law of Thin Numbers*，arXiv:0906.0690v1（[原始版本](https://arxiv.org/abs/0906.0690v1)），Poisson–Charlier 定义、命题 `Charlierexpo`、`prop:radon`、定理 `thm:chisquare` 及完整相关证明已核对。其 chi-square 首项定理固定输入和参考均值；随后 KL 与一半 chi-square 的近似不作为本章统一余项的来源。截断正交展开未必非负的限制保留，附录确定均值例子的下降阶乘上标也未被导入。

第 197 章直接建立真实正似然的有限上界、全部 Charlier 次数的 Gaussian 复积分余项、近零似然区域的熵误差及单侧指数矩。模型内新增关系把这些界接回同一实际总量下的信号／背景直方图，支付移动大均值下的近比例形状、原路径时间依赖、全信息尾及精确均值参考变更，再由实际总量方差亏损取得匹配下界。完整原始直方图的 KL 首项为 $F_Q^2/16$，即 $Q^{-5}/[32\pi(b+a\vartheta^2)]$；pair/path 分别在紧参数区间与确定性支持上一致。

完整组识别、一／两行相对概率、实际总量分解和集中、条件化信息、加权尾与同阶方差亏损分别复用第 175、180、183、187、189、191、193、194 章。线质量归一化复用 `PARITY_HIDDEN_ARROW_POSTERIOR_FIELD.md` (44.9) 与 `PARITY_HIDDEN_ARROW_WINDOW_PHASES.md` (52.12)–(52.15)。不从本结果推出全数据熵、后验熵、同步 E2、下一阶系数或统计实验等价；不主张全球原创性或 Lean 认证。

## 追加锚（本行以下为增补区）

## 198. 重复直方图的似然极限与可达到的检验误差

对应 `PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md` 第 198 章。Lasse Leskelä，*Information divergences and likelihood ratios of Poisson processes and point patterns*，arXiv:2404.00294v2（[原始版本](https://arxiv.org/abs/2404.00294v2)），Hellinger 定义与三角不等式、原文标识 `the:PoissonHellinger` 及 `the:PoissonRenyiFinite` 的完整有限强度证明已核对，包括零密度和共同支配强度。正文采用未减半的平方 Hellinger 距离，转换该文的二分之一约定；Poisson 亲和度公式只用于两个 Poisson 参考律。

Harremoës–Johnson–Kontoyiannis，*Thinning, Entropy and the Law of Thin Numbers*，arXiv:0906.0690v1 的相关归属与适用范围见第 197 章。其固定输入／固定参考均值定理不直接承担当前的三角阵乘积极限。正文复用第 197 章独立建立的全部次数似然余项，直接证明近零似然控制、乘积二阶矩、指数倾斜、相邻性及真实似然的稳定性。

模型内新增关系在完整向量上先支付精确均值变更与信息尾，使其在 $mF_Q^2=O(1)$ 次完整独立实验后仍可传递。真实对数似然的两侧极限为 $N(\mp\tau/16,\tau/8)$，最优等先验错误率为 $\Phi(-\sqrt\tau/(4\sqrt2))$；使用已知精确总均值的二次总计数统计量达到这一极限。临界重复次数为 $Q^5$ 量级，零／无穷尺度的 TV 结论分别证明。原 path 的单次实验内部没有独立化，完整计数线、取整与全部尾均保留。

这是固定参数下规定两种采样分布的普通数学结论，不提供未知均值、未知支持估计、时间箭头区分、全数据恢复或 E2 的结算。有限文献核对不支持全球原创性判断，也不构成 Lean 认证。

## 追加锚（本行以下为增补区）

## 199. 实际相位格、Farey 分离边界与全后验校准概率

对应 `PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md` 第 199 章。Florin P. Boca 与 Alexandru Zaharescu，*The correlations of Farey fractions*，arXiv:math/0404114v4（[原始版本](https://arxiv.org/abs/math/0404114v4)），原始 TeX 的定义、主陈述、固定紧支撑光滑测试条件及第 4 节完整证明已核对。其相关定理对整个 Farey 集合作平均，不是数据自适应全后验校准的原子概率律；正文不把该平均换成实际校准分布。

原文 Mellin 计算的式 (4.16) 与相邻残数、结论存在 $3x^2/\pi^2$ 和 $3x^2/(2\pi^2)$ 的印刷系数差异，本章未使用该渐近。确定性有理数分离与实际校准的小球概率分别处理。Bézout 基与整数格方向构造由正文直接证明，明确保留极短最小向量的例外。

模型内复用第 142、153 章的带标记选取律比较、第 178 章完整锚点 $P_a(v)$ 的精确有限差分，以及第 196 章联合相位信息与宏观系数。新增关系控制固定 $c=2c_q$、原 $\beta>4/5$ 下低原始分母的临界相位事件，其方差、锚点和有限 $q$ 系数由同一隐藏类别同时改变；随后回接原积分亏损和加权剖面误差。较大分母的实际薄格事件 $E_{\rm mid}$ 概率仍未估计，因此没有新的完整固定指数物理反驳，也不否定临界低噪声边界附近的正区间。普通数学结论未作 Lean 认证，不主张全球原创性。

## 追加锚（本行以下为增补区）

## 200. 同样本均值估计与完整直方图的自适应检验功效

对应 `PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md` 第 200 章。Poisson 离散度检验、正交分数与 Neyman–Pearson 比较属于经典统计学。Harremoës–Johnson–Kontoyiannis，*Thinning, Entropy and the Law of Thin Numbers*，arXiv:0906.0690v1（[原始版本](https://arxiv.org/abs/0906.0690v1)）的 Poisson–Charlier 定义、归一化陈述及附录 `Charlierexpo` 证明已核对；该文归一化引理未附证明，固定输入 thinning 命题不直接承担本章任意大未知均值的三角阵校准。下降阶乘上标差异与截断级数未必为正密度的既有来源限制不变。

正文直接证明标量 Poisson 二次分数的固定阶矩一致有界、三角阵极限，以及无偏样本方差与同样本均值所构成统计量的精确恒等式。随后使用第 198 章同一实际实验的已付参考比较，得到未知均值下的功效 $\Phi(\Phi^{-1}(\alpha)+\sqrt{\tau/8})$，并通过有界截断似然证明所有完整直方图检验的渐近上界。适应未知总均值与任意坐标形状不损失此指定检验问题的一阶信息。

一次定向 Crossref 检索返回 Loukas–Kemp 的二维离散度检验、百科条目及 Frey 的未知均值 Poisson Kolmogorov–Smirnov 检验等元数据；这些原始证明未在本次核对，均未作为定理前提。有限检索不构成原创性或检索穷尽结论。

零假设在重复间共享同一未知向量，总强度至少一且有限；原替代是相同参数与确定性支持下独立重复整个实验。原 path 内部依赖、全计数线和零／微小均值坐标均保留。这里只证明正有限临界尺度下的渐近功效，不声称有限样本一致最强性、任意任务的充分性、支持恢复或 E2 结算，亦未作 Lean 认证。

## 追加锚（本行以下为增补区）

## 201. 原子校准访问概率与有理曲线计数的迁移边界

对应 `PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md` 第 201 章。Ayla Gafni，*Counting rational points near planar curves*，arXiv:1401.4958v1（[原始版本](https://arxiv.org/abs/1401.4958v1)）的原始 TeX 已核对，包括共同分母网格、非零曲率与 Hölder 二阶导数假设、定理 1–2、推论及相关证明。部分引用辅助估计的原始证明未在本次独立核对；本章不把该曲线定理直接用于全后验校准的原子分布。

该来源的共同分母、曲率和允许厚度均不能由本章的有限正系数比率自动得到。正文改用同一精确校准路径的上下步长：不同有理临界邻域迫使访问索引分离，再由实际二项核的单峰性得到 $C\mathsf B^2/q+C/\sqrt n+b_{\rm cal}$ 的概率界。固定 $c=2c_q$、原 $\beta>4/5$ 下，选择 $\mathsf B=\lfloor\sqrt q/Q^{10}\rfloor$ 支付第 199 章更大的临界子事件，原低分母截断保持不变。

第 178 章完整锚点有限差分与第 199 章共同粗条件场、带标记选取律返回是模型内前置。大于新截断的实际选定最短格向量事件仍未估计；没有新的物理反驳或完整固定指数分类。普通数学结论不构成 Lean 认证或全球原创性判断。

## 追加锚（本行以下为增补区）

## 202. 全部有限 Poisson 均值下的精确条件检验与临界功效

对应 `PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md` 第 202 章。Poisson 总量条件化、离散边界随机化、Pearson 离散度检验、Taylor 替换和 Neyman–Pearson 功效比较均属经典统计方法。本章直接证明维数显式的条件 multinomial 界，并用原完整实验的已付概率比较，把有限样本精确水平与渐近完整直方图功效界连接起来。

Frédéric Ouimet，*A precise local limit theorem for the multinomial distribution*，arXiv:2001.08512v1（[原始版本](https://arxiv.org/abs/2001.08512v1)）是对照来源。该版本的设定、主定理、bulk 外引理、概率推论和相关完整证明已核对。其固定概率向量、正剩余格与常数依赖不能直接承担本章增长格数、各格概率 $1/m$ 的误差界；第 3 节的应用说明也不提供所需一致性。正文以保持总和约束的 categorical/Gaussian 替换、六阶矩控制和光滑截断自行支付该桥梁，不将上述来源作为未验证的增长维数黑箱。

新增原模型结论：随机化检验对任意可数形状、全部有限总强度（含零）的固定 product-Poisson 重复零假设精确保持水平；非随机化严格上尾版本保守。两者在正有限临界尺度保持 $\Phi(\Phi^{-1}(\alpha)+\sqrt{\tau/8})$，并达到使用全部直方图的渐近功效界。真实 path 内部依赖、完整计数线及零／微小均值尾坐标均未删除。

不主张有限样本一致最强性、有效率的临界函数计算、任意统计任务的充分性或全球原创性。结论未作 Lean 认证。

## 追加锚（本行以下为增补区）

## 203. 精确临界值的全段坐标与有限剖面振幅

对应 `PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md` 第 203 章。Nico M. Temme，*Uniform Asymptotic Methods for Integrals*，arXiv:1308.1547v1（[原始版本](https://arxiv.org/abs/1308.1547v1)），§4.2 是一致变换的对照来源：临界值匹配、可去 Jacobian 与分支选择不能替代全局单射及原轮廓映射。该节的 Bessel/Airy 例子与其引用的外部全局映射证明不被迁移为本章有限随机数组的黑箱定理。

经典二次规范坐标本身不作原创声明。正文的新模型连接是精确有限条件能量的全段斜率商界、统一复拼接、单射逆映射和同一低模混合下的振幅控制。两端临界值保留各自实际能量根，非中心项、行列式及原始噪声均留在有限作用量内。共同场域到达 Taylor 收敛盘外的实际内部鞍点，但尚未进入端点／内部振幅相当的区域。

不由能量方向系数推断完整电荷周期系数，不由局部坐标推断总轮廓的两项相对误差或零点计数。结论未作 Lean 认证；来源核对为定向比较，未作全球原创性认定。

## 追加锚（本行以下为增补区）

## 204. 真实函数似然实验与运行统计量的越界法则

对应 `PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md` 第 204 章。Ward Whitt，*Proofs of the martingale FCLT*，arXiv:0712.1929v1（[原始版本](https://arxiv.org/abs/0712.1929v1)）的原始 TeX 主定理、二次变差与跳幅假设、最大不等式、模连续性和极限刻画证明提供方法对照。可预测括号分支必须保留跳幅条件；单独以括号连续紧性推出过程连续紧性不能承担本章证明，补偿 Poisson 过程即区分两者。来源内引用的一般极限保存与 Lévy 刻画外部证明未被作为本章黑箱输入。

正文直接证明所需的三角数组极限、最大余项和 Gaussian 倾斜，并以同一完整重复实验上的密度鞅支付真实似然转移。全聚合数的运行方差均值比与真实全直方图似然共享一条布朗极限路径；零假设漂移为 $-1/2$，原替代为 $+1/2$。反射公式给出常数边界的渐近误差与功效，Neyman–Pearson 比较进一步证明此监测规则相对于相同信息量的终点最优检验具有严格功效损失。

这些经典概率方法不作原创声明；新增结果是对原完整计数实验逐前缀、初始时间及未知均值误差的定量连接。顺序极限的零假设是原替代的精确均值 Poisson 参考；任意有限均值下的有限样本随时有效检验尚未在本章建立。第 202 章固定终点的精确条件结论不因此扩大。未作 Lean 认证或全球原创性认定。

## 追加锚（本行以下为增补区）
