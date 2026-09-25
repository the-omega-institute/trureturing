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
