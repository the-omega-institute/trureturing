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
