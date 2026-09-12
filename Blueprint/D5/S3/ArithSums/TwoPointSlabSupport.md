# Support of a two-point coordinate box

## Abstract

An actual two-corner budget slab has positive support, strictly above the base at zero shape.

All logarithms are natural. The support theorem uses three coordinates with widths log(2), log(3), log(7). All budgets, heights and shape coordinates are arbitrary finite real numbers. The notation xi denotes the source shape; its minimum is zero exactly when some coordinate is zero, since every coordinate is nonnegative. The variance sum below is unaveraged.

**Definition 1.1 (Distance to an actual pair).**

$$\begin{aligned}\forall S \in \operatorname{Set}\left(\alpha\right), \forall c \in \alpha, \forall d \in \alpha, \operatorname{pairDistance}\left(S, c, d\right) = \operatorname{min}\left(\operatorname{infDist}\left(c, S\right), \operatorname{infDist}\left(d, S\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/ArithSums/TwoPointSlabSupport.pairDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here alpha is any pseudometric space and S is any subset. Each infDist is the usual point-to-set infimum distance. For a nonempty compact S the minimum has the attained-distance meaning proved below.

**Definition 1.2 (One actual endpoint in every coordinate).**

$$\begin{aligned}\forall c \in (\iota \to \alpha), \forall d \in (\iota \to \alpha), \forall x \in (\iota \to \alpha), (\operatorname{IsCorner}\left(c, d, x\right)) \iff (\forall i \in \iota, x_{i} \in \{c_{i}, d_{i}\})\end{aligned}$$

*Formalization.* `D5/S3/ArithSums/TwoPointSlabSupport.IsCorner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index type and coordinate type are arbitrary. Endpoint coincidence is allowed in this definition. Fractional coordinate mixtures are not corners.

**Definition 1.3 (Two different included budget values).**

$$\begin{aligned}\forall c \in (\iota \to \mathbb{R}), \forall d \in (\iota \to \mathbb{R}), \forall M_{0} \in \mathbb{R}, \forall M_{1} \in \mathbb{R}, (\operatorname{WideSlab}\left(c, d, M_{0}, M_{1}\right)) \iff ((M_{0} < M_{1}) \land (\exists x \in (\iota \to \mathbb{R}), \exists y \in (\iota \to \mathbb{R}), (\operatorname{IsCorner}\left(c, d, x\right)) \land (\operatorname{IsCorner}\left(c, d, y\right)) \land (\sum_{i} (x_{i}) \in [M_{0}, M_{1}]) \land (\sum_{i} (y_{i}) \in [M_{0}, M_{1}]) \land (\sum_{i} (x_{i}) \neq \sum_{i} (y_{i}))))\end{aligned}$$

*Formalization.* `D5/S3/ArithSums/TwoPointSlabSupport.WideSlab` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index type iota is finite. A budget is the sum of all coordinates. Both slab endpoints are included. Two corner labels with the same budget do not meet this hypothesis: the actual budget values must differ.

**Definition 1.4 (The exact ordered widths).**

$$\begin{aligned}h = (\log 2,\log 3,\log 7)\end{aligned}$$

*Formalization.* `D5/S3/ArithSums/TwoPointSlabSupport.logWidths` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vector h is indexed by Fin(3), in this displayed order. In particular, a=log(2)>0, and a is no larger than either other width.

**Theorem 1.5 (The minimum is the genuine set distance).**

$$\begin{aligned}\forall S \in \operatorname{Set}\left(\alpha\right), \forall c \in \alpha, \forall d \in \alpha, ((\operatorname{IsCompact}\left(S\right)) \land (S \neq \emptyset)) \implies ((0 \le \operatorname{pairDistance}\left(S, c, d\right)) \land (\exists y \in S, \exists z \in \{c, d\}, \operatorname{pairDistance}\left(S, c, d\right) = \operatorname{dist}\left(y, z\right)) \land (\forall y \in S, \forall z \in \{c, d\}, \operatorname{pairDistance}\left(S, c, d\right) \le \operatorname{dist}\left(y, z\right)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/TwoPointSlabSupport.pair_distance_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In any pseudometric space, compactness and nonemptiness give a closest point of S to each endpoint. Choose the endpoint with the smaller infimum. The result is attained by an actual pair and bounds the distance of every actual pair from below. These properties identify the set-to-set minimum; a merely supplied nonnegative lower bound would not have this meaning.

**Theorem 1.6 (The complete three-coordinate support theorem).**

$$\begin{aligned}\forall T \in \mathbb{R}, \forall M_{0} \in \mathbb{R}, \forall M_{1} \in \mathbb{R}, \forall \operatorname{xi} \in (\operatorname{Fin}\left(3\right) \to \mathbb{R}), \\\operatorname{let} a = \log 2, h = (\log 2,\log 3,\log 7); \\\operatorname{let} c_{i} = T + \operatorname{xi}_{i}, d_{i} = c_{i} + h_{i}, A = 3 \cdot T + \sum_{i} (\operatorname{xi}_{i}); \\\operatorname{let} I = [\frac{M_{0}}{3}, \frac{M_{1}}{3}], \mu = \frac{M_{1}}{3}, \delta_{i} = \operatorname{pairDistance}\left(I, c_{i}, d_{i}\right); \\\operatorname{let} V_{0} = \sum_{i} (\delta_{i}^{2}), \rho = \sqrt{\frac{V_{0}}{6}}, L = \mu - \rho, H = \mu + 2 \cdot \rho; \\\operatorname{let} o = ((e:(\operatorname{Fin}\left(3\right) \to \{0, 1\})) \mapsto \sum_{i} (e_{i} \cdot h_{i})); \\(a \le T) \land (\forall i \in \operatorname{Fin}\left(3\right), 0 \le \operatorname{xi}_{i}) \land (\exists i \in \operatorname{Fin}\left(3\right), \operatorname{xi}_{i} = 0) \land (\operatorname{WideSlab}\left(c, d, M_{0}, M_{1}\right)) \implies\\{}[(\forall x \in (\operatorname{Fin}\left(3\right) \to \mathbb{R}), (\operatorname{IsCorner}\left(c, d, x\right)) \iff (\exists e \in (\operatorname{Fin}\left(3\right) \to \{0, 1\}), x = (i \mapsto c_{i} + e_{i} \cdot h_{i})))\\\land (\forall e \in (\operatorname{Fin}\left(3\right) \to \{0, 1\}), \sum_{i} (c_{i} + e_{i} \cdot h_{i}) = A + o\left(e\right))\\\land (\forall i \in \operatorname{Fin}\left(3\right), (0 \le \delta_{i}) \land (\exists y \in I, \exists z \in \{c_{i}, d_{i}\}, \delta_{i} = \operatorname{dist}\left(y, z\right)) \land (\forall y \in I, \forall z \in \{c_{i}, d_{i}\}, \delta_{i} \le \operatorname{dist}\left(y, z\right)))\\\land (\forall x \in (\operatorname{Fin}\left(3\right) \to \mathbb{R}), ((\operatorname{IsCorner}\left(c, d, x\right)) \land (\sum_{i} (x_{i}) \in [M_{0}, M_{1}])) \implies (\operatorname{let} m = \frac{\sum_{i} (x_{i})}{3}; (m \in I) \land (\forall i \in \operatorname{Fin}\left(3\right), 0 \le x_{i} - T) \land (V_{0} \le \sum_{i} ((x_{i} - m)^{2}) = \sum_{i} ((x_{i} - T)^{2}) - 3 \cdot (m - T)^{2} \le 6 \cdot (m - T)^{2}) \land (0 \le \rho \le m - T \le \mu - T)))\\\land H \ge L \ge T > 0\\\land \operatorname{IsLeast}\left(\operatorname{range}\left(o\right), 0\right) \land \operatorname{IsLeast}\left(\{r \mid (r \in \operatorname{range}\left(o\right)) \land (0 < r)\}, a\right)\\\land ((\operatorname{xi} = 0) \implies (\operatorname{let} u = M_{0} - 3 \cdot T; \operatorname{let} v = M_{1} - 3 \cdot T; (a \le v) \land (u < v) \land ((u \le 0) \implies ((\forall i \in \operatorname{Fin}\left(3\right), \delta_{i} = 0) \land (\rho = 0) \land (L = T + \frac{v}{3}) \land (T < L))) \land ((0 < u) \implies ((\forall i \in \operatorname{Fin}\left(3\right), \delta_{i} \le \frac{u}{3}) \land (\rho \le \frac{u}{3 \cdot \sqrt{2}}) \land (L \ge T + \frac{v - \frac{u}{\sqrt{2}}}{3} > T))) \land (0 < L - T \le H - T)))]\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/TwoPointSlabSupport.wide_slab_support_237` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the displayed statement, all unqualified coordinate sums and coordinate quantifiers range over Fin(3). Bool choices are identified with bits zero and one. Thus e_i h_i means h_i for true and zero for false. The symbol o is the offset function, and its range consists of the actual corner offsets. IsLeast asserts membership as well as a lower bound: zero and a are both attained. The bracketed conclusions are a conjunction under the displayed hypotheses. Every included corner is quantified, not only the two witnessing the slab.

For an included corner, its mean lies in the scaled closed budget interval. The attained-distance comparison gives delta_i <= |x_i-m|. Squaring and summing proves the first variance inequality. With w_i=x_i-T>=0, the identity sum(w_i)=3(m-T) and the nonnegative cross terms in its square give sum(w_i^2)<=(sum(w_i))^2. Subtracting 3(m-T)^2 gives the factor six. The generic finite-index square-sum argument specializes to three coordinates.

Every nonzero bit offset includes at least one positive width, and each width is at least a. The all-false choice attains zero; choosing only the first coordinate attains a. In zero shape, two different included budget values therefore force v>=a. The strict slab order gives u<v.

If u<=0, the base T lies in the mean interval and every coordinate distance vanishes. If u>0, the left interval endpoint bounds every distance by u/3. Summing the three squared bounds yields rho<=u/(3 sqrt(2)). Since sqrt(2)>1 and v>u>0, the displayed intermediate lower bound is strictly greater than T. In either branch the offsets lambda=L-T and eta=H-T satisfy 0<lambda<=eta; lambda is an offset, not a dual price.

Negative lower budgets, arbitrary upper slack, corners at either closed endpoint, zero w coordinates and zero variance are included. No integer exponent, coordinate-width comparison c_i>=h_i, cutoff, small-shape or physical premise is imposed. The result supplies positive arguments for later arithmetic analytic estimates; it makes no quantum or RH assertion.

## References

- Truth anchor: `D5/S3/ArithSums/TwoPointSlabSupport.IsCorner`
- Truth anchor: `D5/S3/ArithSums/TwoPointSlabSupport.WideSlab`
- Truth anchor: `D5/S3/ArithSums/TwoPointSlabSupport.logWidths`
- Truth anchor: `D5/S3/ArithSums/TwoPointSlabSupport.pairDistance`
- Truth anchor: `D5/S3/ArithSums/TwoPointSlabSupport.pair_distance_spec`
- Truth anchor: `D5/S3/ArithSums/TwoPointSlabSupport.wide_slab_support_237`
