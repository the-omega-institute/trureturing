# Monotonicity of finite-spectrum quantum transport cost cones

## Abstract

Monotonicity of finite-spectrum quantum transport cost cones

The positive mixture of q-power distances representing a p-power distance is classical metric-embedding background: the real-line snowflake admits an Lq representation, interpreted by its q-power integral also for q below one. It is used here as analytic background for the finite-exponent cost-cone inclusion. The distance mixture is over a positive dilation and a full phase period; all displayed integrals are real Bochner integrals. This is not a claim that the sine identity is a new result of Bunth, Pitrik, Titkos and Virosztek.

**Definition 1.1 (sineKernel).**

$$\forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; \forall u \in \mathbb{R},\; \operatorname{sineKernel}\left(p, q, u\right) = \operatorname{abs}\left(\operatorname{sin}\left(u\right)\right)^{q} \cdot u^{0 - 1 - p}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.sineKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

The kernel is the absolute sine to power q times u to power minus one minus p.

**Definition 1.2 (sineMoment).**

$$\forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; \operatorname{sineMoment}\left(p, q\right) = \operatorname{IntegralOn}\left(\operatorname{Ioi}\left(0\right), u \mapsto \operatorname{abs}\left(\operatorname{sin}\left(u\right)\right)^{q} \cdot u^{0 - 1 - p}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.sineMoment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

The sine moment integrates the kernel on the positive half-line.

**Definition 1.3 (phaseMoment).**

$$\forall q \in \mathbb{R},\; \operatorname{phaseMoment}\left(q\right) = \operatorname{IntervalIntegral}\left(0, 2 \cdot pi, theta \mapsto \operatorname{abs}\left(\operatorname{cos}\left(theta\right)\right)^{q}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.phaseMoment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

The phase moment integrates the absolute cosine power over one full period.

**Definition 1.4 (sineParameterMeasure).**

$$\operatorname{sineParameterMeasure}\left(\right) = \operatorname{ProductMeasure}\left(\operatorname{Restrict}\left(volume, \operatorname{Ioi}\left(0\right)\right), \operatorname{Restrict}\left(volume, \operatorname{Ioc}\left(0, 2 \cdot pi\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.sineParameterMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

The dilation parameter lies in the positive half-line and the phase parameter lies in the half-open full period.

**Definition 1.5 (sineDistanceIntegrand).**

$$\forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \forall a \in \operatorname{Prod}\left(\mathbb{R}, \mathbb{R}\right),\; \operatorname{sineDistanceIntegrand}\left(p, q, x, y, a\right) = \operatorname{abs}\left(\operatorname{sin}\left(\operatorname{fst}\left(a\right) \cdot x + \operatorname{snd}\left(a\right)\right) - \operatorname{sin}\left(\operatorname{fst}\left(a\right) \cdot y + \operatorname{snd}\left(a\right)\right)\right)^{q} \cdot \operatorname{fst}\left(a\right)^{0 - 1 - p}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.sineDistanceIntegrand` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

The coordinate distance of the sine embedding is multiplied by the dilation density.

**Theorem 1.6 (sineMoment_pos).**

$$\forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; 0 < p \Rightarrow \left(p < q \Rightarrow 0 < \operatorname{sineMoment}\left(p, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.sineMoment_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

For 0 < p < q, the sine moment is integrable and strictly positive. Near zero the kernel is bounded by u to power q minus p minus one; at infinity it is bounded by u to power minus p minus one. The interval from zero to pi lies in its nonzero support.

**Theorem 1.7 (phaseMoment_pos).**

$$\forall q \in \mathbb{R},\; 0 < q \Rightarrow 0 < \operatorname{phaseMoment}\left(q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.phaseMoment_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

For q > 0, the phase integrand is continuous, nonnegative and positive at zero, so its full-period integral is positive.

**Theorem 1.8 (integrable_sineDistance).**

$$\forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; 0 < p \Rightarrow \left(p < q \Rightarrow \left(\forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \operatorname{Integrable}\left(a \mapsto \operatorname{sineDistanceIntegrand}\left(p, q, x, y, a\right), \operatorname{sineParameterMeasure}\left(\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.integrable_sineDistance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

The product-measure mixture is integrable. The full phase integral factors into the phase moment and a dilated sine kernel; Fubini's integrability criterion then applies.

**Theorem 1.9 (integral_sineDistance).**

$$\forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; 0 < p \Rightarrow \left(p < q \Rightarrow \left(\forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \operatorname{Integral}\left(a \mapsto \operatorname{sineDistanceIntegrand}\left(p, q, x, y, a\right), \operatorname{sineParameterMeasure}\left(\right)\right) = \frac{2^{q} \cdot \operatorname{phaseMoment}\left(q\right) \cdot \operatorname{sineMoment}\left(p, q\right)}{2^{p}} \cdot \operatorname{abs}\left(x - y\right)^{p}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.integral_sineDistance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

The sine subtraction identity separates the difference and midpoint. Full-period translation invariance removes the midpoint, and a positive dilation gives the absolute difference to power p. The coefficient equals 2 to power q minus p times the two positive moments.

All powers are real powers of nonnegative real numbers. The configuration index is an arbitrary finite type, including an empty type. The sampling measure can have infinite mass. The finite-dimensional moment theorem applies after changing the measure by the norm density; no closedness of a distance cone or compactness of its normalized section is needed.

**Definition 1.10 (Pair-distance vectors).**

$$\forall I : \operatorname{Type}\left(\right), \forall q : \mathbb{R}, \forall z : (I \to \mathbb{R}), \forall i : I, \forall j : I, \operatorname{distanceVector}\left(q, z, (i,j)\right) = \left|z\left(i\right) - z\left(j\right)\right|^{q}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.distanceVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

The vector has one real coordinate for every ordered pair. Diagonal coordinates and both orientations are retained.

**Theorem 1.11 (Conic cubature on an arbitrary measure).**

$$\forall E : \operatorname{Type}\left(\right), \forall alpha : \operatorname{Type}\left(\right), [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, E\right)] [\operatorname{MeasurableSpace}\left(alpha\right)] \forall mu : \operatorname{Measure}\left(alpha\right), \forall f : (alpha \to E), \forall s : \operatorname{Set}\left(alpha\right), \operatorname{StronglyMeasurable}\left(f\right) \Rightarrow \left(\operatorname{Integrable}\left(f, mu\right) \Rightarrow \left(\operatorname{AE}\left(mu, a \mapsto \operatorname{Mem}\left(a, s\right)\right) \Rightarrow \exists k : \operatorname{Nat}\left(\right), \exists w : (\operatorname{Fin}\left(k\right) \to \mathbb{R}), \exists a : (\operatorname{Fin}\left(k\right) \to alpha), (\forall i : \operatorname{Fin}\left(k\right), 0 \le w\left(i\right)) \land \left((\forall i : \operatorname{Fin}\left(k\right), \operatorname{Mem}\left(a\left(i\right), s\right)) \land \operatorname{Sum}\left(i \mapsto \operatorname{SMul}\left(w\left(i\right), f\left(a\left(i\right)\right)\right)\right) = \operatorname{Integral}\left(f, mu\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.finite_conic_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christian Bayer and Josef Teichmann (2006). *The proof of Tchakaloff's theorem*. DOI: [10.1090/S0002-9939-06-08249-9](https://doi.org/10.1090/S0002-9939-06-08249-9). URL: <https://arxiv.org/abs/math/0502473v2>.

*Commentary.*

For an integrable strongly measurable map f into a finite-dimensional real normed space, use density norm(f) and normalize each nonzero f-value by its norm. The resulting measure is finite. Apply finite_moments on any prescribed conull set, then absorb the normalizing factors into the nonnegative coefficients. The empty witness covers zero moments and zero measure. The inherited finite-measure cubature theorem is attributed to Bayer and Teichmann; the norm-density extension is the composition proved here.

**Theorem 1.12 (Exact replacement of a distance integral).**

$$\forall I : \operatorname{Type}\left(\right), \forall alpha : \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(I\right)] [\operatorname{MeasurableSpace}\left(alpha\right)] \forall mu : \operatorname{Measure}\left(alpha\right), \forall p : \mathbb{R}, \forall q : \mathbb{R}, \forall lambda : (I \to \mathbb{R}), \forall z : (alpha \to (I \to \mathbb{R})), \forall r : (alpha \to \mathbb{R}), 0 < q \Rightarrow \left(\operatorname{AE}\left(mu, a \mapsto 0 \le r\left(a\right)\right) \Rightarrow \left(\operatorname{StronglyMeasurable}\left(a \mapsto \operatorname{SMul}\left(r\left(a\right), \operatorname{distanceVector}\left(q, z\left(a\right)\right)\right)\right) \Rightarrow \left(\operatorname{Integrable}\left(a \mapsto \operatorname{SMul}\left(r\left(a\right), \operatorname{distanceVector}\left(q, z\left(a\right)\right)\right), mu\right) \Rightarrow \left(\operatorname{Integral}\left(a \mapsto \operatorname{SMul}\left(r\left(a\right), \operatorname{distanceVector}\left(q, z\left(a\right)\right)\right), mu\right) = \operatorname{distanceVector}\left(p, lambda\right) \Rightarrow \exists k : \operatorname{Nat}\left(\right), \exists v : (\operatorname{Fin}\left(k\right) \to (I \to \mathbb{R})), \forall i : I, \forall j : I, \left|lambda\left(i\right) - lambda\left(j\right)\right|^{p} = \operatorname{Sum}\left(l \mapsto \left|v\left(l, i\right) - v\left(l, j\right)\right|^{q}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.finite_distance_decomposition_of_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christian Bayer and Josef Teichmann (2006). *The proof of Tchakaloff's theorem*. DOI: [10.1090/S0002-9939-06-08249-9](https://doi.org/10.1090/S0002-9939-06-08249-9). URL: <https://arxiv.org/abs/math/0502473v2>.

*Commentary.*

The vector integrand is r(a) times the q-distance vector of z(a). The real weight r is nonnegative almost everywhere, and its vector integral equals the target p-distance vector. Conic cubature selects points in that conull positivity set. Multiply each configuration by the q-th root of its total nonnegative coefficient. Homogeneity absorbs every coefficient, giving an unweighted finite sum of q-distance vectors.

**Theorem 1.13 (Finite exact snowflake decomposition).**

$$\forall I : \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(I\right)]\forall p : \mathbb{R}, \forall q : \mathbb{R}, \forall lambda : (I \to \mathbb{R}), 0 < p \Rightarrow \left(p < q \Rightarrow \exists k : \operatorname{Nat}\left(\right), \exists v : (\operatorname{Fin}\left(k\right) \to (I \to \mathbb{R})), \forall i : I, \forall j : I, \left|lambda\left(i\right) - lambda\left(j\right)\right|^{p} = \operatorname{Sum}\left(l \mapsto \left|v\left(l, i\right) - v\left(l, j\right)\right|^{q}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.finite_distance_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

For 0 < p < q, the phase-averaged sine representation supplies the integrable vector moment. Its positive normalization is incorporated into the scalar weight. The preceding exact-replacement theorem yields finitely many real configurations. No bound on their number is asserted, and no rationality or effective computation claim is made. This scalar decomposition is consumed by the finite-spectrum operator lift.

The underlying space is any complete complex Hilbert space. No finite dimension or separability assumption is used. A finite-spectrum selfadjoint observable has bounded spectral support, so its spectral integral defines an everywhere defined bounded operator. Thus continuous linear endomorphisms retain the finite-spectrum observables in the source definition, even though its initial class also permits unbounded selfadjoint operators.

The cost is a finite sum of spectral projection tensors in the algebraic tensor product of the two operator algebras. The second factor is written before transposition. Applying the linear bijection from an operator to its transpose on the dual Hilbert space transports this expression to the source convention. The representation of the algebraic tensor product by operators on the Hilbert tensor product is injective: for linearly independent first factors, their matrix coefficient functionals separate their finite-dimensional span, and applying these functionals to a zero represented tensor forces every second factor to vanish. This explains the encoding; the Lean conclusion itself concerns the displayed algebraic tensor costs.

Finite lists encode finite indexed families, including repeated observables. A scalar shift of an observable preserves all spectral gaps and its cost. On a nonzero Hilbert space, finitely many distinct scalar shifts can therefore distinguish all repeated members without changing the sum; on the zero space every cost vanishes. This identifies the collection with the finite-set convention of equation (21). These comparisons explain the spectral-tensor encoding; they are not additional Lean bridge theorems. No approximate closure is added to the cost cone.

**Definition 1.14 (Finite-spectrum selfadjoint observables).**

Lean statement: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.IsFiniteObservable`

*Formalization.* `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.IsFiniteObservable` (`✓ std3`).

*Citation.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

Selfadjoint continuous complex linear endomorphisms whose real spectrum is finite, as in equations (21) and (27).

**Definition 1.15 (A finite spectral projection).**

Lean statement: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.specProj`

*Formalization.* `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.specProj` (`✓ std3`).

*Citation.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

The real continuous functional calculus applied to the indicator of one spectral value. That indicator is continuous on a finite spectrum.

**Definition 1.16 (The order-p spectral cost).**

Lean statement: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.costElem`

*Formalization.* `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.costElem` (`✓ std3`).

*Citation.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

Sum over every pair of spectral values of the p-th real power of their absolute difference times the corresponding tensor of spectral projections, the finite-spectrum form of equation (22). The infinite-spectrum branch of this total function is unused in the cone.

**Definition 1.17 (Finite sums of observable costs).**

Lean statement: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.costCone`

*Formalization.* `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.costCone` (`✓ std3`).

*Citation.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

The collection of finite sums of costs of finite-spectrum selfadjoint observables, corresponding to equation (27).

**Theorem 1.18 (Functional calculus preserves the observable class).**

Lean statement: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.finiteObservable_cfc`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.finiteObservable_cfc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

Every real function on a finite spectrum gives another selfadjoint finite-spectrum observable.

**Theorem 1.19 (Spectral projections after a change of labels).**

Lean statement: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.specProj_cfc`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.specProj_cfc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

The projection at v after functional calculus is the sum of the old projections whose labels map to v. The proof applies composition and finite summation in the continuous functional calculus.

**Theorem 1.20 (Transport of the double spectral cost).**

Lean statement: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.costElem_cfc`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.costElem_cfc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

Regrouping the two projection sums expresses the cost of f(A) using the original spectral projections and the distances between their new real labels.

**Theorem 1.21 (Exact scalar decompositions lift to operator costs).**

Lean statement: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.costElem_of_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.costElem_of_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

An exact finite decomposition of every pair distance on the spectrum gives an exact finite sum of observable costs through functional calculus.

**Theorem 1.22 (The finite-order cost-cone inclusion).**

Lean statement: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.result` (`✓ std3`). ∎

*Resolves.* `Problems/bunth-pitrik-titkos-virosztek-2025-cost-cone-monotonicity` (proved) by `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bunth-pitrik-titkos-virosztek-2025-cost-cone-monotonicity","declaration_gid":"D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth, J. Pitrik, T. Titkos, D. Virosztek (2025). *Wasserstein distances and divergences of order p by quantum channels*. DOI: [10.48550/arXiv.2501.08066](https://doi.org/10.48550/arXiv.2501.08066). URL: <https://arxiv.org/abs/2501.08066v3>.

*Commentary.*

For real parameters 0<p and p at most q, every order-p cost belongs to the order-q cone. The equal-exponent case is immediate. For strict exponents, the positive sine integral represents each scalar distance power. Exact finite-dimensional conic cubature gives finitely many new scalar configurations; functional calculus lifts those configurations to new observables, and their costs sum exactly to the original cost. Replacing each member of a finite family proves the inclusion.

This is the finite-parameter part of Conjecture 9, on Hilbert spaces without a separability restriction. The paper's Proposition 15 supplies the infinite endpoint. Its equations (49) and (50), and the stated concavity consequences for orders at most two, are consequences discussed by the source and are not separately formalized here. Proposition 13 gives reverse non-inclusion when the Hilbert space has dimension at least three, 0<p<pprime<infinity and pprime>1. For p=pprime=infinity the inclusion is reflexive.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.IsFiniteObservable`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.costCone`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.costElem`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.costElem_cfc`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.costElem_of_decomposition`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.distanceVector`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.finiteObservable_cfc`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.finite_conic_moments`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.finite_distance_decomposition`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.finite_distance_decomposition_of_integral`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.integrable_sineDistance`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.integral_sineDistance`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.phaseMoment`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.phaseMoment_pos`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.sineDistanceIntegrand`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.sineKernel`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.sineMoment`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.sineMoment_pos`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.sineParameterMeasure`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.specProj`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.specProj_cfc`
- Dependency: [D5/S3/Analytic/Convexity/MeasurableFiniteMoments](../../../Analytic/Convexity/MeasurableFiniteMoments.md)
