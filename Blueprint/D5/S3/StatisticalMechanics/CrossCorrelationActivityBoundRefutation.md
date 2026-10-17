# An equilibrium complete graph defeats the activity bound

## Abstract

A sixteen-state network contradicts the proposed general-network activity bound on cross-correlation asymmetry.

Fin(N) consists of the states 0 through N − 1. The array w(m,n) gives the transition rate from n to m when m and n differ, and p is a real-valued column vector. Every sum includes all states in Fin(N). All quotients are real quotients, and natural numbers in real expressions are coerced to the reals. The functions flux, activity, entropyRate, scaleRatio, asym and diffusion denote the quantities T, A, σ, γ, α and D of Eqs. (2)–(7), respectively.

**Definition 1.1 (One-way flux).**

$$\forall N \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right),\; \forall p \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall m \in \operatorname{Fin}\left(N\right),\; \forall n \in \operatorname{Fin}\left(N\right),\; \operatorname{flux}\left(w, p, m, n\right) = \operatorname{if} (m = n) \operatorname{then} 0 \operatorname{else} w\left(m, n\right) \cdot p\left(n\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.flux` (`✓ std3`).

*Citation.* Jie Gu (2024). *Thermodynamic bounds on the asymmetry of cross-correlations with dynamical activity and entropy production*. DOI: [10.1103/PhysRevE.109.L042101](https://doi.org/10.1103/PhysRevE.109.L042101). URL: <https://arxiv.org/abs/2312.00354v2>.

*Commentary.*

Off the diagonal, the one-way flux is T_mn = w(m,n) p(n), as in Eq. (2). Its diagonal is zero, so unrestricted double sums of fluxes equal sums over distinct states. The expression is defined for arbitrary real arrays w and p.

**Definition 1.2 (Total dynamical activity).**

$$\forall N \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right),\; \forall p \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \operatorname{activity}\left(w, p\right) = \sum_{m:\operatorname{Fin}\left(N\right)} (\sum_{n:\operatorname{Fin}\left(N\right)} (\operatorname{flux}\left(w, p, m, n\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.activity` (`✓ std3`).

*Citation.* Jie Gu (2024). *Thermodynamic bounds on the asymmetry of cross-correlations with dynamical activity and entropy production*. DOI: [10.1103/PhysRevE.109.L042101](https://doi.org/10.1103/PhysRevE.109.L042101). URL: <https://arxiv.org/abs/2312.00354v2>.

*Commentary.*

Equation (4) sums the one-way fluxes to obtain the total transition activity A. Both orientations of each transition are included.

**Definition 1.3 (Entropy production).**

$$\forall N \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right),\; \forall p \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \operatorname{entropyRate}\left(w, p\right) = \sum_{m:\operatorname{Fin}\left(N\right)} (\sum_{n:\operatorname{Fin}\left(N\right)} (\operatorname{if} (0 < \operatorname{flux}\left(w, p, m, n\right)) \operatorname{then} \operatorname{flux}\left(w, p, m, n\right) \cdot \operatorname{log}\left(\frac{\operatorname{flux}\left(w, p, m, n\right)}{\operatorname{flux}\left(w, p, n, m\right)}\right) \operatorname{else} 0))$$

*Formalization.* `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.entropyRate` (`✓ std3`).

*Citation.* Jie Gu (2024). *Thermodynamic bounds on the asymmetry of cross-correlations with dynamical activity and entropy production*. DOI: [10.1103/PhysRevE.109.L042101](https://doi.org/10.1103/PhysRevE.109.L042101). URL: <https://arxiv.org/abs/2312.00354v2>.

*Commentary.*

Equation (4) weights each positive one-way flux by the logarithm of its ratio to the reverse flux. Terms with nonpositive forward flux are zero. For a bidirectional network in a steady state, every positive forward flux has positive reverse flux. The logarithm is the real natural logarithm.

**Definition 1.4 (Scale separation of positive fluxes).**

$$\forall N \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right),\; \forall p \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \operatorname{scaleRatio}\left(w, p\right) = \frac{\operatorname{sSup}\left(\{x:\mathbb{R} \mid \exists m \in \operatorname{Fin}\left(N\right),\; \exists n \in \operatorname{Fin}\left(N\right),\; (x = \operatorname{flux}\left(w, p, m, n\right)) \land (0 < x)\}\right)}{\operatorname{sInf}\left(\{x:\mathbb{R} \mid \exists m \in \operatorname{Fin}\left(N\right),\; \exists n \in \operatorname{Fin}\left(N\right),\; (x = \operatorname{flux}\left(w, p, m, n\right)) \land (0 < x)\}\right)}$$

*Formalization.* `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.scaleRatio` (`✓ std3`).

*Citation.* Jie Gu (2024). *Thermodynamic bounds on the asymmetry of cross-correlations with dynamical activity and entropy production*. DOI: [10.1103/PhysRevE.109.L042101](https://doi.org/10.1103/PhysRevE.109.L042101). URL: <https://arxiv.org/abs/2312.00354v2>.

*Commentary.*

Equation (3) divides the largest positive one-way flux by the smallest. The displayed set consists exactly of the positive flux values. The real supremum and infimum give a total expression even when that set is empty; when it is nonempty, it is finite and its extrema are attained.

**Definition 1.5 (The antisymmetric correlation slope).**

$$\forall N \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right),\; \forall p \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall a \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall b \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \operatorname{asym}\left(w, p, a, b\right) = \frac{1}{2} \cdot \sum_{m:\operatorname{Fin}\left(N\right)} (\sum_{n:\operatorname{Fin}\left(N\right)} ((a\left(n\right) \cdot b\left(m\right) - a\left(m\right) \cdot b\left(n\right)) \cdot \operatorname{flux}\left(w, p, m, n\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.asym` (`✓ std3`).

*Citation.* Jie Gu (2024). *Thermodynamic bounds on the asymmetry of cross-correlations with dynamical activity and entropy production*. DOI: [10.1103/PhysRevE.109.L042101](https://doi.org/10.1103/PhysRevE.109.L042101). URL: <https://arxiv.org/abs/2312.00354v2>.

*Commentary.*

Equation (7) gives α_ab, half the difference of the two cross-correlation slopes at zero time lag. Its sign uses the transition convention n to m. The observables a and b are arbitrary real-valued functions on the state space.

**Definition 1.6 (The autocorrelation slope).**

$$\forall N \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right),\; \forall p \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall a \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \operatorname{diffusion}\left(w, p, a\right) = \frac{1}{2} \cdot \sum_{m:\operatorname{Fin}\left(N\right)} (\sum_{n:\operatorname{Fin}\left(N\right)} ((a\left(m\right) - a\left(n\right))^{2} \cdot \operatorname{flux}\left(w, p, m, n\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.diffusion` (`✓ std3`).

*Citation.* Jie Gu (2024). *Thermodynamic bounds on the asymmetry of cross-correlations with dynamical activity and entropy production*. DOI: [10.1103/PhysRevE.109.L042101](https://doi.org/10.1103/PhysRevE.109.L042101). URL: <https://arxiv.org/abs/2312.00354v2>.

*Commentary.*

The quantity D_a is half the flux-weighted sum of squared changes in a. Adding the corresponding expression for b and dividing by two gives Eq. (7). Equation (6) normalizes α_ab by the square root of D_a D_b.

**Definition 1.7 (A bidirectional network in a steady state).**

$$\forall N \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right),\; \forall p \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; (\operatorname{IsStationaryNetwork}\left(w, p\right)) \Leftrightarrow ((\forall m \in \operatorname{Fin}\left(N\right),\; \forall n \in \operatorname{Fin}\left(N\right),\; 0 \le w\left(m, n\right)) \land ((\forall m \in \operatorname{Fin}\left(N\right),\; \forall n \in \operatorname{Fin}\left(N\right),\; (w\left(m, n\right) \ne 0) \Leftrightarrow (w\left(n, m\right) \ne 0)) \land (((\forall m \in \operatorname{Fin}\left(N\right),\; 0 \le p\left(m\right)) \land (\sum_{m:\operatorname{Fin}\left(N\right)} (p\left(m\right)) = 1)) \land (\forall m \in \operatorname{Fin}\left(N\right),\; \sum_{n:\operatorname{Fin}\left(N\right)} (w\left(m, n\right) \cdot p\left(n\right)) = (\sum_{k:\operatorname{Fin}\left(N\right)} (w\left(k, m\right))) \cdot p\left(m\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.IsStationaryNetwork` (`✓ std3`).

*Citation.* Jie Gu (2024). *Thermodynamic bounds on the asymmetry of cross-correlations with dynamical activity and entropy production*. DOI: [10.1103/PhysRevE.109.L042101](https://doi.org/10.1103/PhysRevE.109.L042101). URL: <https://arxiv.org/abs/2312.00354v2>.

*Commentary.*

The transition array is nonnegative and a transition is present exactly when its reverse is present. The probability vector has nonnegative entries with total mass one; these are the two conditions of the finite probability predicate. The last equality balances incoming and outgoing probability at each state, as in Eq. (1). Diagonal terms of w cancel from that equality. Equivalently, the generator has off-diagonal entries w(m,n) and diagonal entry −Σ_(k ≠ m) w(k,m).

**Definition 1.8 (The proposed activity bound for every network).**

$$(claim) \Leftrightarrow (\forall N \in \mathbb{N},\; (3 \le N) \Rightarrow (\forall w \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right),\; \forall p \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall a \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall b \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; (\operatorname{IsStationaryNetwork}\left(w, p\right)) \Rightarrow ((\exists m \in \operatorname{Fin}\left(N\right),\; \exists n \in \operatorname{Fin}\left(N\right),\; 0 < \operatorname{flux}\left(w, p, m, n\right)) \Rightarrow ((0 < \operatorname{diffusion}\left(w, p, a\right) \cdot \operatorname{diffusion}\left(w, p, b\right)) \Rightarrow (\frac{\left|\operatorname{asym}\left(w, p, a, b\right)\right|}{\sqrt{\operatorname{diffusion}\left(w, p, a\right) \cdot \operatorname{diffusion}\left(w, p, b\right)}} \le \frac{\operatorname{scaleRatio}\left(w, p\right)}{\operatorname{tan}\left(\frac{\pi}{N}\right)} \cdot \sqrt{\frac{\operatorname{entropyRate}\left(w, p\right)}{2 \cdot \operatorname{activity}\left(w, p\right)}})))))$$

*Formalization.* `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.claim` (`✓ std3`).

*Citation.* Jie Gu (2024). *Thermodynamic bounds on the asymmetry of cross-correlations with dynamical activity and entropy production*. DOI: [10.1103/PhysRevE.109.L042101](https://doi.org/10.1103/PhysRevE.109.L042101). URL: <https://arxiv.org/abs/2312.00354v2>.

*Commentary.*

The conjecture after Eq. (9) extends Eq. (8) from a single cycle to arbitrary networks. It quantifies over every N at least three, every bidirectional network in a steady state with a positive one-way flux, and every pair of real observables with D_a D_b positive. The left side is the absolute normalized asymmetry |χ_ab| of Eq. (6).

**Theorem 1.9 (A sixteen-state counterexample).**

$$\neg (claim)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/gu-2023-cross-correlation-activity-bound-refutation` (refuted) by `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gu-2023-cross-correlation-activity-bound-refutation","declaration_gid":"D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jie Gu (2024). *Thermodynamic bounds on the asymmetry of cross-correlations with dynamical activity and entropy production*. DOI: [10.1103/PhysRevE.109.L042101](https://doi.org/10.1103/PhysRevE.109.L042101). URL: <https://arxiv.org/abs/2312.00354v2>.

*Commentary.*

Take the states 0 through 15. Along the oriented hexagon 0 → 1 → 2 → 3 → 4 → 5 → 0, give each forward transition rate 201/200 and each reverse transition rate 199/200. Join every pair of distinct states in {0,6,7,8,9,10,11,12,13,14,15} by a transition of rate one in each direction. All remaining entries of w are zero. At every state the total incoming and outgoing transition rate agree, so p(m) = 1/16 is a steady state.

On states 0 through 5, respectively, take a = (1,1/2,−1/2,−1,−1/2,1/2) and b = (0,√3/2,√3/2,0,−√3/2,−√3/2), the coordinates of a regular hexagon. On each state k from 6 through 15, take a(k) = (1005 − k)/1000 and b(k) = 0. Thus these last ten a-values are 999/1000 through 990/1000.

The positive fluxes have minimum 199/3200 and maximum 201/3200. The finite sums give γ = 201/199, A = 61/8, σ = (3/800) log(201/199), α_ab = 3√3/3200, D_a = 300121/1600000 and D_b = 3/16. Consequently χ_ab² = 45/600242 and both required diffusion factors are positive.

Since tan(π/16) > π/16 > 3/16, its reciprocal cot(π/16) is less than 16/3. Also log(201/199) < 2/199. If B is the right side of Eq. (8) for this network, these inequalities give B² < (1072/199)² · (3/12200) · (2/199) = 62055936/865289770200 < 45/600242 = χ_ab². The last comparison is the integer inequality 37248579136512 < 38938039659000. Both sides of Eq. (8) are nonnegative, so this contradicts its proposed upper bound.

The complete graph contributes equal flux in both directions and hence no entropy production or antisymmetric correlation slope. It raises the activity from 3/4 to 61/8, while its nearly equal a-values add only 121/1600000 to D_a and leave D_b unchanged. The factor involving total activity therefore makes the proposed bound too small. This counterexample concerns the extension to arbitrary networks; the complete graph introduces cycles beyond the hexagon.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.IsStationaryNetwork`
- Truth anchor: `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.activity`
- Truth anchor: `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.asym`
- Truth anchor: `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.diffusion`
- Truth anchor: `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.entropyRate`
- Truth anchor: `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.flux`
- Truth anchor: `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.result`
- Truth anchor: `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.scaleRatio`
- Dependency: [D5/S3/TotalVariation/CycleSingleCutMinimax](../TotalVariation/CycleSingleCutMinimax.md)
