# Negative scaled kurtosis in a thermal Markov current

## Abstract

An exact six-state two-bath generator contradicts the proposed nonnegativity of the fourth-to-second scaled heat-current cumulant ratio.

**Definition 1.1 (Total directed transition rate).**

$$\forall N \in \mathbb{N},\; (\forall L \in \mathbb{N},\; (\forall q \in \operatorname{Fin}\left(L\right) \to \left(\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)\right),\; (\forall i \in \operatorname{Fin}\left(N\right),\; (\forall j \in \operatorname{Fin}\left(N\right),\; (\operatorname{totalRate}\left(q, i, j\right) = \sum_{a:\operatorname{Fin}\left(L\right)} q\left(a, i, j\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.totalRate` (`✓ std3`).

*Citation.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady state currents*. DOI: [10.48550/arXiv.2204.08421](https://doi.org/10.48550/arXiv.2204.08421). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

Equation (65), page 6, writes kᵢⱼ = ∑α kᵢⱼᵅ. Here q α i j is the rate from i to j due to bath α, so totalRate q i j sums over the finite bath set Fin L.

**Definition 1.2 (Bath-resolved detailed balance).**

$$\forall N \in \mathbb{N},\; (\forall L \in \mathbb{N},\; (\forall E \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; (\forall b \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; (\forall q \in \operatorname{Fin}\left(L\right) \to \left(\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)\right),\; ((\operatorname{ThermalDetailedBalance}\left(E, b, q\right)) \Leftrightarrow (\forall a \in \operatorname{Fin}\left(L\right),\; (\forall i \in \operatorname{Fin}\left(N\right),\; (\forall j \in \operatorname{Fin}\left(N\right),\; ((\neg (i = j)) \Rightarrow (((0 < q\left(a, i, j\right)) \Leftrightarrow (0 < q\left(a, j, i\right))) \land ((0 < q\left(a, i, j\right)) \Rightarrow (\frac{q\left(a, i, j\right)}{q\left(a, j, i\right)} = \operatorname{Real}.\operatorname{exp}\left(b\left(a\right) \cdot (E\left(i\right) - E\left(j\right))\right)))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.ThermalDetailedBalance` (`✓ std3`).

*Citation.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady state currents*. DOI: [10.48550/arXiv.2204.08421](https://doi.org/10.48550/arXiv.2204.08421). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

Equation (66), page 6, states kᵢⱼᵅ/kⱼᵢᵅ = exp(−βᵅ(Eᵢ−Eⱼ)). In directed-rate notation the exponent is β α times (E i − E j). An edge is present exactly when its reverse edge is present, and the ratio equation applies on positive edges. Paired absent edges are allowed.

**Definition 1.3 (The heat-tilted generator).**

$$\forall N \in \mathbb{N},\; (\forall L \in \mathbb{N},\; (\forall E \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; (\forall q \in \operatorname{Fin}\left(L\right) \to \left(\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)\right),\; (\forall c \in \operatorname{Fin}\left(L\right),\; (\forall t \in \mathbb{R},\; (\forall i \in \operatorname{Fin}\left(N\right),\; (\forall j \in \operatorname{Fin}\left(N\right),\; (\operatorname{tiltedRateMatrix}\left(E, q, c, t\right)\left(i, j\right) = \operatorname{ite}\left((\neg (i = j)), \sum_{a:\operatorname{Fin}\left(L\right)} q\left(a, j, i\right) \cdot \operatorname{ite}\left((a = c), \operatorname{Real}.\operatorname{exp}\left(-(t) \cdot (E\left(i\right) - E\left(j\right))\right), 1\right), -(\sum_{k:\operatorname{Fin}\left(N\right)} \operatorname{ite}\left((k = i), 0, \operatorname{totalRate}\left(q, i, k\right)\right))\right)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.tiltedRateMatrix` (`✓ std3`).

*Citation.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady state currents*. DOI: [10.48550/arXiv.2204.08421](https://doi.org/10.48550/arXiv.2204.08421). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

Equations (67)–(68), page 6, multiply each off-diagonal contribution from the counted bath by exp(−lambda times (E i − E j)). The diagonal is minus the sum over states k distinct from i of totalRate q i k. The counting field is real and the counted bath belongs to Fin L.

**Definition 1.4 (A differentiable characteristic-root branch).**

$$\forall N \in \mathbb{N},\; (\forall L \in \mathbb{N},\; (\forall E \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; (\forall q \in \operatorname{Fin}\left(L\right) \to \left(\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)\right),\; (\forall c \in \operatorname{Fin}\left(L\right),\; (\forall f \in \mathbb{R} \to \mathbb{R},\; ((\operatorname{IsSourceSCGF}\left(E, q, c, f\right)) \Leftrightarrow ((f\left(0\right) = 0) \land ((\operatorname{ContDiffAt}\left(\mathbb{R}, 4, f, 0\right)) \land (\forall t \in \mathbb{R},\; ((\operatorname{Matrix}.\operatorname{det}\left((\operatorname{HSMul}.\operatorname{hSMul}\left(f\left(t\right), (1:\operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{R}\right))\right) - \operatorname{tiltedRateMatrix}\left(E, q, c, t\right))\right) = 0) \land (\forall v \in \mathbb{R},\; ((\operatorname{Matrix}.\operatorname{det}\left((\operatorname{HSMul}.\operatorname{hSMul}\left(v, (1:\operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{R}\right))\right) - \operatorname{tiltedRateMatrix}\left(E, q, c, t\right))\right) = 0) \Rightarrow (v \le f\left(t\right))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.IsSourceSCGF` (`✓ std3`).

*Citation.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady state currents*. DOI: [10.48550/arXiv.2204.08421](https://doi.org/10.48550/arXiv.2204.08421). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

Section III D, page 6: “The cumulant generating function χʰ(𝝀) is then equal to the dominant eigenvalue of Wʰ(𝝀) [63]; however, its analytic calculation is usually not possible for N > 4.” Here the branch χ vanishes at zero, is four times continuously differentiable there, and at every real counting field is a greatest real characteristic root of the heat-tilted matrix. Equations (68)–(70) give the characteristic-root equation and derivatives at zero; the root comparison is over real roots, and differentiability is required at zero.

**Definition 1.5 (The proposed nonnegative thermal kurtosis).**

$$(\operatorname{claim}) \Leftrightarrow (\forall N \in \mathbb{N},\; (\forall L \in \mathbb{N},\; (\forall E \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; (\forall b \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; (\forall q \in \operatorname{Fin}\left(L\right) \to \left(\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)\right),\; (\forall c \in \operatorname{Fin}\left(L\right),\; ((\forall a \in \operatorname{Fin}\left(L\right),\; (0 < b\left(a\right))) \Rightarrow ((\forall a \in \operatorname{Fin}\left(L\right),\; (\forall i \in \operatorname{Fin}\left(N\right),\; (\forall j \in \operatorname{Fin}\left(N\right),\; ((\neg (i = j)) \Rightarrow (0 \le q\left(a, i, j\right)))))) \Rightarrow ((\operatorname{ThermalDetailedBalance}\left(E, b, q\right)) \Rightarrow ((\exists f \in \mathbb{R} \to \mathbb{R},\; (\operatorname{IsSourceSCGF}\left(E, q, c, f\right))) \land (\forall f \in \mathbb{R} \to \mathbb{R},\; ((\operatorname{IsSourceSCGF}\left(E, q, c, f\right)) \Rightarrow ((0 < \operatorname{iteratedDeriv}\left(2, f, 0\right)) \Rightarrow (0 \le \frac{\operatorname{iteratedDeriv}\left(4, f, 0\right)}{\operatorname{iteratedDeriv}\left(2, f, 0\right)}))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.claim` (`✓ std3`).

*Citation.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady state currents*. DOI: [10.48550/arXiv.2204.08421](https://doi.org/10.48550/arXiv.2204.08421). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

Section III A, item 3, page 3, Eq. (19): “In classical Markovian systems driven only by temperature differences kurtosis of the heat current is always nonnegative”. The displayed inequality is 𝒦ʰ ≥ 0. The carriers are Fin N for states and Fin L for baths; β is strictly positive, the directed rates are nonnegative off the diagonal and satisfy bath-resolved detailed balance. The assertion includes existence of a branch and requires the ratio to be nonnegative for every such branch with positive second derivative. Equations (4) and (10), page 2, define this ratio using scaled cumulants: iteratedDeriv 4 χ 0 divided by iteratedDeriv 2 χ 0. It is not the standardized fourth central moment.

**Theorem 1.6 (A six-state refutation).**

$$\neg (\forall N \in \mathbb{N},\; (\forall L \in \mathbb{N},\; (\forall E \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; (\forall b \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; (\forall q \in \operatorname{Fin}\left(L\right) \to \left(\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)\right),\; (\forall c \in \operatorname{Fin}\left(L\right),\; ((\forall a \in \operatorname{Fin}\left(L\right),\; (0 < b\left(a\right))) \Rightarrow ((\forall a \in \operatorname{Fin}\left(L\right),\; (\forall i \in \operatorname{Fin}\left(N\right),\; (\forall j \in \operatorname{Fin}\left(N\right),\; ((\neg (i = j)) \Rightarrow (0 \le q\left(a, i, j\right)))))) \Rightarrow ((\operatorname{ThermalDetailedBalance}\left(E, b, q\right)) \Rightarrow ((\exists f \in \mathbb{R} \to \mathbb{R},\; (\operatorname{IsSourceSCGF}\left(E, q, c, f\right))) \land (\forall f \in \mathbb{R} \to \mathbb{R},\; ((\operatorname{IsSourceSCGF}\left(E, q, c, f\right)) \Rightarrow ((0 < \operatorname{iteratedDeriv}\left(2, f, 0\right)) \Rightarrow (0 \le \frac{\operatorname{iteratedDeriv}\left(4, f, 0\right)}{\operatorname{iteratedDeriv}\left(2, f, 0\right)}))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady state currents*. DOI: [10.48550/arXiv.2204.08421](https://doi.org/10.48550/arXiv.2204.08421). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

Take six alternating energy levels (0, 1, 0, 1, 0, 1), with inverse temperatures log 2 and log 8. The first bath joins each consecutive low–high pair with forward rates (1, 6, 6) and reverse rates (2, 12, 12). The second bath joins each high level to the next low level cyclically with downhill rate 8 and reverse rate 1. Counting the second bath gives det(z I − W(t)) = 63504 z + 50202 z² + 13968 z³ + 1507 z⁴ + 66 z⁵ + z⁶ − 18432(exp(3t) − 1) − 288(exp(−3t) − 1). Every branch supplied by the assertion has second derivative 3581/2401 and fourth derivative −113056891/1129900996 at zero. Their ratio is −113056891/1685204276, contradicting nonnegativity. The proof uses the asserted existence of a branch and its characteristic-root equation; it does not separately establish existence or identify a Perron eigenvalue.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.IsSourceSCGF`
- Truth anchor: `D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.ThermalDetailedBalance`
- Truth anchor: `D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.result`
- Truth anchor: `D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.tiltedRateMatrix`
- Truth anchor: `D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.totalRate`
- Dependency: [D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation](MarkovMpembaTripletRefutation.md)
