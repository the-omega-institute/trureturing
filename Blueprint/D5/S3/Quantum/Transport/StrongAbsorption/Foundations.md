# Foundations

## Abstract

Foundations for the strong-absorption cumulant expansion.

Natural-number subtraction is truncated. Unmarked integrals use volume; real-number powers and division use the real field.

**Theorem 1.1 (exp_sum_prod).**

$$\forall (M : \mathbb{N}) , \forall (a : \mathbb{R}) , \forall (p : (Fin M \to \mathbb{R}) \times (Fin M \to \mathbb{R})) , \operatorname{Real}.\operatorname{exp} (-a \cdot ((\sum i , p.1 i) + \sum j , p.2 j)) = (\prod i , \operatorname{Real}.\operatorname{exp} (-(a \cdot p.1 i))) \cdot \prod j , \operatorname{Real}.\operatorname{exp} (-(a \cdot p.2 j))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.exp_sum_prod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential of the sum of both coordinate families factors as the product of their exponentials.

**Definition 1.2 (weight).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , \forall (p : (Fin M \to \mathbb{R}) \times (Fin M \to \mathbb{R})) , weight M \gamma p = (if (\forall i , 0 \le p . 1 i) \land (\forall j , 0 \le p . 2 j \land p . 2 j \le \gamma) then \operatorname{Real}.\operatorname{exp} (- (M : \mathbb{R}) \cdot (\sum i , p . 1 i + \sum j , p . 2 j)) \cdot (\prod i , \prod j , if i < j then  (p . 1 i - p . 1 j)^{2} \cdot  (p . 2 i - p . 2 j)^{2} else 1) \cdot \prod i , \prod j , (\gamma + p . 1 i - p . 2 j) else 0)$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.weight` (`✓ std3`).

*Citation.* M. Novaes (2023). *Time delay statistics for chaotic cavities with absorption*. DOI: [10.1007/s10955-023-03183-7](https://doi.org/10.1007/s10955-023-03183-7). URL: <https://arxiv.org/abs/2305.18235v1>.

*Commentary.*

The unnormalized joint weight of inverse delay rates and auxiliary eigenvalues at β = 2, as diagonalized in Grabsch, Eqs. (3)–(4).

**Definition 1.3 (tauW).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , \forall (p : (Fin M \to \mathbb{R}) \times (Fin M \to \mathbb{R})) , tauW M \gamma p = ((M : \mathbb{R})^{-1} \cdot \sum i , 1 / (\gamma + p . 1 i))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.tauW` (`✓ std3`).

*Citation.* M. Novaes (2023). *Time delay statistics for chaotic cavities with absorption*. DOI: [10.1007/s10955-023-03183-7](https://doi.org/10.1007/s10955-023-03183-7). URL: <https://arxiv.org/abs/2305.18235v1>.

*Commentary.*

Novaes, Section 1: “τW = (1/M) Tr(Q) is called the Wigner time delay”. The inverse delay rates are γ + xᵢ, and times are in dwell-time units.

**Theorem 1.4 (integrable_power_exp).**

$$\forall (a : \mathbb{R}) , \forall (k : \mathbb{N}) , (0 < a) \to IntegrableOn (fun x : \mathbb{R} \mapsto  x^{k} \cdot \operatorname{Real}.\operatorname{exp} (- (a \cdot x))) (Ici 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.integrable_power_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.5 (power_exp_integral).**

$$\forall (a : \mathbb{R}) , \forall (k : \mathbb{N}) , (0 < a) \to (\int x : \mathbb{R} in Ici 0 ,  x^{k} \cdot \operatorname{Real}.\operatorname{exp} (- (a \cdot x))) = (\operatorname{k}.\operatorname{factorial} : \mathbb{R}) /  a^{k + 1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.power_exp_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Definition 1.6 (rawWeight).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , \forall (p : (Fin M \to \mathbb{R}) \times (Fin M \to \mathbb{R})) , rawWeight M \gamma p = (\operatorname{Real}.\operatorname{exp} (- (M : \mathbb{R}) \cdot ((\sum i , p . 1 i) + \sum j , p . 2 j)) \cdot (\prod i , \prod j , if i < j then  (p . 1 i - p . 1 j)^{2} \cdot  (p . 2 i - p . 2 j)^{2} else 1) \cdot \prod i , \prod j , (\gamma + p . 1 i - p . 2 j))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.rawWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Definition 1.7 (supportSet).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , supportSet M \gamma = ((\operatorname{Set}.\operatorname{univ}.\operatorname{pi} (\operatorname{Function}.\operatorname{const} (Fin M) (\operatorname{Set}.\operatorname{Ici} 0))) \times^{s} (\operatorname{Set}.\operatorname{univ}.\operatorname{pi} (\operatorname{Function}.\operatorname{const} (Fin M) (\operatorname{Set}.\operatorname{Icc} 0 \gamma))))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.supportSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Definition 1.8 (strictSupportSet).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , strictSupportSet M \gamma = ((\operatorname{Set}.\operatorname{univ}.\operatorname{pi} (\operatorname{Function}.\operatorname{const} (Fin M) (\operatorname{Set}.\operatorname{Ioi} 0))) \times^{s} (\operatorname{Set}.\operatorname{univ}.\operatorname{pi} (\operatorname{Function}.\operatorname{const} (Fin M) (\operatorname{Set}.\operatorname{Ioo} 0 \gamma))))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.strictSupportSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Definition 1.9 (center).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , center M \gamma = ((fun i \mapsto (\operatorname{val}\left(i\right) : \mathbb{R}) + 1 , fun i \mapsto \gamma \cdot ((\operatorname{val}\left(i\right) : \mathbb{R}) + 1) / ((M : \mathbb{R}) + 1)))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.center` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Definition 1.10 (orthantMeasure).**

$$\forall (M : \mathbb{N}) , orthantMeasure M = (\operatorname{Measure}.\operatorname{pi} (\operatorname{Function}.\operatorname{const} (Fin M) ((volume : Measure \mathbb{R}) . restrict (Ici 0))))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.orthantMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Definition 1.11 (powerSum).**

$$\forall (M : \mathbb{N}) , \forall (r : \mathbb{N}) , \forall (x : Fin M \to \mathbb{R}) , powerSum M r x = (\sum i ,  (x i)^{r})$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.powerSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Definition 1.12 (FirstOrder).**

$$\forall (f : \mathbb{R} \to \mathbb{R}) , \forall (a : \mathbb{R}) , \forall (b : \mathbb{R}) , FirstOrder f a b = ((fun \gamma \mapsto f \gamma - a - b \cdot \gamma^{-1}) =O [atTop] (fun \gamma \mapsto  \left(\gamma^{-1}\right)^{2}))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.FirstOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A first-order expansion at positive infinity with a remainder of order γ⁻².

**Definition 1.13 (gammaCGF).**

$$\forall (d : \mathbb{R}) , \forall (t : \mathbb{R}) , gammaCGF d t = (- d \cdot \operatorname{Real}.\operatorname{log} (1 - t / d))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.gammaCGF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Definition 1.14 (correctionCGF).**

$$\forall (d : \mathbb{R}) , \forall (t : \mathbb{R}) , correctionCGF d t = (t / (1 - t / d) - 2 \cdot t /  (1 - t / d)^{2})$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.correctionCGF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Definition 1.15 (inverseSlope).**

$$\forall (d : \mathbb{R}) , \forall (t : \mathbb{R}) , inverseSlope d t = ((1 - t / d)^{-1})$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.inverseSlope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Definition 1.16 (law).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , law M \gamma = (let \mu := \operatorname{volume}.\operatorname{withDensity} (fun p \mapsto \operatorname{ENNReal}.\operatorname{ofReal} (weight M \gamma p)) ; (\mu \operatorname{Set}.\operatorname{univ})^{-1} \cdot \mu)$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.law` (`✓ std3`).

*Citation.* M. Novaes (2023). *Time delay statistics for chaotic cavities with absorption*. DOI: [10.1007/s10955-023-03183-7](https://doi.org/10.1007/s10955-023-03183-7). URL: <https://arxiv.org/abs/2305.18235v1>.

*Commentary.*

The joint weight normalized by its total mass.

**Theorem 1.17 (supportSet_membership).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , \forall (p : (Fin M \to \mathbb{R}) \times (Fin M \to \mathbb{R})) , p \in supportSet M \gamma \Leftrightarrow (\forall i , 0 \le p . 1 i) \land (\forall j , 0 \le p . 2 j \land p . 2 j \le \gamma)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.supportSet_membership` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.18 (weight_nonneg).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , \forall (p : (Fin M \to \mathbb{R}) \times (Fin M \to \mathbb{R})) , 0 \le weight M \gamma p$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.weight_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.19 (strictSupportSet_membership).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , \forall (p : (Fin M \to \mathbb{R}) \times (Fin M \to \mathbb{R})) , p \in strictSupportSet M \gamma \Leftrightarrow (\forall i , 0 < p . 1 i) \land (\forall j , 0 < p . 2 j \land p . 2 j < \gamma)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.strictSupportSet_membership` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.20 (orthant_restrict).**

$$\forall (M : \mathbb{N}) , (volume : Measure ((Fin M \to \mathbb{R}) \times (Fin M \to \mathbb{R}))) . restrict ((\operatorname{Set}.\operatorname{Ici} (0 : (Fin M \to \mathbb{R}) \times (Fin M \to \mathbb{R})))) = (orthantMeasure M) . prod (orthantMeasure M)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.orthant_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.21 (polynomial_exp_integrable).**

$$\forall (M : \mathbb{N}) , \forall (a : \mathbb{R}) , \forall (P : MvPolynomial (Sum (Fin M) (Fin M)) \mathbb{R}) , (0 < a) \to Integrable (fun p : (Fin M \to \mathbb{R}) \times (Fin M \to \mathbb{R}) \mapsto \operatorname{Real}.\operatorname{exp} (- a \cdot ((\sum i , p . 1 i) + \sum j , p . 2 j)) \cdot \operatorname{MvPolynomial}.\operatorname{eval} (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) P) ((orthantMeasure M) . prod (orthantMeasure M))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.polynomial_exp_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Definition 1.22 (rescaledObservable).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , \forall (p : (Fin M \to \mathbb{R}) \times (Fin M \to \mathbb{R})) , rescaledObservable M \gamma p = (\gamma^{2} \cdot (\gamma^{-1} - tauW M \gamma p))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.rescaledObservable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Theorem 1.23 (FirstOrder.tendsto).**

$$\forall (f : \mathbb{R} \to \mathbb{R}) , \forall (a : \mathbb{R}) , \forall (b : \mathbb{R}) , (FirstOrder f a b) \to Tendsto f atTop (nhds a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.24 (FirstOrder.const).**

$$\forall (a : \mathbb{R}) , FirstOrder (\operatorname{Function}.\operatorname{const} \mathbb{R} a) a 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.25 (FirstOrder.add).**

$$\forall (f : \mathbb{R} \to \mathbb{R}) , \forall (g : \mathbb{R} \to \mathbb{R}) , \forall (a : \mathbb{R}) , \forall (b : \mathbb{R}) , \forall (c : \mathbb{R}) , \forall (d : \mathbb{R}) , (FirstOrder f a b) \to (FirstOrder g c d) \to FirstOrder (fun \gamma \mapsto f \gamma + g \gamma) (a + c) (b + d)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.26 (FirstOrder.const_mul).**

$$\forall (f : \mathbb{R} \to \mathbb{R}) , \forall (a : \mathbb{R}) , \forall (b : \mathbb{R}) , \forall (c : \mathbb{R}) , (FirstOrder f a b) \to FirstOrder (fun \gamma \mapsto c \cdot f \gamma) (c \cdot a) (c \cdot b)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.const_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.27 (FirstOrder.sum).**

$$\forall (\sigma : Type) , \forall (s : Finset \sigma) , \forall (f : \sigma \to \mathbb{R} \to \mathbb{R}) , \forall (a : \sigma \to \mathbb{R}) , \forall (b : \sigma \to \mathbb{R}) , (\forall i \in s , FirstOrder (f i) (a i) (b i)) \to FirstOrder (fun \gamma \mapsto \sum i \in s , f i \gamma) (\sum i \in s , a i) (\sum i \in s , b i)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.28 (FirstOrder.eventual_bound).**

$$\forall (f : \mathbb{R} \to \mathbb{R}) , \forall (a : \mathbb{R}) , \forall (b : \mathbb{R}) , (FirstOrder f a b) \to \exists C \gamma_{0} : \mathbb{R} , 0 < \gamma_{0} \land \forall \gamma : \mathbb{R} , \gamma_{0} \le \gamma \to | f \gamma - a - b / \gamma | \le C /  \gamma^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.eventual_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.29 (gammaCGF_deriv).**

$$\forall (d : \mathbb{R}) , (d \neq 0) \to deriv (gammaCGF d) = inverseSlope d$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.gammaCGF_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Definition 1.30 (kappa).**

$$\forall (M : \mathbb{N}) , \forall (n : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , kappa M n \gamma = (iteratedDeriv n (cgf (tauW M \gamma) (law M \gamma)) 0)$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.kappa` (`✓ std3`).

*Citation.* M. Novaes (2023). *Time delay statistics for chaotic cavities with absorption*. DOI: [10.1007/s10955-023-03183-7](https://doi.org/10.1007/s10955-023-03183-7). URL: <https://arxiv.org/abs/2305.18235v1>.

*Commentary.*

The n-th cumulant is the n-th derivative at zero of the cumulant generating function of tauW under law.

**Theorem 1.31 (center_properties).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , (0 < \gamma) \to center M \gamma \in strictSupportSet M \gamma \land \operatorname{Function}.\operatorname{Injective} ((center M \gamma) . 1) \land \operatorname{Function}.\operatorname{Injective} ((center M \gamma) . 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.center_properties` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.32 (rescaledObservable_eq_u).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , \forall (p : (Fin M \to \mathbb{R}) \times (Fin M \to \mathbb{R})) , (1 \le M) \to (0 < \gamma) \to (\forall i , 0 \le p . 1 i) \to rescaledObservable M \gamma p = (\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} (fun i \mapsto p . 1 i / (1 + \gamma^{-1} \cdot p . 1 i)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.rescaledObservable_eq_u` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.33 (FirstOrder.mul).**

$$\forall (f : \mathbb{R} \to \mathbb{R}) , \forall (g : \mathbb{R} \to \mathbb{R}) , \forall (a : \mathbb{R}) , \forall (b : \mathbb{R}) , \forall (c : \mathbb{R}) , \forall (d : \mathbb{R}) , (FirstOrder f a b) \to (FirstOrder g c d) \to FirstOrder (fun \gamma \mapsto f \gamma \cdot g \gamma) (a \cdot c) (a \cdot d + b \cdot c)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.34 (measurable_weight).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , Measurable (weight M \gamma)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.measurable_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.35 (observable_power_remainder).**

$$\forall (M : \mathbb{N}) , \forall (\varepsilon : \mathbb{R}) , \forall (x : Fin M \to \mathbb{R}) , \forall (k : \mathbb{N}) , (0 \le \varepsilon) \to (\forall i , 0 \le x i) \to |  (\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} (fun i \mapsto x i / (1 + \varepsilon \cdot x i)))^{k + 2} -  (\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} x)^{k + 2} + \varepsilon \cdot (k + 2 : \mathbb{R}) \cdot (\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} (fun i \mapsto  (x i)^{2})) \cdot  (\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} x)^{k + 1} | \le  \varepsilon^{2} \cdot (((k + 2 : \mathbb{R}) \cdot (k + 1) / 2) \cdot  ((\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} (fun i \mapsto  (x i)^{2})))^{2} \cdot  (\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} x)^{k} + (k + 2 : \mathbb{R}) \cdot ((M : \mathbb{R})^{-1} \cdot powerSum M 3 x) \cdot  (\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} x)^{k + 1})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.observable_power_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.36 (observable_power_one).**

$$\forall (M : \mathbb{N}) , \forall (\varepsilon : \mathbb{R}) , \forall (x : Fin M \to \mathbb{R}) , (0 \le \varepsilon) \to (\forall i , 0 \le x i) \to | (\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} (fun i \mapsto x i / (1 + \varepsilon \cdot x i))) - (\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} x) + \varepsilon \cdot (\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} (fun i \mapsto  (x i)^{2})) | \le  \varepsilon^{2} \cdot ((M : \mathbb{R})^{-1} \cdot powerSum M 3 x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.observable_power_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.37 (FirstOrder.sub).**

$$\forall (f : \mathbb{R} \to \mathbb{R}) , \forall (g : \mathbb{R} \to \mathbb{R}) , \forall (a : \mathbb{R}) , \forall (b : \mathbb{R}) , \forall (c : \mathbb{R}) , \forall (d : \mathbb{R}) , (FirstOrder f a b) \to (FirstOrder g c d) \to FirstOrder (fun \gamma \mapsto f \gamma - g \gamma) (a - c) (b - d)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.38 (gammaCGF_iterated).**

$$\forall (d : \mathbb{R}) , \forall (n : \mathbb{N}) , (d \neq 0) \to iteratedDeriv (n + 1) (gammaCGF d) 0 = (\operatorname{n}.\operatorname{factorial} : \mathbb{R}) /  d^{n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.gammaCGF_iterated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.39 (mass_pos).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , (0 < \gamma) \to 0 < (\operatorname{volume}.\operatorname{withDensity} (fun p \mapsto \operatorname{ENNReal}.\operatorname{ofReal} (weight M \gamma p))) \operatorname{Set}.\operatorname{univ}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.mass_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.40 (law_ae_support).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , \forall ^{m} p d law M \gamma , p \in supportSet M \gamma$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.law_ae_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.41 (law_integral).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , \forall (f : (Fin M \to \mathbb{R}) \times (Fin M \to \mathbb{R}) \to \mathbb{R}) , (1 \le M) \to (\int p , f p d law M \gamma) = (\int p , weight M \gamma p \cdot f p) / (\int p , weight M \gamma p)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.law_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.42 (correctionCGF_iterated).**

$$\forall (d : \mathbb{R}) , \forall (n : \mathbb{N}) , (d \neq 0) \to (1 \le n) \to iteratedDeriv n (correctionCGF d) 0 = - (2 \cdot n - 1) \cdot (\operatorname{n}.\operatorname{factorial} : \mathbb{R}) /  d^{n - 1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.correctionCGF_iterated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.43 (law_isProbability).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , (1 \le M) \to (0 < \gamma) \to IsProbabilityMeasure (law M \gamma)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.law_isProbability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.44 (rescaledObservable_integrable_exp).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , \forall (t : \mathbb{R}) , (1 \le M) \to (0 < \gamma) \to Integrable (fun p \mapsto \operatorname{Real}.\operatorname{exp} (t \cdot rescaledObservable M \gamma p)) (law M \gamma)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.rescaledObservable_integrable_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.45 (kappa_rescaled).**

$$\forall (M : \mathbb{N}) , \forall (n : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , (1 \le M) \to (2 \le n) \to (0 < \gamma) \to kappa M n \gamma =  (-  \left(\gamma^{-1}\right)^{2})^{n} \cdot iteratedDeriv n (cgf (rescaledObservable M \gamma) (law M \gamma)) 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.kappa_rescaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.46 (rescaled_moment_cumulant).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , \forall (n : \mathbb{N}) , (1 \le M) \to (0 < \gamma) \to iteratedDeriv (n + 1) (cgf (rescaledObservable M \gamma) (law M \gamma)) 0 = (\int p ,  (rescaledObservable M \gamma p)^{n + 1} d law M \gamma) - \sum i \in range n , (\operatorname{n}.\operatorname{choose} i : \mathbb{R}) \cdot iteratedDeriv (i + 1) (cgf (rescaledObservable M \gamma) (law M \gamma)) 0 \cdot (\int p ,  (rescaledObservable M \gamma p)^{n - i} d law M \gamma)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.rescaled_moment_cumulant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.47 (inverseSlope_deriv).**

$$\forall (d : (\mathbb{R})) , ((deriv (inverseSlope d) = fun t \mapsto (d)^{-1} \cdot ((inverseSlope d t))^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.inverseSlope_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

## References

- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.FirstOrder`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.add`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.center`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.center_properties`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.const`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.const_mul`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.correctionCGF`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.correctionCGF_iterated`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.eventual_bound`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.exp_sum_prod`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.gammaCGF`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.gammaCGF_deriv`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.gammaCGF_iterated`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.integrable_power_exp`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.inverseSlope`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.inverseSlope_deriv`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.kappa`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.kappa_rescaled`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.law`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.law_ae_support`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.law_integral`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.law_isProbability`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.mass_pos`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.measurable_weight`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.mul`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.observable_power_one`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.observable_power_remainder`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.orthantMeasure`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.orthant_restrict`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.polynomial_exp_integrable`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.powerSum`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.power_exp_integral`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.rawWeight`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.rescaledObservable`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.rescaledObservable_eq_u`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.rescaledObservable_integrable_exp`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.rescaled_moment_cumulant`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.strictSupportSet`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.strictSupportSet_membership`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.sub`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.sum`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.supportSet`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.supportSet_membership`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.tauW`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.tendsto`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.weight`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.weight_nonneg`
