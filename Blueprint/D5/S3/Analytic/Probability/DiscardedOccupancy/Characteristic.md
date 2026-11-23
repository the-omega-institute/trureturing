# Occupancy word laws and characteristic functions

## Abstract

The explicit finite word measure is the product of the individual throw measures.

**Theorem 1.1 (The finite word measure is a product).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (j: \mathbb{N}), 0<n \implies 0 \leq p \implies p \leq 1 \implies \operatorname{toMeasure}\left(\operatorname{wordPMF}\left(n, p, j\right)\right) = \prod_{i: \operatorname{Fin}\left(j\right)} \operatorname{toMeasure}\left(\operatorname{throwPMF}\left(n, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.wordMeasure_eq_pi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A throw is discarded with probability one minus p and each ordinary bin has mass p divided by n. The mass of a word is the product of the coordinate masses. The transition calculation for the characteristic function uses this same law and conditions on the count of occupied bins after the prefix.

**Definition 1.2 (Centered Bernoulli).**

$$\forall (r: \mathbb{R}), \forall (s: \mathbb{R}), (\mathit{centeredBernoulli} r s : \mathbb{C}) = (1 - r) \cdot \mathit{phase} (s \cdot -r) + r \cdot \mathit{phase} (s \cdot (1 - r))$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.centeredBernoulli` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.3 (Char Fun standardized Law).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (p: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hpUpper}: p \leq 1), \forall (j: \mathbb{N}), \forall (t: \mathbb{R}), \mathit{MeasureTheory}.\mathit{charFun} (\mathit{val} (\mathit{standardizedLaw} \mathit{hn} \mathit{hp} \mathit{hpUpper} j)) t = \mathit{expect} n p j \mathit{fun} (x : \mathbb{N}) => \mathit{phase} (t \cdot \mathit{standardized} n p j x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.charFun_standardizedLaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.4 (Conditional comparison).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (p: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hpUpper}: p \leq 1), \forall (j: \mathbb{N}), \forall (\mathit{hj}: j \leq n), \forall (s: \mathbb{R}), \forall (\mathit{hs}: |s| \leq 1), \Vert \mathit{rowPhase} n p (j + 1) s - \mathit{rowPhase} n p j (a n p \cdot s) \cdot \mathit{gaussianFactor} s (\mathit{predictableVariance} n p j)\Vert \leq (\mathit{Real}.\mathit{exp} 1 + 1) \cdot |s| ^ 3 + s ^ 2 / 2 \cdot \mathit{fluctuationBound} n p$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.conditional_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.5 (Expect sub).**

$$\forall (E: \mathit{Type}), [\mathit{AddCommGroup} E] [\mathrm{anonymous}\mathit{root}\mathrm{anonymous}.\mathit{Module} \mathbb{R} E] \forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (j: \mathbb{N}), \forall (f: \mathbb{N} \to E), \forall (g: \mathbb{N} \to E), (\mathit{expect} n p j \mathit{fun} (x : \mathbb{N}) => f x - g x) = \mathit{expect} n p j f - \mathit{expect} n p j g$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.expect_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.6 (Fluctuation Bound).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), (\mathit{fluctuationBound} n p : \mathbb{R}) = p / \mathit{val} n \cdot \operatorname{sqrt} \mathit{val} n$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.fluctuationBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.7 (Gaussian Factor).**

$$\forall (s: \mathbb{R}), \forall (u: \mathbb{R}), (\mathit{gaussianFactor} s u : \mathbb{C}) = \mathit{val} (\mathit{Real}.\mathit{exp} (-s ^ 2 \cdot u / 2))$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.gaussianFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.8 (Inst Measurable Singleton Class Option Fin d5).**

$$\forall (n: \mathbb{N}), \mathit{MeasurableSingletonClass} (\mathit{Option} (\mathit{Fin} n))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.instMeasurableSingletonClassOptionFin_d5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.9 (Inst Measurable Space Option Fin d5).**

$$\forall (n: \mathbb{N}), (\mathit{instMeasurableSpaceOptionFin}\mathrm{anonymous}\mathit{d5} n : \mathit{MeasurableSpace} (\mathit{Option} (\mathit{Fin} n))) = \operatorname{top}$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.instMeasurableSpaceOptionFin_d5` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.10 (Integral count).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (p: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hpUpper}: p \leq 1), \forall (j: \mathbb{N}), \int (\omega : \mathit{DiscardedOccupancy}.\mathit{History} n j), \mathit{val} (\mathit{count} n j \omega) d (\mathit{wordPMF} \mathit{hn} \mathit{hp} \mathit{hpUpper} j).\mathit{toMeasure} = \mathit{mean} n p j$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.integral_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.11 (Mem occupied iff).**

$$\forall (n: \mathbb{N}), \forall (i: \mathit{Fin} n), \forall (j: \mathbb{N}), \forall (\omega: \mathit{DiscardedOccupancy}.\mathit{History} n j), i \in \mathit{occupied} n j \omega \iff \exists (t : \mathit{Fin} j), \omega t = \mathit{some} i$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.mem_occupied_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.12 (Norm expect le).**

$$\forall (E: \mathit{Type}), [\mathit{NormedAddCommGroup} E] [\mathit{NormedSpace} \mathbb{R} E] \forall (n: \mathbb{N}), \forall (j: \mathbb{N}), \forall (p: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hpUpper}: p \leq 1), \forall (f: \mathbb{N} \to E), \Vert \mathit{expect} n p j f\Vert \leq \mathit{expect} n p j \mathit{fun} (x : \mathbb{N}) => \Vert f x\Vert$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.norm_expect_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.13 (Norm gaussian Factor le).**

$$\forall (s: \mathbb{R}), \forall (u: \mathbb{R}), \forall (\mathit{hu}: 0 \leq u), \Vert \mathit{gaussianFactor} s u\Vert \leq 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.norm_gaussianFactor_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.14 (Palette P).**

$$\forall (k: \mathbb{N}), (\mathit{paletteP} k : \mathbb{R}) = (\mathit{val} k) ^(-1)$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.paletteP` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.15 (Palette bounds).**

$$\forall (k: \mathbb{N}), \forall (\mathit{hk}: 2 \leq k), 0 < \mathit{paletteP} k \land \mathit{paletteP} k < 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.palette_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.16 (Palette throw mass).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (\mathit{hk}: 2 \leq k), (\mathit{throwPMF} n (\mathit{paletteP} k)).\mathit{toMeasure} \{\mathit{none}\} = \mathit{ENNReal}.\mathit{ofReal} (1 - 1 / \mathit{val} k) \land \forall (i : \mathit{Fin} n), (\mathit{throwPMF} n (\mathit{paletteP} k)).\mathit{toMeasure} \{\mathit{some} i\} = \mathit{ENNReal}.\mathit{ofReal} (1 / (\mathit{val} k \cdot \mathit{val} n))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.palette_throw_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.17 (Phase).**

$$\forall (s: \mathbb{R}), (\mathit{phase} s : \mathbb{C}) = \mathit{Complex}.\mathit{exp} (\mathit{val} s \cdot \mathit{Complex}.I)$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.phase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.18 (Predictable Variance).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (j: \mathbb{N}), (\mathit{predictableVariance} n p j : \mathbb{R}) = v n p (\mathit{mean} n p j)$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.predictableVariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.19 (Row Law).**

$$\forall (k: \mathbb{N}), \forall (\mathit{hk}: 2 \leq k), \forall (N: \mathbb{N}), (\mathit{rowLaw} k \mathit{hk} N : \mathit{MeasureTheory}.\mathit{ProbabilityMeasure} \mathbb{R}) = \mathit{standardizedLaw} (N + 1) (\mathit{paletteP} k) N$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.rowLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.20 (Row Phase).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (j: \mathbb{N}), \forall (s: \mathbb{R}), (\mathit{rowPhase} n p j s : \mathbb{C}) = \mathit{expect} n p j \mathit{fun} (x : \mathbb{N}) => \mathit{phase} (s \cdot (\mathit{val} x - \mathit{mean} n p j))$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.rowPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.21 (Row Phase zero).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (s: \mathbb{R}), \mathit{rowPhase} n p 0 s = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.rowPhase_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.22 (Standardized).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (j: \mathbb{N}), \forall (x: \mathbb{N}), (\mathit{standardized} n p j x : \mathbb{R}) = (\mathit{val} x - \mathit{mean} n p j) / \operatorname{sqrt} (\mathit{variance} n p j)$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.standardized` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.23 (Standardized Law).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (p: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hpUpper}: p \leq 1), \forall (j: \mathbb{N}), (\mathit{standardizedLaw} n \mathit{hn} p \mathit{hp} \mathit{hpUpper} j : \mathit{MeasureTheory}.\mathit{ProbabilityMeasure} \mathbb{R}) = \langle \mathit{MeasureTheory}.\mathit{Measure}.\mathit{map} (\mathit{fun} (\omega : \mathit{DiscardedOccupancy}.\mathit{History} n j) => \mathit{standardized} n p j (\mathit{count} n j \omega)) (\mathit{wordPMF} \mathit{hn} \mathit{hp} \mathit{hpUpper} j).\mathit{toMeasure}\rangle$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.standardizedLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.24 (Throw PMF).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (p: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hpUpper}: p \leq 1), (\mathit{throwPMF} n \mathit{hn} p \mathit{hp} \mathit{hpUpper} : \mathit{PMF} (\mathit{Option} (\mathit{Fin} n))) = \mathit{PMF}.\mathit{ofFintype} (\mathit{fun} (b : \mathit{Option} (\mathit{Fin} n)) => \mathit{ENNReal}.\mathit{ofReal} (\mathit{throwMass} n p b))$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.throwPMF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.25 (Variance count).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (p: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hpUpper}: p \leq 1), \forall (j: \mathbb{N}), \mathit{ProbabilityTheory}.\mathit{variance} (\mathit{fun} (\omega : \mathit{DiscardedOccupancy}.\mathit{History} n j) => \mathit{val} (\mathit{count} n j \omega)) (\mathit{wordPMF} \mathit{hn} \mathit{hp} \mathit{hpUpper} j).\mathit{toMeasure} = \mathit{variance} n p j$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.variance_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.26 (Variance fluctuation).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (p: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hpUpper}: p \leq 1), \forall (j: \mathbb{N}), \forall (\mathit{hj}: j \leq n), (\mathit{expect} n p j \mathit{fun} (x : \mathbb{N}) => |v n p \mathit{val} x - \mathit{predictableVariance} n p j|) \leq \mathit{fluctuationBound} n p$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.variance_fluctuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.27 (Weight).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (m: \mathbb{N}), \forall (j: \mathbb{N}), (\mathit{weight} n p m j : \mathbb{R}) = a n p ^ (m - j)$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.28 (Word PMF).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (p: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hpUpper}: p \leq 1), \forall (j: \mathbb{N}), (\mathit{wordPMF} n \mathit{hn} p \mathit{hp} \mathit{hpUpper} j : \mathit{PMF} (\mathit{DiscardedOccupancy}.\mathit{History} n j)) = \mathit{PMF}.\mathit{ofFintype} (\mathit{fun} (w : \mathit{History} n j) => \mathit{ENNReal}.\mathit{ofReal} (\mathit{wordMass} n p w))$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.wordPMF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

## References

- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.centeredBernoulli`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.charFun_standardizedLaw`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.conditional_comparison`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.expect_sub`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.fluctuationBound`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.gaussianFactor`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.instMeasurableSingletonClassOptionFin_d5`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.instMeasurableSpaceOptionFin_d5`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.integral_count`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.mem_occupied_iff`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.norm_expect_le`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.norm_gaussianFactor_le`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.paletteP`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.palette_bounds`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.palette_throw_mass`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.phase`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.predictableVariance`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.rowLaw`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.rowPhase`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.rowPhase_zero`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.standardized`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.standardizedLaw`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.throwPMF`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.variance_count`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.variance_fluctuation`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.weight`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.wordMeasure_eq_pi`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.wordPMF`
- Dependency: [D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions](Transitions.md)
