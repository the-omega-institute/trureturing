# UniformParameterAnchor

## Abstract

Public declarations of UniformParameterAnchor, with complete parameters and the Lean operations.

**Definition 1.1 (Uniform.epsilon).**

$$\forall (n : \mathbb{N}) , \operatorname{Uniform}. \operatorname{epsilon} n = (1 \operatorname{HDiv}.\operatorname{hDiv} (1000000000 \cdot (\operatorname{val}\left(n\right))^{6}))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.epsilon` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.2 (Uniform.angle).**

$$\forall (n : \mathbb{N}) , \forall (i : Fin n) , \operatorname{Uniform}. \operatorname{angle} n i = (if \operatorname{val}\left(i\right) = 0 \operatorname{then} 0 \operatorname{else} if \operatorname{val}\left(i\right) + 1 = n \operatorname{then} \operatorname{Real}. pi \operatorname{else} \operatorname{Real}. pi \cdot (1 \operatorname{HDiv}.\operatorname{hDiv} 4 + \operatorname{val}\left(\operatorname{val}\left(i\right)\right) \cdot \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{epsilon} n))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.angle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.3 (Uniform.alpha).**

$$\forall (n : \mathbb{N}) , \forall (i : Fin n) , \operatorname{Uniform}. \operatorname{alpha} n i = (\operatorname{Complex}. exp (\operatorname{Complex}. I \cdot \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{angle} n i\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.4 (Uniform.beta).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n) , \operatorname{Uniform}. \operatorname{beta} n a = (1)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.beta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.5 (Uniform.anchorAlpha).**

$$\forall (n : \mathbb{N}) , \forall (i : Fin n) , \operatorname{Uniform}. \operatorname{anchorAlpha} n i = (if \operatorname{val}\left(i\right) = 0 \operatorname{then} 1 \operatorname{else} if \operatorname{val}\left(i\right) + 1 = n \operatorname{then} - 1 \operatorname{else} \operatorname{Complex}. exp (\operatorname{Complex}. I \cdot \operatorname{val}\left(\operatorname{Real}. pi \operatorname{HDiv}.\operatorname{hDiv} 4\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.anchorAlpha` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.6 (Uniform.epsilon_pos).**

$$\forall (n : \mathbb{N}) , (0 < n) \to (0 < \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{epsilon} n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.epsilon_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.7 (Uniform.alpha_norm).**

$$\forall (n : \mathbb{N}) , \forall (i : Fin n) , \left\lVert \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} n i \right\rVert = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.alpha_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.8 (Uniform.admissible).**

$$\forall (n : \mathbb{N}) , (3 \leq n) \to (\operatorname{ConstructionReduction}. \operatorname{Admissible} (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} n) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} n))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.9 (Uniform.alpha_anchor_distance).**

$$\forall (n : \mathbb{N}) , (3 \leq n) \to (\forall (i : Fin n) , \left\lVert \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} n i - \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{anchorAlpha} n i \right\rVert \leq \operatorname{Real}. pi \cdot \operatorname{val}\left(n\right) \cdot \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{epsilon} n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.alpha_anchor_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.10 (Uniform.operator_perturbation).**

$$\forall (n : \mathbb{N}) , (3 \leq n) \to (\forall (r : \mathbb{R}) , (\operatorname{norm} \circ \operatorname{val}\left(\operatorname{Matrix}. \operatorname{toEuclideanCLM}\right)) (\operatorname{ConstructionReduction}. D (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} n) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} n) r - \operatorname{ConstructionReduction}. D (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{anchorAlpha} n) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} n) r) \leq 2 \cdot \operatorname{Real}. pi \operatorname{HDiv}.\operatorname{hDiv} (1000000000 \cdot (\operatorname{val}\left(n\right))^{4}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.operator_perturbation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.11 (Uniform.uniform_coordinate_lower).**

$$\forall (n : \mathbb{N}) , (17 \leq n) \to (\forall (r : \mathbb{R}) , \forall (x : \mathbb{R}) , (161 \operatorname{HDiv}.\operatorname{hDiv} 32 < r) \to (((r)^{2} \leq 9 \cdot \operatorname{val}\left(n\right)) \to (((r - 5) \operatorname{HDiv}.\operatorname{hDiv} (r)^{2} \leq x) \to (1 \operatorname{HDiv}.\operatorname{hDiv} (288 \cdot \operatorname{val}\left(n\right)) < x))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.uniform_coordinate_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.12 (Uniform.three_halfplanes_star).**

$$\forall (n : \mathbb{N}) , (3 \leq n) \to (\forall (a : Fin n \to \mathbb{C}) , \forall (b : Fin n \to \mathbb{C}) , \forall (w : Fin n \to \mathbb{C}) , \forall (\operatorname{zAlpha} : \mathbb{C}) , \forall (\operatorname{zBeta} : \mathbb{C}) , \forall (\operatorname{zEnds} : \mathbb{C}) , (\forall (i : Fin n) , \operatorname{val}\left(i\right) + 1 \neq n \to 0 < (\operatorname{zAlpha} \cdot (a i \cdot (\operatorname{starRingEnd} \mathbb{C}) (w i))) . re) \to ((\forall (i : Fin n) , \operatorname{val}\left(i\right) \neq 0 \to 0 < (\operatorname{zBeta} \cdot (b i \cdot (\operatorname{starRingEnd} \mathbb{C}) (w i))) . re) \to ((\forall (i : Fin n) , \operatorname{val}\left(i\right) = 0 \lor \operatorname{val}\left(i\right) + 1 = n \to 0 < (\operatorname{zEnds} \cdot (a i \cdot (\operatorname{starRingEnd} \mathbb{C}) (w i))) . re) \to (\operatorname{ConstructionReduction}. \operatorname{StarCondition} a b w))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.three_halfplanes_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.13 (Uniform.band).**

$$\forall (m : \mathbb{N}) , \operatorname{Uniform}. \operatorname{band} m = (\lambda (i j : Fin m) \mapsto if \operatorname{val}\left(i\right) + 1 = \operatorname{val}\left(j\right) \lor \operatorname{val}\left(j\right) + 1 = \operatorname{val}\left(i\right) \lor \operatorname{val}\left(i\right) + 2 = \operatorname{val}\left(j\right) \lor \operatorname{val}\left(j\right) + 2 = \operatorname{val}\left(i\right) \operatorname{then} 1 \operatorname{else} 0)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.band` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.14 (Uniform.band_hermitian).**

$$\forall (m : \mathbb{N}) , (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{band} m) . \operatorname{IsHermitian}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.band_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.15 (Uniform.band_row_bound).**

$$\forall (m : \mathbb{N}) , \forall (i : Fin m) , (\sum j : Fin m , \left\lVert \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{band} m i j \right\rVert) \leq 4$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.band_row_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.16 (Uniform.spike).**

$$\forall (m : \mathbb{N}) , \forall (a : Fin m) , \operatorname{Uniform}. \operatorname{spike} m a = (if \operatorname{val}\left(a\right) = 1 \operatorname{then} 2 \operatorname{else} 1)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.spike` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.17 (Uniform.spike_lower).**

$$\forall (m : \mathbb{N}) , \forall (i : Fin m) , 1 \leq \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{spike} m i$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.spike_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.18 (Uniform.phase_aligned_stability).**

$$\forall (H : \operatorname{Type}*) , \forall [\operatorname{NormedAddCommGroup} H] , \forall [\operatorname{InnerProductSpace} \mathbb{C} H] , \forall (A : H \to_{L} [\mathbb{C}] H) , \forall (E : H \to_{L} [\mathbb{C}] H) , \forall (q : H) , \forall (q' : H) , \forall (lam : \mathbb{R}) , \forall (lam' : \mathbb{R}) , \forall (g : \mathbb{R}) , \forall (e : \mathbb{R}) , (0 < g) \to ((\left\lVert q \right\rVert = 1) \to ((\left\lVert q' \right\rVert = 1) \to ((A q = \operatorname{val}\left(lam\right) \cdot q) \to (((A + E) q' = \operatorname{val}\left(lam'\right) \cdot q') \to ((\forall (v : H) , \operatorname{inner} \mathbb{C} q v = 0 \to g \cdot \left\lVert v \right\rVert \leq \left\lVert A v - \operatorname{val}\left(lam\right) \cdot v \right\rVert) \to ((\left|lam' - lam\right| \leq e) \to ((\left\lVert E \right\rVert \leq e) \to (\exists (z : \mathbb{C}) , \left\lVert z \right\rVert = 1 \land \left\lVert z \cdot q' - q \right\rVert \leq 4 \cdot e \operatorname{HDiv}.\operatorname{hDiv} g))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.phase_aligned_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.19 (Uniform.surviving_projection).**

$$\forall (n : \mathbb{N}) , (17 \leq n) \to (\forall (a : Fin n \to \mathbb{C}) , \forall (a' : Fin n \to \mathbb{C}) , \forall (q : \operatorname{EuclideanSpace} \mathbb{C} (Fin n)) , \forall (q' : \operatorname{EuclideanSpace} \mathbb{C} (Fin n)) , \forall (z : \mathbb{C}) , \forall (i : Fin n) , (\left\lVert z \right\rVert = 1) \to ((\left\lVert a' i \right\rVert = 1) \to ((\left\lVert q \right\rVert = 1) \to ((1 \operatorname{HDiv}.\operatorname{hDiv} (100000 \cdot (\operatorname{val}\left(n\right))^{3}) \leq (z \cdot (a i \cdot (\operatorname{starRingEnd} \mathbb{C}) (q. \operatorname{ofLp} i))) . re) \to ((\left\lVert q' - q \right\rVert + \left\lVert a' i - a i \right\rVert \leq 73 \cdot \operatorname{Real}. pi \operatorname{HDiv}.\operatorname{hDiv} (1000000000 \cdot (\operatorname{val}\left(n\right))^{3})) \to (1 \operatorname{HDiv}.\operatorname{hDiv} (200000 \cdot (\operatorname{val}\left(n\right))^{3}) \leq (z \cdot (a' i \cdot (\operatorname{starRingEnd} \mathbb{C}) (q'. \operatorname{ofLp} i))) . re))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.surviving_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.20 (Uniform.perturbation_error_small).**

$$\forall (n : \mathbb{N}) , (17 \leq n) \to (2 \cdot \operatorname{Real}. pi \operatorname{HDiv}.\operatorname{hDiv} (1000000000 \cdot (\operatorname{val}\left(n\right))^{4}) < 1 \operatorname{HDiv}.\operatorname{hDiv} (36 \cdot \operatorname{val}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.perturbation_error_small` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.21 (Uniform.shifted_gap).**

$$\forall (n : \mathbb{N}) , (17 \leq n) \to (\forall (x : \mathbb{R}) , \forall (y : \mathbb{R}) , \forall (x' : \mathbb{R}) , \forall (y' : \mathbb{R}) , (1 \operatorname{HDiv}.\operatorname{hDiv} (9 \cdot \operatorname{val}\left(n\right)) \leq x - y) \to ((\left|x' - x\right| \leq 2 \cdot \operatorname{Real}. pi \operatorname{HDiv}.\operatorname{hDiv} (1000000000 \cdot (\operatorname{val}\left(n\right))^{4})) \to ((\left|y' - y\right| \leq 2 \cdot \operatorname{Real}. pi \operatorname{HDiv}.\operatorname{hDiv} (1000000000 \cdot (\operatorname{val}\left(n\right))^{4})) \to (1 \operatorname{HDiv}.\operatorname{hDiv} (18 \cdot \operatorname{val}\left(n\right)) \leq x' - y'))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.shifted_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.22 (Uniform.stability_error_budget).**

$$\forall (n : \mathbb{N}) , (17 \leq n) \to (\forall (g : \mathbb{R}) , \forall (e : \mathbb{R}) , (1 \operatorname{HDiv}.\operatorname{hDiv} (9 \cdot \operatorname{val}\left(n\right)) \leq g) \to ((0 \leq e) \to ((e \leq 2 \cdot \operatorname{Real}. pi \operatorname{HDiv}.\operatorname{hDiv} (1000000000 \cdot (\operatorname{val}\left(n\right))^{4})) \to (4 \cdot e \operatorname{HDiv}.\operatorname{hDiv} g + \operatorname{Real}. pi \cdot \operatorname{val}\left(n\right) \cdot \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{epsilon} n \leq 73 \cdot \operatorname{Real}. pi \operatorname{HDiv}.\operatorname{hDiv} (1000000000 \cdot (\operatorname{val}\left(n\right))^{3})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.stability_error_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.23 (Uniform.resolvent).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , \operatorname{Uniform}. \operatorname{resolvent} m r = (r \cdot 1 + \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{band} m)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.resolvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.24 (Uniform.resolvent_isUnit).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , (5 < r) \to (\operatorname{IsUnit} (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{resolvent} m r))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.resolvent_isUnit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.25 (Uniform.anchorInterior).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , \forall (a : Fin m) , \operatorname{Uniform}. \operatorname{anchorInterior} m r a = (((\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{resolvent} m r))^{- 1} . \operatorname{mulVec} (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{spike} m) a)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.anchorInterior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.26 (Uniform.anchorInterior_solve).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , (5 < r) \to ((\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{resolvent} m r) . \operatorname{mulVec} (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{anchorInterior} m r) = \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{spike} m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.anchorInterior_solve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.27 (Uniform.anchorInterior_positive).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , (5 < r) \to (\forall (i : Fin m) , 0 < \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{anchorInterior} m r i \land (r - 5) \operatorname{HDiv}.\operatorname{hDiv} (r)^{2} \leq \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{anchorInterior} m r i)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.anchorInterior_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.28 (Uniform.band_reverse).**

$$\forall (m : \mathbb{N}) , \forall (i : Fin m) , \forall (j : Fin m) , \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{band} m i. rev j. rev = \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{band} m i j$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.band_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.29 (Uniform.anchorInterior_upper).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , (5 < r) \to (\forall (i : Fin m) , \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{anchorInterior} m r i \leq 2 \operatorname{HDiv}.\operatorname{hDiv} (r - 4))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.anchorInterior_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.30 (Uniform.pencil_top_largest).**

$$\forall (n : \mathbb{N}) , \forall (hn : 0 < n) , \forall (A : \operatorname{Matrix} (Fin n) (Fin n) \mathbb{C}) , \forall (hA : A. \operatorname{IsHermitian}) , \operatorname{have} k_{0} := \langle 0 , hn \rangle ; \operatorname{have} r := hA. \operatorname{eigenvalues}_{0} k_{0} ; (\operatorname{ConstructionReduction}. \operatorname{Spectral}. \operatorname{pencil} A r) . det = 0 \land (\forall (s : \mathbb{R}) , (\operatorname{ConstructionReduction}. \operatorname{Spectral}. \operatorname{pencil} A s) . det = 0 \to s \leq r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.pencil_top_largest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.31 (Uniform.simple_root_of_rank).**

$$\forall (n : \mathbb{N}) , (0 < n) \to (\forall (A : \operatorname{Matrix} (Fin n) (Fin n) \mathbb{C}) , (A. \operatorname{IsHermitian}) \to (\forall (r : \mathbb{R}) , ((\operatorname{ConstructionReduction}. \operatorname{Spectral}. \operatorname{pencil} A r) . det = 0) \to (((\operatorname{ConstructionReduction}. \operatorname{Spectral}. \operatorname{pencil} A r) . \operatorname{rank} = n - 1) \to (\exists (d : \mathbb{R}) , d \neq 0 \land \operatorname{HasDerivAt} (\lambda (s : \mathbb{R}) \mapsto (\operatorname{ConstructionReduction}. \operatorname{Spectral}. \operatorname{pencil} A s) . det. re) d r))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.simple_root_of_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.32 (Uniform.negative_eigenvalue_perturbation).**

$$\forall (n : \mathbb{N}) , \forall (hn : 3 \leq n) , \forall (k : Fin (\operatorname{Fintype}. \operatorname{card} (Fin n))) , \left|((\operatorname{ConstructionReduction}. D_{\operatorname{hermitian}} hn (\operatorname{Uniform}. \operatorname{alpha} n) (\operatorname{Uniform}. \operatorname{beta} n) 0) . neg) . \operatorname{eigenvalues}_{0} k - ((\operatorname{ConstructionReduction}. D_{\operatorname{hermitian}} hn (\operatorname{Uniform}. \operatorname{anchorAlpha} n) (\operatorname{Uniform}. \operatorname{beta} n) 0) . neg) . \operatorname{eigenvalues}_{0} k\right| \leq 2 \cdot \operatorname{Real}. pi \operatorname{HDiv}.\operatorname{hDiv} (1000000000 \cdot ((n : \mathbb{R}))^{4})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.negative_eigenvalue_perturbation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.33 (Uniform.top_root_simple).**

$$\forall (n : \mathbb{N}) , \forall (hn : 0 < n) , \forall (A : \operatorname{Matrix} (Fin n) (Fin n) \mathbb{C}) , \forall (hA : A. \operatorname{IsHermitian}) , (\forall (k : Fin (\operatorname{Fintype}. \operatorname{card} (Fin n))) , \operatorname{val}\left(k\right) \neq 0 \to hA. \operatorname{eigenvalues}_{0} k < hA. \operatorname{eigenvalues}_{0} \langle 0 , hn \rangle) \to (\operatorname{have} r := hA. \operatorname{eigenvalues}_{0} \langle 0 , hn \rangle ; \exists (d : \mathbb{R}) , d \neq 0 \land \operatorname{HasDerivAt} (\lambda (s : \mathbb{R}) \mapsto (\operatorname{ConstructionReduction}. \operatorname{Spectral}. \operatorname{pencil} A s) . det. re) d r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.top_root_simple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.34 (Anchor17Probe.R).**

$$\operatorname{Anchor17Probe}. R = (161 \operatorname{HDiv}.\operatorname{hDiv} 32)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.35 (Anchor17Probe.den).**

$$\operatorname{Anchor17Probe}. den = (467481426546007099229949447217505)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.den` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.36 (Anchor17Probe.numerators).**

$$\forall (a : Fin 15) , \operatorname{Anchor17Probe}. \operatorname{numerators} a = (! [54327066786808963613640806075424 , 162449231862550997644964313113664 , 31699139912323503403854828536864 , 31613948584422024541176559469600 , 59604881628347486929523162482720 , 54670494327411800278812578252832 , 49610783029226477391942069717024 , 51590888719220490214531871213600 , 52010909755231607428873297004576 , 51622580565559122738458025199648 , 52977284525991984008498705532960 , 51176235075093681300178634180640 , 46129738378725518219680378619936 , 59271390354165390221788584643616 , 71966270372793280156716617928736] a)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.numerators` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.37 (Anchor17Probe.u).**

$$\forall (a : Fin 15) , \operatorname{Anchor17Probe}. u a = (\operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. \operatorname{numerators} a\right) \operatorname{HDiv}.\operatorname{hDiv} \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. den\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.u` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.38 (Anchor17Probe.rational_solve).**

$$(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. R \cdot 1 + \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{band} 15) . \operatorname{mulVec} \operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. u = \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{spike} 15$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.rational_solve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.39 (Anchor17Probe.knum).**

$$\operatorname{Anchor17Probe}. \operatorname{knum} = (1043170075740423325737604745085504)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.knum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.40 (Anchor17Probe.lnum).**

$$\operatorname{Anchor17Probe}. \operatorname{lnum} = (939992234232037718314429016615456)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.lnum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.41 (Anchor17Probe.k_value).**

$$\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{spike} 15 \cdot \operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. u = \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. \operatorname{knum}\right) \operatorname{HDiv}.\operatorname{hDiv} \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. den\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.k_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.42 (Anchor17Probe.ell_value).**

$$(\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{spike} 15 \cdot \lambda (i : Fin 15) \mapsto \operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. u i. rev) = \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. \operatorname{lnum}\right) \operatorname{HDiv}.\operatorname{hDiv} \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. den\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.ell_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.43 (Anchor17Probe.aa).**

$$\operatorname{Anchor17Probe}. aa = (\operatorname{val}\left(\operatorname{Real}. \operatorname{sqrt} 2 \operatorname{HDiv}.\operatorname{hDiv} 2\right) + \operatorname{val}\left(\operatorname{Real}. \operatorname{sqrt} 2 \operatorname{HDiv}.\operatorname{hDiv} 2\right) \cdot \operatorname{Complex}. I)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.aa` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.44 (Anchor17Probe.aa_anchor).**

$$\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. aa = \operatorname{Complex}. exp (\operatorname{Complex}. I \cdot \operatorname{val}\left(\operatorname{Real}. pi \operatorname{HDiv}.\operatorname{hDiv} 4\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.aa_anchor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.45 (Anchor17Probe.probeSchur).**

$$\operatorname{Anchor17Probe}. \operatorname{probeSchur} = (! ! [\operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. R - \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. \operatorname{knum}\right) \operatorname{HDiv}.\operatorname{hDiv} \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. den\right)\right) , - 1 - (\operatorname{starRingEnd} \mathbb{C}) \operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. aa \cdot \operatorname{val}\left(\operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. \operatorname{lnum}\right) \operatorname{HDiv}.\operatorname{hDiv} \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. den\right)\right) ; - 1 - \operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. aa \cdot \operatorname{val}\left(\operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. \operatorname{lnum}\right) \operatorname{HDiv}.\operatorname{hDiv} \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. den\right)\right) , \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. R - \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. \operatorname{knum}\right) \operatorname{HDiv}.\operatorname{hDiv} \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. den\right)\right)])$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.probeSchur` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.46 (Anchor17Probe.schur_det_negative).**

$$\operatorname{UniformParameterAnchor}. \operatorname{Anchor17Probe}. \operatorname{probeSchur}. det. re < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.schur_det_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.47 (Anchor.a).**

$$\operatorname{Anchor}. a = (\operatorname{Complex}. exp (\operatorname{Complex}. I \cdot \operatorname{val}\left(\operatorname{Real}. pi\right) \cdot (1 \operatorname{HDiv}.\operatorname{hDiv} 4)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.48 (Anchor.address).**

$$\forall (m : \mathbb{N}) , \operatorname{Anchor}. \operatorname{address} m = (\operatorname{Equiv}. \operatorname{sumCongr} (\operatorname{finSumFinEquiv} (\operatorname{m} := 1) (\operatorname{n} := 1)). \operatorname{symm} (\operatorname{Equiv}. \operatorname{refl} (\operatorname{Fin} m))). \operatorname{trans} ((\operatorname{Equiv}. \operatorname{sumAssoc} (\operatorname{Fin} 1) (\operatorname{Fin} 1) (\operatorname{Fin} m)). \operatorname{trans} ((\operatorname{Equiv}. \operatorname{sumCongr} (\operatorname{Equiv}. \operatorname{refl} (\operatorname{Fin} 1)) (\operatorname{Equiv}. \operatorname{sumComm} (\operatorname{Fin} 1) (\operatorname{Fin} m))). \operatorname{trans} ((\operatorname{Equiv}. \operatorname{sumCongr} (\operatorname{Equiv}. \operatorname{refl} (\operatorname{Fin} 1)) (\operatorname{finSumFinEquiv} (\operatorname{m} := m) (\operatorname{n} := 1))). \operatorname{trans} ((\operatorname{finSumFinEquiv} (\operatorname{m} := 1) (\operatorname{n} := (m + 1))). \operatorname{trans} ((\operatorname{finCongr} (\operatorname{by} \operatorname{omega})))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.address` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion. The defining forward map uses Mathlib’s Fin constructors; The equivalence sends Sum.inl 0 to 0, Sum.inl 1 to m+1, and Sum.inr i to i.val+1. Its inverse sends 0 to Sum.inl 0, m+1 to Sum.inl 1, and every other i to Sum.inr ⟨i.val−1, the induced bound⟩. The left and right inverse fields prove these literal formulas.

**Definition 1.49 (Anchor.endpoints).**

$$\forall (r : \mathbb{R}) , \operatorname{Anchor}. \operatorname{endpoints} r = (! ! [\operatorname{val}\left(r\right) , - 1 ; - 1 , \operatorname{val}\left(r\right)])$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.endpoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.50 (Anchor.coupling).**

$$\forall (m : \mathbb{N}) , \operatorname{Anchor}. \operatorname{coupling} m = (\lambda (i : Fin m) (j : Fin 2) \mapsto if \operatorname{val}\left(j\right) = 0 \operatorname{then} \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. a \cdot \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{spike} m i\right) \operatorname{else} \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{spike} m i. rev\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.coupling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.51 (Anchor.interior).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , \operatorname{Anchor}. \operatorname{interior} m r = ((\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{resolvent} m r) . map \operatorname{Complex}. \operatorname{ofReal})$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.interior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.52 (Anchor.block).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , \operatorname{Anchor}. \operatorname{block} m r = (\operatorname{Matrix}. \operatorname{fromBlocks} (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{endpoints} r) (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{coupling} m) . \operatorname{conjTranspose} (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{coupling} m) (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{interior} m r))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.block` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.53 (Anchor.phase_def).**

$$\operatorname{Complex}. exp (\operatorname{Complex}. I \cdot \operatorname{val}\left(\operatorname{Real}. pi \operatorname{HDiv}.\operatorname{hDiv} 4\right)) = \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. a$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.phase_def` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.54 (Anchor.phase_unit).**

$$\left\lVert \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. a \right\rVert = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.phase_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.55 (Anchor.phase_mul_conj).**

$$\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. a \cdot (\operatorname{starRingEnd} \mathbb{C}) \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. a = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.phase_mul_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.56 (Anchor.anchor_reindex).**

$$\forall (m : \mathbb{N}) , (4 \leq m) \to (\forall (r : \mathbb{R}) , (\operatorname{ConstructionReduction}. D (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{anchorAlpha} (m + 2)) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} (m + 2)) r) . \operatorname{submatrix} \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{address} m\right) \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{address} m\right) = \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{block} m r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.anchor_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.57 (Anchor.k).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , \operatorname{Anchor}. k m r = (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{spike} m \cdot \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{anchorInterior} m r)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.k` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.58 (Anchor.ell).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , \operatorname{Anchor}. ell m r = (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{spike} m \cdot (\lambda (m : \mathbb{N}) (r : \mathbb{R}) (i : Fin m) \mapsto \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{anchorInterior} m r i. rev) m r)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.ell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.59 (Anchor.zeta).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , \operatorname{Anchor}. \operatorname{zeta} m r = (1 + \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. a \cdot \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. ell m r\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.zeta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.60 (Anchor.b).**

$$\forall (m : \mathbb{N}) (r : \mathbb{R}) , \operatorname{Anchor}. \operatorname{b} m r = \operatorname{NormedSpace}. \operatorname{normalize} (\operatorname{Anchor}. \operatorname{zeta} m r)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.61 (Anchor.kernelBlock).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , \forall (a : Sum (Fin 2) (Fin m)) , \operatorname{Anchor}. \operatorname{kernelBlock} m r a = (Sum. \operatorname{elim} ! [(\operatorname{starRingEnd} \mathbb{C}) (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. b m r) , 1] (\lambda (i : Fin m) \mapsto - (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. a \cdot (\operatorname{starRingEnd} \mathbb{C}) (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. b m r) \cdot \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{anchorInterior} m r i\right) + \operatorname{val}\left((\lambda (m : \mathbb{N}) (r : \mathbb{R}) (i : Fin m) \mapsto \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{anchorInterior} m r i. rev) m r i\right))) a)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.kernelBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.62 (Anchor.kernel).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , \forall (a : Fin (m + 2)) , \operatorname{Anchor}. \operatorname{kernel} m r a = (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{kernelBlock} m r ((\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{address} m) . \operatorname{symm} a))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.kernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.63 (Anchor.a_cartesian).**

$$\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. a = \operatorname{val}\left(\operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{Information}. \operatorname{BinaryStabilizerLocalInequivalence}. s2. re\right) + \operatorname{val}\left(\operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{Information}. \operatorname{BinaryStabilizerLocalInequivalence}. s2. re\right) \cdot \operatorname{Complex}. I$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.a_cartesian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.64 (Anchor.h_positive).**

$$0 < \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{Information}. \operatorname{BinaryStabilizerLocalInequivalence}. s2. re$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.h_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.65 (Anchor.ell_positive).**

$$\forall (m : \mathbb{N}) , (0 < m) \to (\forall (r : \mathbb{R}) , (5 < r) \to (0 < \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. ell m r))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.ell_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.66 (Anchor.zeta_re).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{zeta} m r) . re = 1 + \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{Information}. \operatorname{BinaryStabilizerLocalInequivalence}. s2. re \cdot \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. ell m r$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.zeta_re` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.67 (Anchor.zeta_im).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{zeta} m r) . im = \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{Information}. \operatorname{BinaryStabilizerLocalInequivalence}. s2. re \cdot \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. ell m r$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.zeta_im` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.68 (Anchor.zeta_norm_pos).**

$$\forall (m : \mathbb{N}) , (0 < m) \to (\forall (r : \mathbb{R}) , (5 < r) \to (0 < \left\lVert \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{zeta} m r \right\rVert))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.zeta_norm_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.69 (Anchor.b_unit).**

$$\forall (m : \mathbb{N}) , (0 < m) \to (\forall (r : \mathbb{R}) , (5 < r) \to (\left\lVert \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. b m r \right\rVert = 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.b_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.70 (Anchor.d).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , \operatorname{Anchor}. d m r = (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. a \cdot (\operatorname{starRingEnd} \mathbb{C}) (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. b m r))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.d` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.71 (Anchor.d_unit).**

$$\forall (m : \mathbb{N}) , (0 < m) \to (\forall (r : \mathbb{R}) , (5 < r) \to (\left\lVert \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. d m r \right\rVert = 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.d_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.72 (Anchor.d_im_pos).**

$$\forall (m : \mathbb{N}) , (0 < m) \to (\forall (r : \mathbb{R}) , (5 < r) \to (0 < (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. d m r) . im))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.d_im_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.73 (Anchor.coupling_real).**

$$\forall (m : \mathbb{N}) , \forall (f : Fin m \to \mathbb{R}) , ((\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{coupling} m) . \operatorname{conjTranspose}. \operatorname{mulVec} \lambda (i : Fin m) \mapsto \operatorname{val}\left(f i\right)) = ! [(\operatorname{starRingEnd} \mathbb{C}) \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. a \cdot \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{spike} m \cdot f\right) , \operatorname{val}\left((\lambda (i : Fin m) \mapsto \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{spike} m i. rev) \cdot f\right)]$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.coupling_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.74 (Anchor.actual_kernel).**

$$\forall (m : \mathbb{N}) , (4 \leq m) \to (\forall (r : \mathbb{R}) , (5 < r) \to ((r - \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. k m r = \left\lVert \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{zeta} m r \right\rVert) \to ((\operatorname{ConstructionReduction}. D (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{anchorAlpha} (m + 2)) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} (m + 2)) r) . \operatorname{mulVec} (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{kernel} m r) = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.actual_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.75 (Anchor.interior_hermitian).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{interior} m r) . \operatorname{IsHermitian}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.interior_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.76 (Anchor.interior_posDef).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , (5 < r) \to ((\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{interior} m r) . \operatorname{PosDef})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.interior_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.77 (Anchor.inverseCoupling).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , \operatorname{Anchor}. \operatorname{inverseCoupling} m r = (\lambda (i : Fin m) (j : Fin 2) \mapsto if \operatorname{val}\left(j\right) = 0 \operatorname{then} \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. a \cdot \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{anchorInterior} m r i\right) \operatorname{else} \operatorname{val}\left((\lambda (m : \mathbb{N}) (r : \mathbb{R}) (i : Fin m) \mapsto \operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{anchorInterior} m r i. rev) m r i\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.inverseCoupling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.78 (Anchor.inverseCoupling_solve).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , (5 < r) \to (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{interior} m r \cdot \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{inverseCoupling} m r = \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{coupling} m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.inverseCoupling_solve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.79 (Anchor.inverseCoupling_eq).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , (5 < r) \to (((\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{interior} m r))^{- 1} \cdot \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{coupling} m = \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{inverseCoupling} m r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.inverseCoupling_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.80 (Anchor.schur).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , \operatorname{Anchor}. \operatorname{schur} m r = (! ! [\operatorname{val}\left(r - \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. k m r\right) , - 1 - (\operatorname{starRingEnd} \mathbb{C}) \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. a \cdot \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. ell m r\right) ; - 1 - \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. a \cdot \operatorname{val}\left(\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. ell m r\right) , \operatorname{val}\left(r - \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. k m r\right)])$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.schur` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.81 (Anchor.schur_eq).**

$$\forall (m : \mathbb{N}) , \forall (r : \mathbb{R}) , (5 < r) \to (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{endpoints} r - (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{coupling} m) . \operatorname{conjTranspose} \cdot ((\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{interior} m r))^{- 1} \cdot \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{coupling} m = \operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{schur} m r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.schur_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.R`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.a`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.a_cartesian`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.aa`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.aa_anchor`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.actual_kernel`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.address`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.admissible`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.alpha`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.alpha_anchor_distance`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.alpha_norm`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.anchorAlpha`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.anchorInterior`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.anchorInterior_positive`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.anchorInterior_solve`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.anchorInterior_upper`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.anchor_reindex`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.angle`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.b`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.b_unit`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.band`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.band_hermitian`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.band_reverse`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.band_row_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.beta`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.block`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.coupling`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.coupling_real`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.d`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.d_im_pos`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.d_unit`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.den`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.ell`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.ell_positive`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.ell_value`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.endpoints`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.epsilon`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.epsilon_pos`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.h_positive`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.interior`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.interior_hermitian`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.interior_posDef`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.inverseCoupling`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.inverseCoupling_eq`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.inverseCoupling_solve`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.k`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.k_value`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.kernel`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.kernelBlock`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.knum`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.lnum`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.negative_eigenvalue_perturbation`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.numerators`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.operator_perturbation`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.pencil_top_largest`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.perturbation_error_small`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.phase_aligned_stability`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.phase_def`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.phase_mul_conj`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.phase_unit`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.probeSchur`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.rational_solve`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.resolvent`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.resolvent_isUnit`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.schur`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.schur_det_negative`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.schur_eq`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.shifted_gap`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.simple_root_of_rank`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.spike`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.spike_lower`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.stability_error_budget`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.surviving_projection`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.three_halfplanes_star`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.top_root_simple`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.u`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.uniform_coordinate_lower`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.zeta`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.zeta_im`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.zeta_norm_pos`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.zeta_re`
- Dependency: [D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction](ConstructionReduction.md)
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence](../../Information/BinaryStabilizerLocalInequivalence.md)
- Dependency: [D5/S3/SpectralTopology/HermitianEigenvaluePerturbation](../../../SpectralTopology/HermitianEigenvaluePerturbation.md)
