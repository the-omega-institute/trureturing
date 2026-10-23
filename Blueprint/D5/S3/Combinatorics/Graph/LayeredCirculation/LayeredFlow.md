# LayeredFlow

## Abstract

The five patterns are ordered 000,100,010,001,101 and the three seam states are 00,01,10. A local law has arbitrary real nonnegative coordinates, one unit of mass at each position, and all four binary-pair overlap equations, including the zero 11 equation. The graph vertices are ZMod n times Fin 3 and edges are ZMod n times Fin 5. Its conservation laws use the actual source and target labels. Native bridges transport the exact upstream signed real decomposition to forward circuits, identify their winding numbers, and certify strict positive-support erasure.

Generic declarations use these source contexts:

**Definition 1.1 (pattern).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.pattern`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.pattern` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def pattern : Fin 5 → Bool × Bool × Bool := ![(false, false, false), (true, false, false), (false, true, false), (false, false, true), (true, false, true)]

**Definition 1.2 (seam).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.seam`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.seam` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def seam : Fin 3 → Bool × Bool := ![(false, false), (false, true), (true, false)]

**Definition 1.3 (sourceState).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.sourceState`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.sourceState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def sourceState : Fin 5 → Fin 3 := ![0, 2, 1, 0, 2]

**Definition 1.4 (targetState).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.targetState`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.targetState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def targetState : Fin 5 → Fin 3 := ![0, 0, 2, 1, 1]

**Definition 1.5 (IsLocalLaw).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.IsLocalLaw`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.IsLocalLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def IsLocalLaw {n : ℕ} (p : ZMod n → Fin 5 → ℝ) : Prop := (∀ i σ, 0 ≤ p i σ) ∧ (∀ i, ∑ σ, p i σ = 1) ∧ ∀ i b c, (∑ σ, if (pattern σ).2.1 = b ∧ (pattern σ).2.2 = c then p i σ else 0) = ∑ σ, if (pattern σ).1 = b ∧ (pattern σ).2.1 = c then p (i + 1) σ else 0

**Definition 1.6 (localScore).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.localScore`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.localScore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def localScore {n : ℕ} [NeZero n] (f p : ZMod n → Fin 5 → ℝ) : ℝ := ∑ i, ∑ σ, f i σ * p i σ

**Definition 1.7 (layeredGraph).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.layeredGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.layeredGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def layeredGraph (n : ℕ) : EdgeGraph (ZMod n × Fin 3) (ZMod n × Fin 5) where source e := (e.1, sourceState e.2) target e := (e.1 + 1, targetState e.2)

**Theorem 1.8 (labels).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.labels`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem labels (σ : Fin 5) : seam (sourceState σ) = ((pattern σ).1, (pattern σ).2.1) ∧ seam (targetState σ) = ((pattern σ).2.1, (pattern σ).2.2)

**Definition 1.9 (IsCirculation).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.IsCirculation`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.IsCirculation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def IsCirculation {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) : Prop := ∀ v, (∑ e, if (layeredGraph n).source e = v then p e.1 e.2 else 0) = ∑ e, if (layeredGraph n).target e = v then p e.1 e.2 else 0

**Theorem 1.10 (local law iff).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.local_law_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.local_law_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem local_law_iff {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) : IsLocalLaw p ↔ (∀ i σ, 0 ≤ p i σ) ∧ (∀ i, ∑ σ, p i σ = 1) ∧ IsCirculation p

**Definition 1.11 (layerCount).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.layerCount`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.layerCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def layerCount {n : ℕ} {a b : ZMod n × Fin 3} (w : (layeredGraph n).Walk a b) (i : ZMod n) : ℕ := ∑ σ, w.edgeMultiplicity (i,σ)

**Theorem 1.12 (layer count uniform).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.layer_count_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.layer_count_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem layer_count_uniform {n : ℕ} [NeZero n] {a : ZMod n × Fin 3} (w : (layeredGraph n).Walk a a) (i : ZMod n) : layerCount w i = layerCount w 0

**Theorem 1.13 (length eq layer count).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.length_eq_layer_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.length_eq_layer_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem length_eq_layer_count {n : ℕ} [NeZero n] {a : ZMod n × Fin 3} (w : (layeredGraph n).Walk a a) : w.length = n * layerCount w 0

**Definition 1.14 (walkLaw).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.walkLaw`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.walkLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def walkLaw {n : ℕ} {a : ZMod n × Fin 3} (w : (layeredGraph n).Walk a a) : ZMod n → Fin 5 → ℝ := fun i σ => w.edgeMultiplicity (i,σ) / layerCount w 0

**Theorem 1.15 (walk law local).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.walk_law_local`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.walk_law_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem walk_law_local {n : ℕ} [NeZero n] {a : ZMod n × Fin 3} (w : (layeredGraph n).Walk a a) (hw : 0 < w.length) : IsLocalLaw (walkLaw w)

**Theorem 1.16 (walk law score).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.walk_law_score`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.walk_law_score` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem walk_law_score {n : ℕ} [NeZero n] (f : ZMod n → Fin 5 → ℝ) {a : ZMod n × Fin 3} (w : (layeredGraph n).Walk a a) : localScore f (walkLaw w) = Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w / layerCount w 0

**Theorem 1.17 (simple cycle winding).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.simple_cycle_winding`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.simple_cycle_winding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem simple_cycle_winding {n : ℕ} [NeZero n] {a : ZMod n × Fin 3} (w : (layeredGraph n).Walk a a) (hw : IsSimpleCycle w) : 1 ≤ layerCount w 0 ∧ layerCount w 0 ≤ 3 ∧ w.length = n * layerCount w 0

**Theorem 1.18 (local simple cycle decomposition).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.local_simple_cycle_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.local_simple_cycle_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem local_simple_cycle_decomposition {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) (hp : IsLocalLaw p) : ∃ (ι : Type) (_ : Fintype ι) (weight : ι → ℝ) (base : ι → ZMod n × Fin 3) (cycle : ∀ i, (layeredGraph n).Walk (base i) (base i)), (∀ i, 0 ≤ weight i) ∧ (∑ i, weight i) = 1 ∧ (∀ i, 0 < weight i → IsSimpleCycle (cycle i)) ∧ (∀ i, 0 < weight i → 1 ≤ layerCount (cycle i) 0 ∧ layerCount (cycle i) 0 ≤ 3) ∧ (∀ i, 0 < weight i → IsLocalLaw (walkLaw (cycle i))) ∧ (∀ j σ, p j σ = ∑ i, weight i * walkLaw (cycle i) j σ) ∧ ∀ i, weight i = layerCount (cycle i) 0 * (weight i / layerCount (cycle i) 0)

**Definition 1.19 (positiveSupport).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.positiveSupport`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.positiveSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def positiveSupport {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) : Finset (ZMod n × Fin 5) := Finset.univ.filter (fun e => 0 < p e.1 e.2)

**Definition 1.20 (subtractCycle).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.subtractCycle`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.subtractCycle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def subtractCycle {n : ℕ} {a : ZMod n × Fin 3} (p : ZMod n → Fin 5 → ℝ) (w : (layeredGraph n).Walk a a) (α : ℝ) : ZMod n → Fin 5 → ℝ := fun i σ => p i σ - α * w.edgeMultiplicity (i,σ)

**Theorem 1.21 (positive cycle erasure).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.positive_cycle_erasure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.positive_cycle_erasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem positive_cycle_erasure {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) (hnonneg : ∀ i σ, 0 ≤ p i σ) (hbal : IsCirculation p) (hne : p ≠ 0) : ∃ (a : ZMod n × Fin 3) (w : (layeredGraph n).Walk a a) (α : ℝ), IsSimpleCycle w ∧ 0 < α ∧ (∀ e ∈ w.edges, α ≤ p e.1 e.2) ∧ (∃ e ∈ w.edges, p e.1 e.2=α) ∧ (∀ i σ, 0 ≤ subtractCycle p w α i σ) ∧ IsCirculation (subtractCycle p w α) ∧ (positiveSupport (subtractCycle p w α)).card < (positiveSupport p).card ∧ ∀ e, (w.edgeMultiplicity e : ℝ) = if e ∈ w.edges then 1 else 0

**Definition 1.22 (HasPositiveCycleDecomposition).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.HasPositiveCycleDecomposition`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.HasPositiveCycleDecomposition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def HasPositiveCycleDecomposition {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) : Prop := ∃ (ι : Type) (_ : Fintype ι) (base : ι → ZMod n × Fin 3) (cycle : ∀ i, (layeredGraph n).Walk (base i) (base i)) (α : ι → ℝ), (∀ i, IsSimpleCycle (cycle i) ∧ 0 < α i ∧ 1 ≤ layerCount (cycle i) 0 ∧ layerCount (cycle i) 0 ≤ 3 ∧ IsLocalLaw (walkLaw (cycle i)) ∧ (cycle i).length=layerCount (cycle i) 0 * n ∧ (∀ j, layerCount (cycle i) j=layerCount (cycle i) 0) ∧ ∀ e, ((cycle i).edgeMultiplicity e : ℝ) = if e ∈ (cycle i).edges then 1 else 0) ∧ (∑ i, (layerCount (cycle i) 0 : ℝ) * α i) = 1 ∧ (∀ j σ, p j σ = ∑ i, α i * (if (j,σ) ∈ (cycle i).edges then 1 else 0)) ∧ ∀ j σ, p j σ = ∑ i, ((layerCount (cycle i) 0 : ℝ) * α i) * walkLaw (cycle i) j σ

**Theorem 1.23 (positive cycle decomposition).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.positive_cycle_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.positive_cycle_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem positive_cycle_decomposition {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) (hp : IsLocalLaw p) : HasPositiveCycleDecomposition p

**Definition 1.24 (HasPositiveCycleErasure).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.HasPositiveCycleErasure`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.HasPositiveCycleErasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def HasPositiveCycleErasure {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) : Prop := ∃ (a : ZMod n × Fin 3) (w : (layeredGraph n).Walk a a) (α : ℝ), IsSimpleCycle w ∧ 0 < α ∧ (∀ e ∈ w.edges, α ≤ p e.1 e.2) ∧ (∃ e ∈ w.edges, p e.1 e.2=α) ∧ (∀ i σ, 0 ≤ subtractCycle p w α i σ) ∧ IsCirculation (subtractCycle p w α) ∧ (positiveSupport (subtractCycle p w α)).card < (positiveSupport p).card ∧ ∀ e, (w.edgeMultiplicity e : ℝ) = if e ∈ w.edges then 1 else 0

**Theorem 1.25 (local law compact).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.local_law_compact`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.local_law_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem local_law_compact {n : ℕ} [NeZero n] : IsCompact {p : ZMod n → Fin 5 → ℝ | IsLocalLaw p}

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.HasPositiveCycleDecomposition`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.HasPositiveCycleErasure`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.IsCirculation`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.IsLocalLaw`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.labels`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.layerCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.layer_count_uniform`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.layeredGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.length_eq_layer_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.localScore`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.local_law_compact`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.local_law_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.local_simple_cycle_decomposition`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.pattern`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.positiveSupport`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.positive_cycle_decomposition`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.positive_cycle_erasure`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.seam`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.simple_cycle_winding`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.sourceState`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.subtractCycle`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.targetState`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.walkLaw`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.walk_law_local`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.walk_law_score`
- Dependency: [D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier](PositiveCircuitSupplier.md)
