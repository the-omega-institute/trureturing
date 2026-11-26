import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.PartialDerivComm
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of measure and integration (textbook or folklore).

Part of: Invariant integration on a quotient (Weil's formula), unfolding, unimodularity (known
result; see Lib.Adelic.QuotientMeasure.Unimodular).

This file: Quotient measure defined by a cutoff weight of mass one on each orbit. Haar integrals
over subgroups: translation, character orthogonality, sums over finite quotients. -/

open AddSubgroup MeasureTheory Set

attribute [simp] lintegral_count withDensity_smul_measure ENNReal.tsum_prod' ENNReal.tsum_mul_left
  ENNReal.tsum_mul_right

variable {H X G} [MeasurableSpace H] [MeasurableSpace X] [SMul H X] (ν : Measure H) (μ : Measure X)
  [Group G] (N : Subgroup G) [TopologicalSpace G]

/-- The subgroup N of G is cocompact: there is a compact C ⊂ G such that every g has a translate
γg in C with γ ∈ N. -/
@[to_additive] abbrev Subgroup.Cocpt := ∃ C, IsCompact C ∧ ∀ g, ∃ γ ∈ N, γ * g ∈ C

/-- The function F on G is left invariant under the subgroup N: F(γg) = F(g) for all γ ∈ N and g
∈ G. -/
@[simp] abbrev Subgroup.FixesLeft {W} (F : G → W) := ∀ γ ∈ N, ∀ g, F (γ * g) = F g

/-- The property that β: X → [0, ∞] is measurable and ∫_H β(hx) dν(h) = 1 for every x in X. -/
@[to_additive IsAddCutoff] def IsCutoff β := Measurable β ∧ ∀ x : X, ∫⁻ h, β (h • x) ∂ν = 1

/-- The measure βμ on X for a chosen cutoff β of the action of (H, ν); integrating an
H-invariant function against it gives the integral over H\X. -/
@[to_additive addOrbitMeasure] noncomputable abbrev orbitMeasure :=
  μ.withDensity (Classical.epsilon (IsCutoff ν))

/-- The hypothesis that the action of H, with measure ν, on X admits a cutoff: a measurable
weight with integral one over each orbit. -/
@[to_additive HasAddCutoff] abbrev HasCutoff X [MeasurableSpace X] [SMul H X] := Fact
    (∃ β, IsCutoff (X := X) ν β)

@[to_additive] instance (priority := high) mulActionSubgroupSelf : MulAction N G := inferInstance

@[to_additive] instance (priority := high) smulSubgroupSelf : SMul N G := inferInstance

/-- The measure `orbitMeasure` on G for counting measure on the subgroup N and μ on G: μ weighted by
a chosen cutoff, computing integrals over N\G. -/
@[to_additive] noncomputable abbrev Subgroup.qms [MeasurableSpace G]
    (μ : Measure G := by volume_tac) := orbitMeasure (@Measure.count N _) μ

variable {V} {X : Type*} [AddCommGroup V] [MeasurableSpace V] {ν : Measure V} [ν.IsAddLeftInvariant]
  {M L : AddSubgroup V} [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [BorelSpace V]

lemma setIntegral_add_mem (F : V → X) {m} : m ∈ M → ∫ x in M, F (m + x) ∂ν = ∫ x in M, F x ∂ν := by
    simp_all [← (measurePreserving_add_left ..).setIntegral_image_emb
  (measurableEmbedding_addLeft m), preimage, add_mem_cancel_left]

/-- Orthogonality of characters: let ν be a translation-invariant Borel measure on V, M an open
subgroup, and χ(x+y) = χ(x)χ(y) for all x, y in V. Then ∫_M χ dν is ν(M) (read as 0 if
infinite) if χ = 1 on M, and 0 otherwise. -/
lemma setIntegral_char (ho : @IsOpen V _ M) {χ : V → ℂ} (h : ∀ x y, χ (x + y) = χ x * χ y) :
    ∫ x in M, χ x ∂ν = ite (∀ x ∈ M, χ x = 1) ↑(ν.real M) 0 := by
  split; simp [setIntegral_congr_fun ho.measurableSet ‹_›]; by_contra
  simp_all [← mul_eq_right₀ this, ← integral_const_mul, ← h, setIntegral_add_mem]

lemma setIntegral_eq_finsum [IsFiniteMeasureOnCompacts ν] [CompleteSpace X] [T2Space V] (hc :
    @IsCompact V _ M) (hL : @IsOpen V _ L) {F : V → X} (hF : ∀ x y : M, -x.1 + y ∈ L → F y = F x) :
    ∫ x in M, F x ∂ν = ν.real (L ∩ M) • ∑ᶠ q : M ⧸ L.addSubgroupOf M, F q.out := by
  have := fintypeOfIndexNeZero (hc.relIndex_ne_zero_add hL)
  rw [setIntegral_congr_fun hc.measurableSet, integral_finsetSum]
  simpa [Finset.smul_sum, hL.measurableSet] using this.sum_congr _ _
    fun q ↦ setIntegral_add_mem (indicator L fun _ ↦ F q.out) (-q.out).2
  all_goals intro x h
  exact (integrableOn_const hc.measure_ne_top).indicator (measurable_const_add _ hL.measurableSet)
  have := (@QuotientAddGroup.eq _ _ (L.addSubgroupOf M) · ⟨x, h⟩ |>.symm)
  simp_all [indicator, mem_addSubgroupOf, ← hF _ ⟨x, h⟩]
