/- GID: D5/S3/Combinatorics/Graph/Queries/PartialForwardOrderLaw
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/PartialForwardOrderLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Partial observations of binary forward orders have a common positive likelihood. -/

import D5.S3.Combinatorics.Graph.Queries.FixedNeighborOrder

/-! A single observed slot determines the whole order of two distinct forward choices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw

open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open D5.S3.Combinatorics.Graph.Queries.FixedNeighborOrder (uniform_coordinate_cylinder)
open scoped ENNReal BigOperators

/-- A candidate table agrees with every observed forward slot. -/
def Matches {P V : Type*} (choices : P → Bool → V) (observed : P → Bool → Option V)
    (f : P → Equiv.Perm Bool) : Prop :=
  ∀ p b v, observed p b = some v → choices p (f p b) = v

/-- Every observed value is available, and opposite slots cannot name the same value. -/
def Compatible {P V : Type*} (choices : P → Bool → V)
    (observed : P → Bool → Option V) : Prop :=
  (∀ p b v, observed p b = some v → v ∈ Set.range (choices p)) ∧
  (∀ p v, observed p false = some v → observed p true ≠ some v)

private theorem boolPerm_ext_at (σ τ : Equiv.Perm Bool) (b : Bool)
    (h : σ b = τ b) : σ = τ := by
  apply Equiv.ext
  intro i
  by_cases hi : i = b
  · exact hi ▸ h
  · have hσ : σ i ≠ σ b := fun e => hi (σ.injective e)
    have hτ : τ i ≠ σ b := by rw [h]; exact fun e => hi (τ.injective e)
    cases hs : σ b <;> cases hs' : σ i <;> cases ht' : τ i <;> simp_all

private theorem local_order_exists {V : Type*} (choices : Bool → V) (o : Bool → Option V)
    (h : ∀ b v, o b = some v → v ∈ Set.range choices)
    (hSep : ∀ v, o false = some v → o true ≠ some v) :
    ∃ f : Equiv.Perm Bool, ∀ b v, o b = some v → choices (f b) = v := by
  cases h0 : o false with
  | none =>
    cases h1 : o true with
    | none =>
      refine ⟨1, ?_⟩
      intro b v hb
      cases b <;> simp [h0, h1] at hb
    | some v =>
      obtain ⟨i, hi⟩ := h _ _ h1
      refine ⟨Equiv.swap true i, ?_⟩
      intro b w hw
      cases b with
      | false => simp [h0] at hw
      | true =>
        have hwv := Option.some.inj (h1.symm.trans hw)
        rw [Equiv.swap_apply_left, hi, hwv]
  | some v =>
    obtain ⟨i, hi⟩ := h _ _ h0
    refine ⟨Equiv.swap false i, ?_⟩
    intro b w hw
    cases b with
    | false =>
      have hwv := Option.some.inj (h0.symm.trans hw)
      rw [Equiv.swap_apply_left, hi, hwv]
    | true =>
      obtain ⟨j, hj⟩ := h _ _ hw
      have hij : i ≠ j := by
        rintro rfl
        exact hSep v h0 (hw.trans (congrArg some (hj.symm.trans hi)))
      have hbit : Equiv.swap false i true = j := by
        cases i <;> cases j
        · exact (hij rfl).elim
        · decide
        · decide
        · exact (hij rfl).elim
      rw [hbit, hj]

private theorem exists_matches_iff {P V : Type*} (choices : P → Bool → V)
    (hChoice : ∀ p, Function.Injective (choices p)) (observed : P → Bool → Option V) :
    (∃ f, Matches choices observed f) ↔ Compatible choices observed := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun p b v h => ⟨f p b, hf p b v h⟩, ?_⟩
    intro p v h0 h1
    exact (by decide : false ≠ true) ((f p).injective
      (hChoice p ((hf p false v h0).trans (hf p true v h1).symm)))
  · rintro ⟨h, hSep⟩
    choose f hf using (fun p => local_order_exists (choices p) (observed p) (h p) (hSep p))
    exact ⟨f, hf⟩

private theorem mass_of_matches {P V : Type*} [Fintype P] [DecidableEq P]
    (choices : P → Bool → V) (hChoice : ∀ p, Function.Injective (choices p))
    (observed : P → Bool → Option V)
    (s : Finset P) (hS : ∀ p, p ∈ s ↔ ∃ b v, observed p b = some v)
    (ref : P → Equiv.Perm Bool)
    (hRef : Matches choices observed ref) :
    (uniformPmf (P → Equiv.Perm Bool)).toOuterMeasure
      {f | Matches choices observed f} =
      ((2 ^ s.card : ℕ) : ℝ≥0∞)⁻¹ := by
  have hEvent : {f : P → Equiv.Perm Bool | Matches choices observed f} =
      {f | ∀ p : s, f p = ref p} := by
    ext f
    constructor
    · intro h p
      obtain ⟨b, v, hb⟩ := (hS p.1).mp p.2
      exact boolPerm_ext_at _ _ b (hChoice p.1 ((h p.1 b v hb).trans (hRef p.1 b v hb).symm))
    · intro h p b v hb
      have hp : p ∈ s := (hS p).mpr ⟨b, v, hb⟩
      exact (h ⟨p, hp⟩).symm ▸ hRef p b v hb
  rw [hEvent, uniform_coordinate_cylinder (fun _ : P => Equiv.Perm Bool) s (fun p => ref p)]
  have hCard : Fintype.card (Equiv.Perm Bool) = 2 := by rw [Fintype.card_perm]; decide
  simp [hCard]

attribute [local instance] Classical.propDecidable

/-- The observation costs one independent factor of one half per position it touches. -/
theorem partial_forward_order_likelihood {P V : Type*} [Fintype P] [DecidableEq P]
    (choices : P → Bool → V) (hChoice : ∀ p, Function.Injective (choices p))
    (observed : P → Bool → Option V)
    (s : Finset P) (hS : ∀ p, p ∈ s ↔ ∃ b v, observed p b = some v) :
    let observedCount := s.card
    (uniformPmf (P → Equiv.Perm Bool)).toOuterMeasure {f | Matches choices observed f} =
      if Compatible choices observed then ((2 ^ observedCount : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  classical
  dsimp only
  by_cases h : Compatible choices observed
  · obtain ⟨ref, hRef⟩ := (exists_matches_iff choices hChoice observed).mpr h
    rw [ite_eq_left h]
    exact mass_of_matches choices hChoice observed s hS ref hRef
  · have hEmpty : {f | Matches choices observed f} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun f hf =>
        h ((exists_matches_iff choices hChoice observed).mp ⟨f, hf⟩)
    rw [ite_eq_right h, hEmpty, MeasureTheory.measure_empty]

private def compatibleWorlds {P V W : Type*} (choices : W → P → Bool → V)
    (observed : P → Bool → Option V) : Set W :=
  {w | Compatible (choices w) observed}

/-- Conditioning on a positive observation restricts the world prior to compatible worlds. -/
theorem partial_forward_order_posterior {P V W : Type*} [Fintype P] [DecidableEq P]
    (π : PMF W) (choices : W → P → Bool → V)
    (hChoice : ∀ w p, Function.Injective (choices w p))
    (observed : P → Bool → Option V)
    (s : Finset P) (hS : ∀ p, p ∈ s ↔ ∃ b v, observed p b = some v) :
    let Ω := P → Equiv.Perm Bool
    let μ : PMF (W × Ω) := π.bind fun w => (uniformPmf Ω).map (Prod.mk w)
    let H : Set (W × Ω) := {x | Matches (choices x.1) observed x.2}
    let feasible := compatibleWorlds choices observed
    μ.toOuterMeasure H ≠ 0 →
      ∀ B : Set W, μ.toOuterMeasure (H ∩ Prod.fst ⁻¹' B) / μ.toOuterMeasure H =
        π.toOuterMeasure (feasible ∩ B) / π.toOuterMeasure feasible := by
  classical
  intro Ω μ H feasible hPositive B
  let c : ℝ≥0∞ := ((2 ^ s.card : ℕ) : ℝ≥0∞)⁻¹
  have hc : c ≠ 0 := ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hct : c ≠ ⊤ := ENNReal.inv_ne_top.mpr
    (Nat.cast_ne_zero.mpr (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)))
  have hMass (B : Set W) :
      μ.toOuterMeasure (H ∩ Prod.fst ⁻¹' B) = π.toOuterMeasure (feasible ∩ B) * c := by
    change (π.bind fun w => (uniformPmf Ω).map (Prod.mk w)).toOuterMeasure _ = _
    rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro w
    rw [PMF.toOuterMeasure_map_apply]
    by_cases hB : w ∈ B
    · have he : Prod.mk w ⁻¹' (H ∩ Prod.fst ⁻¹' B) =
          {f | Matches (choices w) observed f} := by
        ext f
        change (Matches (choices w) observed f ∧ w ∈ B) ↔ Matches (choices w) observed f
        exact and_iff_left hB
      rw [he, partial_forward_order_likelihood (choices w) (hChoice w) observed s hS]
      by_cases hFeasible : Compatible (choices w) observed
      · rw [Set.indicator_of_mem (show w ∈ feasible ∩ B from ⟨hFeasible, hB⟩),
          ite_eq_left hFeasible]
      · rw [Set.indicator_of_notMem (fun h : w ∈ feasible ∩ B => hFeasible h.1),
          ite_eq_right hFeasible, zero_mul, mul_zero]
    · have he : Prod.mk w ⁻¹' (H ∩ Prod.fst ⁻¹' B) = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun _ h => hB h.2)
      rw [he, MeasureTheory.measure_empty, mul_zero,
        Set.indicator_of_notMem (fun h : w ∈ feasible ∩ B => hB h.2), zero_mul]
  have hx : μ.toOuterMeasure H = π.toOuterMeasure feasible * c := by
    simpa only [Set.preimage_univ, Set.inter_univ] using hMass Set.univ
  rw [hMass B, hx, ENNReal.mul_div_mul_right _ _ hc hct]

end D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw
