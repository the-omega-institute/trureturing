/- GID: D5/S3/Combinatorics/Graph/LinearForests/AlternatingSuccessorSetBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/AlternatingSuccessorSetBound
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: The mass of a set of successor labels is bounded by its size and the color inventory. -/

import D5.S3.Combinatorics.Graph.LinearForests.AlternatingConnectorLaw
import Mathlib.Data.Set.Card

/-! A finite set of possible successors in a uniformly sampled compatible cycle. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Combinatorics.Graph.LinearForests
open CompatibleCycleInventory AlternatingConnectorLaw
open scoped ENNReal

namespace D5.S3.Combinatorics.Graph.LinearForests.AlternatingSuccessorSetBound

variable {C : Type*} [Finite C]

omit [Finite C] in
private theorem side_delete (s : C → Bool) (y : C) (a : Bool) :
    Nat.card (Side (fun z : {z : C // z ≠ y} => s z.1) a) =
      Nat.card (Side s a) - if s y = a then 1 else 0 := by
  classical
  let X : Set C := {z | s z = a}
  let e : Side (fun z : {z : C // z ≠ y} => s z.1) a ≃ ↥(X \ {y}) :=
    { toFun := fun z => ⟨z.1.1, z.2, z.1.2⟩
      invFun := fun z => ⟨⟨z.1, z.2.2⟩, z.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  change (X \ {y}).ncard = X.ncard - if s y = a then 1 else 0
  by_cases hy : s y = a
  · rw [ite_eq_left hy]
    exact Set.ncard_sdiff_singleton_of_mem (show y ∈ X from hy)
  · rw [ite_eq_right hy, Nat.sub_zero]
    congr 1
    ext x
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, fun he => hy ((Set.mem_singleton_iff.mp he) ▸ h)⟩

omit [Finite C] in
private theorem side_contract (s : C → Bool) (x y : C) (a : Bool) :
    Nat.card (Side (contractedSource s x y) a) =
      Nat.card (Side s a) - if s y = a then 1 else 0 := by
  classical
  let σ := Equiv.swap x y
  have hσx : σ x = y := Equiv.swap_apply_left x y
  have hσy : σ y = x := Equiv.swap_apply_right x y
  have hcolor (z : C) (hz : z ≠ x) : s (σ z) = contractedSource s x y ⟨z, hz⟩ := by
    by_cases hy : z = y
    · subst z
      simp [hσy, contractedSource]
    · simp [σ, Equiv.swap_apply_of_ne_of_ne hz hy, contractedSource, hy]
  let e : Side (contractedSource s x y) a ≃ Side (fun z : {z : C // z ≠ y} => s z.1) a :=
    { toFun := fun z =>
        ⟨⟨σ z.1.1, fun he => z.1.2 (σ.injective (he.trans hσx.symm))⟩,
          (hcolor _ _).trans z.2⟩
      invFun := fun z =>
        ⟨⟨σ.symm z.1.1, fun he =>
          z.1.2 ((σ.apply_symm_apply z.1.1).symm.trans ((congrArg σ he).trans hσx))⟩,
          by rw [← hcolor, σ.apply_symm_apply]; exact z.2⟩
      left_inv := fun z => Subtype.ext (Subtype.ext (σ.symm_apply_apply z.1.1))
      right_inv := fun z => Subtype.ext (Subtype.ext (σ.apply_symm_apply z.1.1)) }
  exact (Nat.card_congr e).trans (side_delete s y a)

private theorem cross_contract_le (s d : C → Bool) (x y : C) (hy : s y = d x) :
    inventory (contractedSource s x y) (fun z => d z.1) false true ≤
      inventory s d false true := by
  classical
  let I := {z : {z : C // z ≠ x} // contractedSource s x y z = false ∧ d z.1 = true}
  let J := {z : C // s z = false ∧ d z = true}
  change Nat.card I ≤ Nat.card J
  let move := y ≠ x ∧ s x ≠ s y
  let f : I → J := fun z =>
    if hm : z.1.1 = y ∧ move then
      ⟨x, by
        have hxs : s x = false := by
          simpa [contractedSource, hm.1] using z.2.1
        have hyt : s y = true := by
          cases h : s y
          · exact (hm.2.2 (hxs.trans h.symm)).elim
          · rfl
        exact ⟨hxs, hy.symm.trans hyt⟩⟩
    else ⟨z.1.1, by
      have hs : s z.1.1 = false := by
        by_cases he : z.1.1 = y
        · have heq : s x = s y := not_not.mp fun h => hm ⟨he, he ▸ z.1.2, h⟩
          simpa [contractedSource, he, heq] using z.2.1
        · simpa [contractedSource, he] using z.2.1
      exact ⟨hs, z.2.2⟩⟩
  apply Nat.card_le_card_of_injective f
  intro z z' heq
  apply Subtype.ext
  apply Subtype.ext
  have hv := congrArg Subtype.val heq
  dsimp [f] at hv
  split at hv <;> split at hv
  · exact ‹z.1.1 = y ∧ move›.1.trans ‹z'.1.1 = y ∧ move›.1.symm
  · exact (z'.1.2 hv.symm).elim
  · exact (z.1.2 hv).elim
  · exact hv

private theorem mixed_count (s d : C → Bool)
    (hbal : inventory s d false true = inventory s d true false)
    (h₀ : 0 < Nat.card (Side s false)) (h₁ : 0 < Nat.card (Side s true)) :
    contractedInventoryCount s d =
      inventory s d false true * (Nat.card (Side s false) - 1).factorial *
        (Nat.card (Side s true) - 1).factorial := by
  classical
  by_cases hp : 0 < inventory s d false true
  · simp [contractedInventoryCount, hp]
  · have hz : inventory s d false true = 0 := Nat.eq_zero_of_not_pos hp
    have he (z : C) : d z = s z := by
      cases hs : s z <;> cases hd : d z
      · rfl
      · exact (inventory_zero s d false true hz z hs hd).elim
      · exact (inventory_zero s d true false (hbal.symm.trans hz) z hs hd).elim
      · rfl
    have hc (b : Bool) : inventory s d b b = Nat.card (Side s b) :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun z => by simp [he z]))
    simp [contractedInventoryCount, hz, hc, Nat.ne_of_gt h₀, Nat.ne_of_gt h₁]

private theorem mass_count_bound (s d : C → Bool) (x y : C) (hxy : y ≠ x)
    (hy : s y = d x) (hcolors : ∀ c, 2 ≤ Nat.card (Side s c)) (σ : Compatible s d) :
    let B := {z : C // z ≠ x}
    (Nat.card (Side s (d x)) - 1) *
      contractedInventoryCount (contractedSource s x y) (fun z : B => d z.1)
      ≤ Nat.card (Compatible s d) := by
  classical
  intro B
  let u := contractedSource s x y
  let v : B → Bool := fun z => d z.1
  have hAmbient := balance_of_compatible s d σ
  have hS (c : Bool) : Nat.card (Side u c) =
      Nat.card (Side s c) - if s y = c then 1 else 0 := side_contract s x y c
  have hContracted : inventory u v false true = inventory u v true false :=
    contracted_balance_at s d x y hxy hy σ
  have hPos (c : Bool) : 0 < Nat.card (Side u c) := by
    rw [hS]
    have := hcolors c
    split <;> omega
  let : Nonempty C := ⟨x⟩
  have hC : Nat.card C ≠ 0 := Nat.ne_of_gt Nat.card_pos
  have hTotal : Nat.card (Compatible s d) = contractedInventoryCount s d := by
    simpa [contractedInventoryCount, hC] using compatible_cycle_card s d hAmbient
  rw [hTotal, mixed_count s d hAmbient
      (Nat.lt_of_lt_of_le (by decide) (hcolors false))
      (Nat.lt_of_lt_of_le (by decide) (hcolors true)),
    mixed_count u v hContracted (hPos false) (hPos true)]
  have hi : inventory u v false true ≤ inventory s d false true :=
    cross_contract_le s d x y hy
  refine (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hi))).trans ?_
  apply le_of_eq
  have hDrop : Nat.card (Side u (d x)) = Nat.card (Side s (d x)) - 1 := by
    simpa [hy] using hS (d x)
  have hFactorial : (Nat.card (Side s (d x)) - 1) *
      (Nat.card (Side u (d x)) - 1).factorial =
      (Nat.card (Side s (d x)) - 1).factorial := by
    rw [hDrop, Nat.mul_factorial_pred]
    have := hcolors (d x)
    omega
  cases hx : d x
  · have hKeep : Nat.card (Side u true) = Nat.card (Side s true) := by
      simpa [hy, hx] using hS true
    rw [hKeep]
    have h := hFactorial
    rw [hx] at h
    rw [← h]
    ac_rfl
  · have hKeep : Nat.card (Side u false) = Nat.card (Side s false) := by
      simpa [hy, hx] using hS false
    rw [hKeep]
    have h := hFactorial
    rw [hx] at h
    rw [← h]
    ac_rfl

private theorem successor_mass_le (s d : C → Bool) (x y : C) (hxy : y ≠ x)
    (hcolors : ∀ c, 2 ≤ Nat.card (Side s c))
    (μ : PMF (Compatible s d)) (hμ : ∀ σ, μ σ = (Nat.card (Compatible s d) : ℝ≥0∞)⁻¹) :
    μ.toOuterMeasure {σ | σ.1 x = y} ≤
      ((Nat.card (Side s (d x)) - 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  rw [connector_mass s d x y hxy μ hμ]
  split
  · rename_i hy
    obtain ⟨σ, _⟩ := μ.support_nonempty
    let : Nonempty (Compatible s d) := ⟨σ⟩
    let M := Nat.card (Side s (d x)) - 1
    have hM : M ≠ 0 := by
      have := hcolors (d x)
      dsimp [M]
      omega
    have hK : (Nat.card (Compatible s d) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
    let K := Nat.card (Compatible s d)
    let L := contractedInventoryCount (contractedSource s x y) (fun z => d z.1)
    change (L : ℝ≥0∞) / K ≤ (M : ℝ≥0∞)⁻¹
    rw [← one_div, ENNReal.le_div_iff_mul_le (.inl (Nat.cast_ne_zero.mpr hM))
      (.inl (ENNReal.natCast_ne_top _))]
    calc
      ((L : ℝ≥0∞) / K) * M = ((M * L : ℕ) : ℝ≥0∞) / K := by
        rw [Nat.cast_mul]
        simp only [div_eq_mul_inv]
        ac_rfl
      _ ≤ 1 := by
        rw [ENNReal.div_le_iff hK (ENNReal.natCast_ne_top _), one_mul]
        exact_mod_cast mass_count_bound s d x y hxy hy hcolors σ
  · exact zero_le

/-- Bounding each prescribed connector and summing over the target set bounds its mass. -/
theorem successor_set_mass_le (s d : C → Bool) (x : C) (targets : Finset C)
    (not_self : x ∉ targets) (hcolors : ∀ c, 2 ≤ Nat.card (Side s c))
    (μ : PMF (Compatible s d)) (hμ : ∀ σ, μ σ = (Nat.card (Compatible s d) : ℝ≥0∞)⁻¹) :
    let choices := Nat.card (Side s (d x)) - 1
    let targetCount := targets.card
    μ.toOuterMeasure {σ | σ.1 x ∈ targets} ≤ (targetCount : ℝ≥0∞) / choices := by
  classical
  intro choices
  let A (y : C) : Set (Compatible s d) := {σ | σ.1 x = y}
  have he : {σ : Compatible s d | σ.1 x ∈ targets} = ⋃ y ∈ targets, A y := by
    ext σ
    simp [A]
  rw [he]
  calc
    _ ≤ ∑ y ∈ targets, μ.toOuterMeasure (A y) := MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ targets, (choices : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro y hy
      refine successor_mass_le s d x y (fun h => not_self (h ▸ hy)) hcolors μ hμ
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

end D5.S3.Combinatorics.Graph.LinearForests.AlternatingSuccessorSetBound
