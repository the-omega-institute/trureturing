/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalGoodRecordCount
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalGoodRecordCount
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: Bounded actual good records count original parameter and endpoint incidences. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalRecords
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Count actual good incidences by their ten bounded integer coordinates.
The original parameter is reconstructed from the anchor and physical basis;
it is not an extra free choice in a record fiber. -/

open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private def recordCoordinateBox (J₁ J₂ : ℝ) : Finset Coordinate :=
  (Finset.Icc (-⌊J₁⌋) ⌊J₁⌋) ×ˢ (Finset.Icc (-⌊J₂⌋) ⌊J₂⌋)

private theorem mem_recordCoordinateBox {J₁ J₂ : ℝ} {z : Coordinate}
    (hz : CoordinateBound J₁ J₂ z) : z ∈ recordCoordinateBox J₁ J₂ := by
  have hi : z.1 ≤ ⌊J₁⌋ := Int.le_floor.mpr ((le_abs_self _).trans hz.1)
  have hi' : -z.1 ≤ ⌊J₁⌋ := Int.le_floor.mpr (by
    simpa only [Int.cast_neg] using (neg_le_abs (z.1 : ℝ)).trans hz.1)
  have hj : z.2 ≤ ⌊J₂⌋ := Int.le_floor.mpr ((le_abs_self _).trans hz.2)
  have hj' : -z.2 ≤ ⌊J₂⌋ := Int.le_floor.mpr (by
    simpa only [Int.cast_neg] using (neg_le_abs (z.2 : ℝ)).trans hz.2)
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega, hi⟩, Finset.mem_Icc.mpr ⟨by omega, hj⟩⟩

private theorem recordCoordinateBox_card {J₁ J₂ : ℝ}
    (h₁ : 1 ≤ J₁) (h₂ : 1 ≤ J₂) :
    ((recordCoordinateBox J₁ J₂).card : ℝ) ≤ 9 * J₁ * J₂ := by
  have hinterval (J : ℝ) (hJ : 1 ≤ J) :
      ((Finset.Icc (-⌊J⌋) ⌊J⌋).card : ℝ) ≤ 3 * J := by
    have hN : 0 ≤ ⌊J⌋ := Int.floor_nonneg.mpr (by linarith)
    have he := Int.card_Icc_of_le (a := -⌊J⌋) (b := ⌊J⌋) (by omega)
    have heR : ((Finset.Icc (-⌊J⌋) ⌊J⌋).card : ℝ) =
        (⌊J⌋ : ℝ) + 1 - (-⌊J⌋ : ℤ) := by exact_mod_cast he
    rw [heR]
    push_cast
    linarith [Int.floor_le J]
  rw [recordCoordinateBox, Finset.card_product, Nat.cast_mul]
  calc
    _ ≤ (3 * J₁) * (3 * J₂) :=
      mul_le_mul (hinterval J₁ h₁) (hinterval J₂ h₂)
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

private def actualRecordKey (q : Coordinate → Coordinate)
    (u : Coordinate × Endpoint × Endpoint) : Coordinate × Endpoint × Endpoint :=
  (q u.1, u.2.1, u.2.2)

/-- A fixed bounded coordinate chart has uniformly few actual good incidences.
The finite set T contains the original integer parameter (w,t) and two actual
ordered endpoint pairs; the physical bases are allowed to vary with (w,t).
The original anchor identity proves that one physical realization cannot hide
several different original parameters in the same record fiber. -/
theorem actual_bounded_good_record_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y J₁ J₂ : ℝ)
      (a₁ a₂ : ZMod (p^3)) (q : Coordinate → Coordinate)
      (RV : Coordinate → Coordinate × Coordinate)
      (T : Finset (Coordinate × Endpoint × Endpoint)),
      0 < X → X ≤ Y → 3*Y < (p : ℝ)^2 →
      1 ≤ J₁ → 1 ≤ J₂ → IsUnit a₁ → IsUnit a₂ →
      (∀ u ∈ T, GoodRecordRealization p X Y a₁ a₂
        (q u.1) u.2.1 u.2.2 (RV u.1)) →
      (∀ u ∈ T, physical (RV u.1).1 (RV u.1).2 (q u.1) = -u.1) →
      (∀ u ∈ T, CoordinateBound J₁ J₂ (q u.1) ∧
        CoordinateBound J₁ J₂ u.2.1.1 ∧ CoordinateBound J₁ J₂ u.2.1.2 ∧
        CoordinateBound J₁ J₂ u.2.2.1 ∧ CoordinateBound J₁ J₂ u.2.2.2) →
      (T.card : ℝ) ≤ C*(p : ℝ)^ε*(9*J₁*J₂)^5 := by
  classical
  obtain ⟨C, hC, hrealizations⟩ := actual_good_record_realizations_subpower ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp X Y J₁ J₂ a₁ a₂ q RV T hX hXY hsmall h₁ h₂ ha₁ ha₂
    hgood hanchor hbounds
  let key := actualRecordKey q
  have hfiber (r : Coordinate × Endpoint × Endpoint) :
      ((T.filter (fun u => key u = r)).card : ℝ) ≤ C*(p : ℝ)^ε := by
    let f := fun u : Coordinate × Endpoint × Endpoint => RV u.1
    let fiber := T.filter (fun u => key u = r)
    obtain ⟨hfinite, hcard⟩ := hrealizations p hp X Y a₁ a₂ r.1 r.2.1 r.2.2
      hX hXY hsmall ha₁ ha₂
    have hinj : Set.InjOn f (fiber : Set _) := by
      intro u hu v hv huv
      obtain ⟨huT, huk⟩ := Finset.mem_filter.mp hu
      obtain ⟨hvT, hvk⟩ := Finset.mem_filter.mp hv
      have hkey : key u = key v := huk.trans hvk.symm
      have hq : q u.1 = q v.1 := congrArg Prod.fst hkey
      have hphys : physical (RV u.1).1 (RV u.1).2 (q u.1) =
          physical (RV v.1).1 (RV v.1).2 (q v.1) :=
        congrArg₂ (fun b z => physical b.1 b.2 z) huv hq
      have hwt : u.1 = v.1 := neg_injective
        ((hanchor u huT).symm.trans (hphys.trans (hanchor v hvT)))
      have he : u.2 = v.2 := by
        simpa only [key, actualRecordKey] using congrArg Prod.snd hkey
      exact Prod.ext hwt he
    have hsub : (fiber.image f : Set _) ⊆
        {b | GoodRecordRealization p X Y a₁ a₂ r.1 r.2.1 r.2.2 b} := by
      intro b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨huT, huk⟩ := Finset.mem_filter.mp hu
      have hg := hgood u huT
      change GoodRecordRealization p X Y a₁ a₂
        (key u).1 (key u).2.1 (key u).2.2 (f u) at hg
      change GoodRecordRealization p X Y a₁ a₂ r.1 r.2.1 r.2.2 (f u)
      simpa only [huk] using hg
    have hn : fiber.card ≤
        {b | GoodRecordRealization p X Y a₁ a₂ r.1 r.2.1 r.2.2 b}.ncard := by
      simpa only [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj] using
        Set.ncard_le_ncard hsub hfinite
    exact (show (fiber.card : ℝ) ≤ _ by exact_mod_cast hn).trans hcard
  let box := recordCoordinateBox J₁ J₂
  let records := box ×ˢ ((box ×ˢ box) ×ˢ (box ×ˢ box))
  have hsub : T.image key ⊆ records := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hq, hx, hy, hx', hy'⟩ := hbounds u hu
    exact Finset.mem_product.mpr ⟨mem_recordCoordinateBox hq,
      Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨mem_recordCoordinateBox hx, mem_recordCoordinateBox hy⟩,
          Finset.mem_product.mpr ⟨mem_recordCoordinateBox hx', mem_recordCoordinateBox hy'⟩⟩⟩
  have hrecords : ((T.image key).card : ℝ) ≤ (9*J₁*J₂)^5 := by
    have he : (records.card : ℝ) = (box.card : ℝ)^5 := by
      simp only [records, Finset.card_product, Nat.cast_mul]
      ring
    calc
      _ ≤ (records.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = (box.card : ℝ)^5 := he
      _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) (recordCoordinateBox_card h₁ h₂) 5
  calc
    (T.card : ℝ) = ∑ r ∈ T.image key, ((T.filter (fun u => key u = r)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image key T
    _ ≤ ∑ _r ∈ T.image key, C*(p : ℝ)^ε := Finset.sum_le_sum fun r _ => hfiber r
    _ = ((T.image key).card : ℝ)*(C*(p : ℝ)^ε) := by simp
    _ ≤ (9*J₁*J₂)^5*(C*(p : ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hrecords (by positivity)
    _ = C*(p : ℝ)^ε*(9*J₁*J₂)^5 := by ring

end
end D5.S3.Arith.CharacterSums.Original
