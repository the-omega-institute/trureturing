/- GID: D5/S3/Arith/Robin/PriceRecord/ActualRecordHigherInventoryAllLog
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualRecordHigherInventoryAllLog
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Uniform all-real-log convergence of the full actual higher coordinate mismatch. -/

import D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder
import D5.S3.Arith.Robin.PriceRecord.ActualHigherMassCoercivity
import D5.S3.Arith.Robin.PriceRecord.CanonicalRecordPowerDefect

/-! Uniform higher-coordinate convergence at the original strict-record clock. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherInventoryAllLog

open Finset Filter Real
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask (actualDefect)
open D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual (completeFirstLayerLoss)
open D5.S3.Arith.Robin.PriceRecord.CompleteHigherInventoryDuality
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.Robin.ActualTwoPriceDefect (strictInteger)
open D5.S3.Arith.Robin.PriceRecord.CanonicalRecordPowerDefect (higherInventoryMismatch)
open D5.S3.Arith.Robin.PriceRecord.ActualHigherMassCoercivity
open D5.S3.Arith.Robin.PriceRecord.ActualHigherMassResponse
open D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder
  (actual_record_all_real_log_residual)

private theorem finite_inventory_l1 {ι : Type*} (S : Finset ι)
    (b w : ι → ℝ) (i : ι → Bool) (hw : ∀ c ∈ S, 0 ≤ w c)
    {«λ» t : ℝ} (ht : 0 < t) :
    let F := fun η => ∑ c ∈ S, max (b c - η * w c) 0
    let h := fun η => ∑ c ∈ S, if 0 < b c - η * w c then w c else 0
    let H := ∑ c ∈ S, if i c then w c else 0
    let B := ∑ c ∈ S, if i c then b c else 0
    let R := F «λ» - B + «λ» * H
    (∑ c ∈ S, if i c then
      (if 0 < b c - «λ» * w c then 0 else w c)
      else (if 0 < b c - «λ» * w c then w c else 0)) ≤
      R / t + h («λ» - t) - h («λ» + t) := by
  classical
  dsimp only
  have hpoint (c : ι) (hc : c ∈ S) :
      (if i c then (if 0 < b c - «λ» * w c then 0 else w c)
        else (if 0 < b c - «λ» * w c then w c else 0)) ≤
      (max (b c - «λ» * w c) 0 - (if i c then b c else 0) +
        «λ» * (if i c then w c else 0)) / t +
        (if 0 < b c - («λ» - t) * w c then w c else 0) -
        (if 0 < b c - («λ» + t) * w c then w c else 0) := by
    have hd := finite_dual_abs ({c} : Finset ι) b w i
      (by
        intro d hd
        simpa only [mem_singleton.mp hd] using hw c hc)
      («λ» := «λ») (t := t) ht
    simp only [sum_singleton] at hd
    have habs :
        |(if i c then w c else 0) -
          (if 0 < b c - «λ» * w c then w c else 0)| =
        (if i c then (if 0 < b c - «λ» * w c then 0 else w c)
          else (if 0 < b c - «λ» * w c then w c else 0)) := by
      cases hi : i c <;> by_cases hq : 0 < b c - «λ» * w c <;>
        simp [hq, abs_of_nonneg (hw c hc)]
    rw [habs] at hd
    exact hd
  have hh := sum_le_sum hpoint
  simpa only [sum_add_distrib, sum_sub_distrib, ← sum_div, ← mul_sum] using hh

/-- The auxiliary low-price canonical set bounds only canonical occupancy;
the full actual set is included independently, with no support or exponent cap. -/
private theorem actual_inventory_dual_estimate {X s : ℝ} (hX : exp 2 ≤ X)
    {n : ℕ} (hn : 1 ≤ n) (hs : 0 < s) (hs2 : s ≤ 1 / 2) :
    higherInventoryMismatch X n ≤
      (actualDefect X n - completeFirstLayerLoss X n) * X * log X / s +
        400 * s * sqrt X * log X + 400 * log X ^ 2 := by
  classical
  have hX0 : 0 < X := (exp_pos 2).trans_le hX
  have hL : 2 ≤ log X := (le_log_iff_exp_le hX0).mpr hX
  have hX1 : 1 < X := (log_pos_iff hX0.le).mp (by linarith : 0 < log X)
  let lam := referencePrice X
  let t := s * lam
  have hlam : 0 < lam := one_div_pos.mpr (mul_pos hX0 (by linarith : 0 < log X))
  have ht : 0 < t := mul_pos hs hlam
  have ht_le : t ≤ (1 / 2 : ℝ) * lam := mul_le_mul_of_nonneg_right hs2 hlam.le
  have hm : 0 < lam - t := by linarith
  have hp : 0 < lam + t := add_pos hlam ht
  let S := coordinates n ∪ coordinates (strictInteger (lam - t))
  have hprime (c : ℕ × ℕ) (hc : c ∈ S) : c.1.Prime ∧ 2 ≤ c.2 := by
    rcases mem_union.mp hc with hc | hc <;>
      exact ⟨(mem_coordinates.mp hc).1, (mem_coordinates.mp hc).2.1⟩
  have hnS : coordinates n ⊆ S := subset_union_left
  have hmS : coordinates (strictInteger (lam - t)) ⊆ S := subset_union_right
  have hbS : coordinates (strictInteger lam) ⊆ S :=
    (canonical_coordinates_antitone hm hlam (by linarith)).trans hmS
  have hpS : coordinates (strictInteger (lam + t)) ⊆ S :=
    (canonical_coordinates_antitone hm hp (by linarith)).trans hmS
  let i := fun c : ℕ × ℕ => decide (c ∈ coordinates n)
  have hH : (∑ c ∈ S, if i c then coordinateWeight c else 0) = higherMass n := by
    simp only [i, decide_eq_true_eq]
    rw [← sum_filter]
    have he : S.filter (fun c => c ∈ coordinates n) = coordinates n := by
      ext c
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hnS h, h⟩⟩
    rw [he, higherMass_eq_coordinate_sum]
    rfl
  have hB : (∑ c ∈ S, if i c then coordinateGain c else 0) = inventoryGain n := by
    simp only [i, decide_eq_true_eq]
    rw [← sum_filter]
    have he : S.filter (fun c => c ∈ coordinates n) = coordinates n := by
      ext c
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hnS h, h⟩⟩
    rw [he]
    rfl
  have hD : (∑ c ∈ S, if i c then
      (if 0 < coordinateGain c - lam * coordinateWeight c then 0 else coordinateWeight c)
      else (if 0 < coordinateGain c - lam * coordinateWeight c then coordinateWeight c else 0)) =
      higherInventoryMismatch X n := by
    let C := coordinates (strictInteger lam)
    let M := (coordinates n \ C) ∪ (C \ coordinates n)
    have hMS : M ⊆ S := by
      intro c hc
      rcases mem_union.mp hc with hc | hc
      · exact hnS (mem_sdiff.mp hc).1
      · exact hbS (mem_sdiff.mp hc).1
    have hcentral (c : ℕ × ℕ) (hc : c ∈ S) :
        (0 < coordinateGain c - lam * coordinateWeight c) ↔ c ∈ C := by
      constructor
      · intro hpos
        exact (canonical_mem hlam).mpr ⟨(hprime c hc).1, (hprime c hc).2,
          (positive_coordinate (hprime c hc).1).mp hpos⟩
      · intro hmem
        exact (positive_coordinate (hprime c hc).1).mpr
          ((canonical_mem hlam).mp hmem).2.2
    have hzero (c : ℕ × ℕ) (hcS : c ∈ S) (hcM : c ∉ M) :
        (if i c then
          (if 0 < coordinateGain c - lam * coordinateWeight c then 0 else coordinateWeight c)
          else (if 0 < coordinateGain c - lam * coordinateWeight c then coordinateWeight c else 0)) =
          0 := by
      simp only [i, decide_eq_true_eq, hcentral c hcS]
      by_cases ha : c ∈ coordinates n
      · by_cases hb : c ∈ C
        · simp only [ite_eq_left ha, ite_eq_left hb]
        · exact (hcM (mem_union_left _ (mem_sdiff.mpr ⟨ha, hb⟩))).elim
      · by_cases hb : c ∈ C
        · exact (hcM (mem_union_right _ (mem_sdiff.mpr ⟨hb, ha⟩))).elim
        · simp only [ite_eq_right ha, ite_eq_right hb]
    rw [← sum_subset hMS hzero]
    change (∑ c ∈ M, if i c then
      (if 0 < coordinateGain c - lam * coordinateWeight c then 0 else coordinateWeight c)
      else (if 0 < coordinateGain c - lam * coordinateWeight c then coordinateWeight c else 0)) =
      ∑ c ∈ M, coordinateWeight c
    apply sum_congr rfl
    intro c hc
    simp only [i, decide_eq_true_eq, hcentral c (hMS hc)]
    rcases mem_union.mp hc with hc | hc
    · obtain ⟨ha, hb⟩ := mem_sdiff.mp hc
      simp only [ite_eq_left ha, ite_eq_right hb]
    · obtain ⟨hb, ha⟩ := mem_sdiff.mp hc
      simp only [ite_eq_right ha, ite_eq_left hb]
  have hid := literal_loss_identity hX1 hn S hprime (union_subset hbS hnS)
  have hd := finite_inventory_l1 S coordinateGain coordinateWeight i
    («λ» := lam) (t := t) (fun c hc => (hprime c hc).1.log_pos.le) ht
  change (∑ c ∈ S, if i c then
      (if 0 < coordinateGain c - lam * coordinateWeight c then 0 else coordinateWeight c)
      else (if 0 < coordinateGain c - lam * coordinateWeight c then coordinateWeight c else 0)) ≤
    (potential S lam - (∑ c ∈ S, if i c then coordinateGain c else 0) +
      lam * (∑ c ∈ S, if i c then coordinateWeight c else 0)) / t +
      strictMass S (lam - t) - strictMass S (lam + t) at hd
  rw [hD, hH, hB, strictMass_eq hm hprime hmS,
    strictMass_eq hp hprime hpS, ← hid] at hd
  have hlow : lam - t = (1 - s) * referencePrice X := by dsimp [lam, t]; ring
  have hhigh : lam + t = (1 + s) * referencePrice X := by dsimp [lam, t]; ring
  rw [hlow, hhigh] at hd
  have hresponse := (actual_higher_mass_response hX hs hs2).2
  have hden : (actualDefect X n - completeFirstLayerLoss X n) / t =
      (actualDefect X n - completeFirstLayerLoss X n) * X * log X / s := by
    dsimp [t, lam, referencePrice]
    field_simp [hs.ne', hX0.ne', (show log X ≠ 0 by linarith)]
  rw [hden] at hd
  linarith

/-- Complete higher loss controls the full weighted coordinate symmetric
difference for every original X and n, including empty higher inventories. -/
private theorem actual_complete_higher_inventory_coercivity {X : ℝ} (hX : exp 2 ≤ X)
    (n : ℕ) (hn : 1 ≤ n) :
    let R := actualDefect X n - completeFirstLayerLoss X n
    0 ≤ R ∧
    higherInventoryMismatch X n ≤
      1000 * (X ^ (3 / 4 : ℝ) * log X * sqrt R + X * log X * R + log X ^ 2) := by
  have hX0 : 0 < X := (exp_pos 2).trans_le hX
  have hL : 2 ≤ log X := (le_log_iff_exp_le hX0).mpr hX
  have hL0 : 0 < log X := by linarith
  let R := actualDefect X n - completeFirstLayerLoss X n
  have hR : 0 ≤ R := (actual_complete_higher_mass_coercivity hX n hn).1
  have hbal := balance_response (Δ := higherInventoryMismatch X n)
    (R := R) (q := sqrt X) (L := log X) hR (sqrt_pos.mpr hX0) hL0
    (fun s hs hs2 => by
      simpa only [sq_sqrt hX0.le, mul_assoc] using
        actual_inventory_dual_estimate hX hn hs hs2)
  have hpower : sqrt X * sqrt (sqrt X) = X ^ (3 / 4 : ℝ) := by
    have hinner : sqrt (sqrt X) = X ^ ((1 / 2 : ℝ) * (1 / 2)) := by
      rw [rpow_mul hX0.le (1 / 2) (1 / 2)]
      simp only [sqrt_eq_rpow]
    calc
      sqrt X * sqrt (sqrt X) = X ^ (1 / 2 : ℝ) * X ^ ((1 / 2 : ℝ) * (1 / 2)) :=
        congrArg₂ (· * ·) (sqrt_eq_rpow X) hinner
      _ = X ^ ((1 / 2 : ℝ) + (1 / 2) * (1 / 2)) := (rpow_add hX0 _ _).symm
      _ = _ := by rw [show (1 / 2 : ℝ) + (1 / 2) * (1 / 2) = 3 / 4 by norm_num]
  rw [sq_sqrt hX0.le, hpower] at hbal
  exact ⟨hR, hbal⟩


private theorem inventory_mismatch_nonneg (X : ℝ) (n : ℕ) :
    0 ≤ higherInventoryMismatch X n := by
  unfold higherInventoryMismatch coordinateWeight
  exact Finset.sum_nonneg (fun c _ => Real.log_natCast_nonneg c.1)

/- Exact normalization of the supplied finite L1 estimate. All real exponents,
   including negative ones, are handled at the positive base log X. -/
private theorem normalized_inventory_bound {X : ℝ} (hX : exp 2 ≤ X)
    (n : ℕ) (hn : 1 ≤ n) (a : ℝ) :
    let R := actualDefect X n - completeFirstLayerLoss X n
    Real.rpow (log X) a * higherInventoryMismatch X n / sqrt X ≤
      1000 * (sqrt (sqrt X * Real.rpow (log X) (2 * a + 2) * R) +
        sqrt X * Real.rpow (log X) (a + 1) * R +
        Real.rpow (log X) (a + 2) / sqrt X) := by
  have hX0 : 0 < X := (exp_pos 2).trans_le hX
  have hL : 2 ≤ log X := (le_log_iff_exp_le hX0).mpr hX
  have hL0 : 0 < log X := by linarith
  have hs : 0 < sqrt X := sqrt_pos.mpr hX0
  have hw : 0 ≤ Real.rpow (log X) a := Real.rpow_nonneg hL0.le a
  let R := actualDefect X n - completeFirstLayerLoss X n
  have hfinite : higherInventoryMismatch X n ≤
      1000 * (X ^ (3 / 4 : ℝ) * log X * sqrt R +
        X * log X * R + log X ^ 2) :=
    (actual_complete_higher_inventory_coercivity hX n hn).2
  have hlogOne : Real.rpow (log X) (a + 1) =
      Real.rpow (log X) a * log X :=
    Real.rpow_add_one hL0.ne' a
  have hlogTwo : Real.rpow (log X) (a + 2) =
      Real.rpow (log X) a * log X ^ 2 := by
    exact (Real.rpow_add hL0 a 2).trans
      (congrArg (fun w => Real.rpow (log X) a * w) (Real.rpow_two (log X)))
  have hlogSquare : Real.rpow (log X) (2 * a + 2) =
      (Real.rpow (log X) a * log X) ^ 2 := by
    calc
      _ = Real.rpow (log X) ((a + 1) * 2) := by congr 1 <;> ring
      _ = (Real.rpow (log X) (a + 1)) ^ 2 := by
        exact (Real.rpow_mul hL0.le (a + 1) 2).trans (Real.rpow_two _)
      _ = _ := by rw [hlogOne]
  have hpower : sqrt X * sqrt (sqrt X) = X ^ (3 / 4 : ℝ) := by
    have hinner : sqrt (sqrt X) = X ^ ((1 / 2 : ℝ) * (1 / 2)) := by
      rw [Real.rpow_mul hX0.le (1 / 2) (1 / 2)]
      simp only [Real.sqrt_eq_rpow]
    calc
      sqrt X * sqrt (sqrt X) =
          X ^ (1 / 2 : ℝ) * X ^ ((1 / 2 : ℝ) * (1 / 2)) :=
        congrArg₂ (· * ·) (Real.sqrt_eq_rpow X) hinner
      _ = X ^ ((1 / 2 : ℝ) + (1 / 2) * (1 / 2)) :=
        (Real.rpow_add hX0 _ _).symm
      _ = _ := by
        rw [show (1 / 2 : ℝ) + (1 / 2) * (1 / 2) = 3 / 4 by norm_num]
  have hfirst :
      Real.rpow (log X) a * (X ^ (3 / 4 : ℝ) * log X * sqrt R) / sqrt X =
        sqrt (sqrt X * Real.rpow (log X) (2 * a + 2) * R) := by
    rw [hlogSquare,
      Real.sqrt_mul
        (mul_nonneg (sqrt_nonneg X)
          (sq_nonneg (Real.rpow (log X) a * log X))) R,
      Real.sqrt_mul (sqrt_nonneg X) ((Real.rpow (log X) a * log X) ^ 2),
      Real.sqrt_sq (mul_nonneg hw hL0.le), ← hpower]
    field_simp [hs.ne']
    <;> ring
  have hsecond :
      Real.rpow (log X) a * (X * log X * R) / sqrt X =
        sqrt X * Real.rpow (log X) (a + 1) * R := by
    rw [hlogOne]
    calc
      _ = Real.rpow (log X) a * ((sqrt X) ^ 2 * log X * R) / sqrt X := by
        rw [Real.sq_sqrt hX0.le]
      _ = _ := by field_simp [hs.ne'] <;> ring
  have hthird : Real.rpow (log X) a * log X ^ 2 / sqrt X =
      Real.rpow (log X) (a + 2) / sqrt X := by
    rw [hlogTwo]
  calc
    Real.rpow (log X) a * higherInventoryMismatch X n / sqrt X ≤
        Real.rpow (log X) a *
          (1000 * (X ^ (3 / 4 : ℝ) * log X * sqrt R +
            X * log X * R + log X ^ 2)) / sqrt X :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfinite hw) hs.le
    _ = 1000 *
        (Real.rpow (log X) a * (X ^ (3 / 4 : ℝ) * log X * sqrt R) / sqrt X +
          Real.rpow (log X) a * (X * log X * R) / sqrt X +
          Real.rpow (log X) a * log X ^ 2 / sqrt X) := by ring
    _ = _ := by rw [hfirst, hsecond, hthird]

/-- One threshold, chosen before every original integer and every original
positive price, controls the full weighted higher coordinate symmetric
difference at the original clock X = log m. No support or exponent cap is
imposed on the actual inventory, and canonical occupancy remains strict. -/
theorem actual_record_all_real_log_higher_inventory :
    ∀ a : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ X0 : ℝ, 1 < X0 ∧
        ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
          (∀ k : ℕ, 0 < k → k < m →
            goldenResourceObjective mu k < goldenResourceObjective mu m) →
          X0 ≤ log (m : ℝ) →
          let X := log (m : ℝ)
          0 ≤ Real.rpow (log X) a * higherInventoryMismatch X m / sqrt X ∧
          Real.rpow (log X) a * higherInventoryMismatch X m / sqrt X < ε := by
  intro a ε hε
  let δ : ℝ := ε / 3000
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨B₁, _, hB₁⟩ := actual_record_all_real_log_residual
    (2 * a + 2) (δ ^ 2) (sq_pos_of_pos hδ)
  obtain ⟨B₂, _, hB₂⟩ := actual_record_all_real_log_residual (a + 1) δ hδ
  have htail : Tendsto
      (fun X : ℝ => Real.rpow (log X) (a + 2) / sqrt X) atTop (𝓝 0) := by
    simpa only [← Real.sqrt_eq_rpow, Real.rpow_eq_pow] using
      (_root_.isLittleO_log_rpow_rpow_atTop (a + 2)
        (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have htailSmall : ∀ᶠ X : ℝ in atTop,
      Real.rpow (log X) (a + 2) / sqrt X < δ :=
    (tendsto_order.mp htail).2 δ hδ
  obtain ⟨B₃, hB₃⟩ := eventually_atTop.mp htailSmall
  refine ⟨max 2 (max (exp 2) (max B₁ (max B₂ B₃))),
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro m hm mu hmu hrecord hlarge
  rcases max_le_iff.mp hlarge with ⟨hclock2, hlarge⟩
  rcases max_le_iff.mp hlarge with ⟨hX, hlarge⟩
  rcases max_le_iff.mp hlarge with ⟨hB₁m, hlarge⟩
  rcases max_le_iff.mp hlarge with ⟨hB₂m, hB₃m⟩
  let X := log (m : ℝ)
  have hX1 : 1 < X := lt_of_lt_of_le (by norm_num) hclock2
  have hL0 : 0 < log X := log_pos hX1
  have hfirstSmall := hB₁ m hm mu hmu hrecord hB₁m
  have hsecondSmall := hB₂ m hm mu hmu hrecord hB₂m
  have hsqrtSmall :
      sqrt (sqrt X * Real.rpow (log X) (2 * a + 2) *
        (actualDefect X m - completeFirstLayerLoss X m)) < δ :=
    (Real.sqrt_lt hfirstSmall.1 hδ.le).mpr hfirstSmall.2
  have hlastSmall : Real.rpow (log X) (a + 2) / sqrt X < δ := hB₃ X hB₃m
  change 0 ≤ Real.rpow (log X) a * higherInventoryMismatch X m / sqrt X ∧
    Real.rpow (log X) a * higherInventoryMismatch X m / sqrt X < ε
  refine ⟨div_nonneg
    (mul_nonneg (Real.rpow_nonneg hL0.le a) (inventory_mismatch_nonneg X m))
    (sqrt_nonneg X), ?_⟩
  calc
    Real.rpow (log X) a * higherInventoryMismatch X m / sqrt X ≤
        1000 *
          (sqrt (sqrt X * Real.rpow (log X) (2 * a + 2) *
              (actualDefect X m - completeFirstLayerLoss X m)) +
            sqrt X * Real.rpow (log X) (a + 1) *
              (actualDefect X m - completeFirstLayerLoss X m) +
            Real.rpow (log X) (a + 2) / sqrt X) :=
      normalized_inventory_bound hX m (by omega) a
    _ < 1000 * (δ + δ + δ) :=
      mul_lt_mul_of_pos_left
        (add_lt_add (add_lt_add hsqrtSmall hsecondSmall.2) hlastSmall) (by norm_num)
    _ = ε := by dsimp [δ]; ring

end D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherInventoryAllLog
