/- GID: D5/S3/Arith/Robin/PriceRecord/ActualHigherInventoryCoercivity
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualHigherInventoryCoercivity
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: Complete higher loss controls the full weighted inventory symmetric difference. -/
import D5.S3.Arith.Robin.PriceRecord.ActualHigherMassCoercivity

/-! Full weighted symmetric difference of the literal higher inventories.
The common finite support contains every actual coordinate of n. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualHigherInventoryCoercivity
open Finset Real
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open D5.S3.Arith.Robin.PriceRecord.CompleteHigherInventoryDuality
open D5.S3.Arith.Robin.PriceRecord.ActualHigherMassResponse
open D5.S3.Arith.Robin.PriceRecord.ActualHigherMassCoercivity

/-- All missing and excess coordinates of order at least two, each counted
with its logarithmic prime weight. No cancellation between coordinates. -/
def higherInventoryMismatch (X : ℝ) (n : ℕ) : ℝ :=
  ∑ c ∈ (coordinates n \ coordinates (strictInteger (referencePrice X))) ∪
      (coordinates (strictInteger (referencePrice X)) \ coordinates n),
    coordinateWeight c

/-- The strict central threshold and both strict neighbouring thresholds are
kept literally. In particular, w=0 imposes no condition on q or i. -/
private theorem pointwise_inventory_l1 (i : Bool) {q w t : ℝ}
    (hw : 0 ≤ w) (ht : 0 ≤ t) :
    t * (if i then (if 0 < q then 0 else w) else (if 0 < q then w else 0)) ≤
      max q 0 - (if i then q else 0) +
        t * ((if 0 < q + t * w then w else 0) -
          (if 0 < q - t * w then w else 0)) := by
  have htw : 0 ≤ t * w := mul_nonneg ht hw
  by_cases hq : 0 < q
  · have hlo : 0 < q + t * w := by linarith
    rw [max_eq_left hq.le]
    cases i <;> by_cases hhi : 0 < q - t * w <;>
      simp [hq, hlo, hhi] <;> nlinarith
  · have hhi : ¬ 0 < q - t * w := by linarith
    rw [max_eq_right (le_of_not_gt hq)]
    cases i <;> by_cases hlo : 0 < q + t * w <;>
      simp [hq, hlo, hhi] <;> nlinarith

/-- Finite L1 duality uses the same potential, occupied gain and masses as
finite_dual_abs, but sums the coordinate mismatches before any cancellation. -/
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
  let F := fun η => ∑ c ∈ S, max (b c - η * w c) 0
  let h := fun η => ∑ c ∈ S, if 0 < b c - η * w c then w c else 0
  let H := ∑ c ∈ S, if i c then w c else 0
  let B := ∑ c ∈ S, if i c then b c else 0
  let R := F «λ» - B + «λ» * H
  let D := ∑ c ∈ S, if i c then
    (if 0 < b c - «λ» * w c then 0 else w c)
    else (if 0 < b c - «λ» * w c then w c else 0)
  change D ≤ R / t + h («λ» - t) - h («λ» + t)
  have hpoint (c : ι) (hc : c ∈ S) :
      t * (if i c then (if 0 < b c - «λ» * w c then 0 else w c)
        else (if 0 < b c - «λ» * w c then w c else 0)) ≤
      (max (b c - «λ» * w c) 0 - (if i c then b c else 0) +
        «λ» * (if i c then w c else 0)) +
        t * ((if 0 < b c - («λ» - t) * w c then w c else 0) -
          (if 0 < b c - («λ» + t) * w c then w c else 0)) := by
    have hh := pointwise_inventory_l1 (i c)
      (q := b c - «λ» * w c) (w := w c) (t := t) (hw c hc) ht.le
    have hlo : b c - «λ» * w c + t * w c = b c - («λ» - t) * w c := by ring
    have hhi : b c - «λ» * w c - t * w c = b c - («λ» + t) * w c := by ring
    rw [hlo, hhi] at hh
    cases hi : i c <;>
      simp only [hi, Bool.false_eq_true, if_false, if_true] at hh ⊢ <;>
      nlinarith only [hh]
  have hh := sum_le_sum hpoint
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum] at hh
  change t * D ≤ R + t * (h («λ» - t) - h («λ» + t)) at hh
  have hmul : (D - (h («λ» - t) - h («λ» + t))) * t ≤ R := by
    nlinarith only [hh]
  have hdiv := (le_div_iff₀ ht).mpr hmul
  linarith only [hdiv]

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
        · simp only [if_pos ha, if_pos hb]
        · exact (hcM (mem_union_left _ (mem_sdiff.mpr ⟨ha, hb⟩))).elim
      · by_cases hb : c ∈ C
        · exact (hcM (mem_union_right _ (mem_sdiff.mpr ⟨hb, ha⟩))).elim
        · simp only [if_neg ha, if_neg hb]
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
      simp only [if_pos ha, if_neg hb]
    · obtain ⟨hb, ha⟩ := mem_sdiff.mp hc
      simp only [if_neg ha, if_pos hb]
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
theorem actual_complete_higher_inventory_coercivity {X : ℝ} (hX : exp 2 ≤ X)
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

end D5.S3.Arith.Robin.PriceRecord.ActualHigherInventoryCoercivity
