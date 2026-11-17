/- GID: D5/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: Complete higher loss controls the higher mass of every actual integer. -/
import D5.S3.Arith.Robin.PriceRecord.ActualHigherMassResponse
import Mathlib.Tactic

/-! Finite duality and the canonical response bound give coercivity for
arbitrary actual prime support and exponents. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualHigherMassCoercivity
open Finset Real
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open D5.S3.Arith.Robin.PriceRecord.CompleteHigherInventoryDuality
open D5.S3.Arith.Robin.PriceRecord.ActualHigherMassResponse

/-- The actual dual estimate keeps all coordinates of n in the common finite
set. The canonical low-price cutoff is used only to include positive parts. -/
theorem actual_dual_estimate {X s : ℝ} (hX : exp 2 ≤ X) {n : ℕ} (hn : 1 ≤ n)
    (hs : 0 < s) (hs2 : s ≤ 1 / 2) :
    |higherMass n - higherMass (strictInteger (referencePrice X))| ≤
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
  have hid := literal_loss_identity hX1 hn S hprime (union_subset hbS hnS)
  have hd := finite_dual_abs S coordinateGain coordinateWeight i
    («λ» := lam) (t := t)
    (fun c hc => (hprime c hc).1.log_pos.le) ht
  change |(∑ c ∈ S, if i c then coordinateWeight c else 0) - strictMass S lam| ≤
    (potential S lam - (∑ c ∈ S, if i c then coordinateGain c else 0) +
      lam * (∑ c ∈ S, if i c then coordinateWeight c else 0)) / t +
      strictMass S (lam - t) - strictMass S (lam + t) at hd
  rw [hH, hB, strictMass_eq hlam hprime hbS, strictMass_eq hm hprime hmS,
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

/-- Scalar optimization at precisely min(1/2,sqrt(R*q)). The R=0 branch
uses an actual epsilon argument, with no continuity assumption on inventory. -/
theorem balance_response {Δ R q L : ℝ} (hR : 0 ≤ R) (hq : 0 < q) (hL : 0 < L)
    (hbound : ∀ s : ℝ, 0 < s → s ≤ 1 / 2 →
      Δ ≤ R * q ^ 2 * L / s + 400 * s * q * L + 400 * L ^ 2) :
    Δ ≤ 1000 * (q * sqrt q * L * sqrt R + q ^ 2 * L * R + L ^ 2) := by
  have hqR : 0 ≤ q ^ 2 * L * R := by positivity
  have hsroot : 0 ≤ q * sqrt q * L * sqrt R := by positivity
  by_cases hzero : R = 0
  · have hδ : Δ ≤ 400 * L ^ 2 := by
      by_contra! hnot
      let ε := Δ - 400 * L ^ 2
      have hε : 0 < ε := by dsimp [ε]; linarith
      let s := min (1 / 2) (ε / (800 * q * L))
      have hs : 0 < s := lt_min (by norm_num) (by positivity)
      have hs2 : s ≤ 1 / 2 := min_le_left _ _
      have hsε : 800 * s * q * L ≤ ε := by
        have hh := (le_div_iff₀ (show 0 < 800 * q * L by positivity)).mp
          (min_le_right (1 / 2) (ε / (800 * q * L)))
        dsimp [s]
        nlinarith
      have hh := hbound s hs hs2
      rw [hzero] at hh
      simp only [zero_mul, zero_div, zero_add] at hh
      dsimp [ε] at hsε
      have hA : 0 < s * q * L := by positivity
      nlinarith
    nlinarith [sq_nonneg L]
  have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hzero)
  let s := min (1 / 2) (sqrt (R * q))
  have hs : 0 < s := lt_min (by norm_num) (sqrt_pos.mpr (mul_pos hRpos hq))
  have hs2 : s ≤ 1 / 2 := min_le_left _ _
  have hh := hbound s hs hs2
  by_cases hsmall : R * q ≤ 1 / 4
  · have hroot : sqrt (R * q) ≤ 1 / 2 := by
      nlinarith [sq_sqrt (show 0 ≤ R * q by positivity), sqrt_nonneg (R * q)]
    have hsEq : s = sqrt (R * q) := min_eq_right hroot
    have hsSq : s ^ 2 = R * q := by rw [hsEq, sq_sqrt (by positivity : 0 ≤ R * q)]
    have hquot : R * q ^ 2 * L / s = q * L * s := by
      apply (div_eq_iff hs.ne').mpr
      nlinarith [congrArg (fun z : ℝ => q * L * z) hsSq]
    have hrootmul : s = sqrt R * sqrt q := by rw [hsEq, sqrt_mul hR]
    rw [hquot, hrootmul] at hh
    nlinarith [sq_nonneg L]
  · have hroot : 1 / 2 ≤ sqrt (R * q) := by
      nlinarith [sq_sqrt (show 0 ≤ R * q by positivity), sqrt_nonneg (R * q)]
    have hsEq : s = 1 / 2 := min_eq_left hroot
    rw [hsEq] at hh
    have hbig : q ≤ 4 * R * q ^ 2 := by
      have hrq : (1 / 4 : ℝ) ≤ R * q := (lt_of_not_ge hsmall).le
      have hm := mul_le_mul_of_nonneg_right hrq hq.le
      nlinarith
    have hbigL := mul_le_mul_of_nonneg_right hbig hL.le
    nlinarith [sq_nonneg L]

/-- Literal complete higher loss versus actual higher mass, with all original
support and tie cases. Constants are independent of X AND n. -/
theorem actual_complete_higher_mass_coercivity {X : ℝ} (hX : exp 2 ≤ X)
    (n : ℕ) (hn : 1 ≤ n) :
    let R := actualDefect X n - completeFirstLayerLoss X n
    0 ≤ R ∧
    |higherMass n - higherMass (strictInteger (referencePrice X))| ≤
      1000 * (X ^ (3 / 4 : ℝ) * log X * sqrt R + X * log X * R + log X ^ 2) := by
  have hX0 : 0 < X := (exp_pos 2).trans_le hX
  have hL : 2 ≤ log X := (le_log_iff_exp_le hX0).mpr hX
  have hL0 : 0 < log X := by linarith
  have hX1 : 1 < X := (log_pos_iff hX0.le).mp hL0
  let R := actualDefect X n - completeFirstLayerLoss X n
  have hR : 0 ≤ R := by
    have hd := actual_defect_decomposition hX1 hn
    have h2 : 0 ≤ completeSecondLayerLoss X n :=
      sum_nonneg (fun p _ => layer_loss_nonneg X n p 2)
    have h3 : 0 ≤ completeHigherLayerLoss X n :=
      sum_nonneg (fun p _ => sum_nonneg (fun j _ => layer_loss_nonneg X n p j))
    dsimp [R]
    linarith
  have hbal := balance_response hR (sqrt_pos.mpr hX0) hL0 (fun s hs hs2 => by
    simpa only [sq_sqrt hX0.le, mul_assoc] using actual_dual_estimate hX hn hs hs2)
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
end D5.S3.Arith.Robin.PriceRecord.ActualHigherMassCoercivity
