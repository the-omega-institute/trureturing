/- GID: D5/S3/Arith/Robin/PriceRecord/ActualHigherMassResponse
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualHigherMassResponse
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: Integer counting bounds the response of the literal strict higher inventory. -/
import D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
import D5.S3.Arith.Robin.PriceRecord.CompleteHigherInventoryDuality
import Mathlib.Tactic

/-! Only canonical inventories are bounded by the cutoffs. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualHigherMassResponse
open Finset Real
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open D5.S3.Arith.Robin.PriceRecord.CompleteHigherInventoryDuality

private def layerPrimes (C : Finset (ℕ × ℕ)) (j : ℕ) : Finset ℕ :=
  (C.filter fun c => c.2 = j).image Prod.fst

private theorem mem_layerPrimes {C : Finset (ℕ × ℕ)} {p j : ℕ} :
    p ∈ layerPrimes C j ↔ (p, j) ∈ C := by
  classical
  simp only [layerPrimes, mem_image, mem_filter]
  constructor
  · rintro ⟨⟨q, k⟩, ⟨hc, hk⟩, hp⟩
    dsimp at hk hp
    subst q
    subst k
    exact hc
  · intro h
    exact ⟨(p, j), ⟨h, rfl⟩, rfl⟩

private theorem sum_by_layer (C : Finset (ℕ × ℕ)) :
    ∑ c ∈ C, log (c.1 : ℝ) =
      ∑ j ∈ C.image Prod.snd, ∑ p ∈ layerPrimes C j, log (p : ℝ) := by
  classical
  let J := C.image Prod.snd
  let A := fun j => (layerPrimes C j).image fun p => (p, j)
  have hset : C = J.biUnion A := by
    ext c
    rcases c with ⟨p, j⟩
    simp only [mem_biUnion, A, mem_image, Prod.mk.injEq]
    constructor
    · intro hc
      exact ⟨j, mem_image_of_mem Prod.snd hc, p, mem_layerPrimes.mpr hc, rfl, rfl⟩
    · rintro ⟨k, _, q, hq, rfl, rfl⟩
      exact mem_layerPrimes.mp hq
  calc
    (∑ c ∈ C, log (c.1 : ℝ)) = ∑ c ∈ J.biUnion A, log (c.1 : ℝ) :=
      congrArg (fun T : Finset (ℕ × ℕ) => ∑ c ∈ T, log (c.1 : ℝ)) hset
    _ = ∑ j ∈ C.image Prod.snd, ∑ p ∈ layerPrimes C j, log (p : ℝ) := by
      rw [sum_biUnion]
      · apply sum_congr rfl
        intro j _
        dsimp [A]
        rw [sum_image (fun _ _ _ _ h => (Prod.mk.inj h).1)]
      · intro j _ k _ hjk
        apply disjoint_left.mpr
        intro c hc hd
        obtain ⟨p, _, hp⟩ := mem_image.mp hc
        obtain ⟨q, _, hq⟩ := mem_image.mp hd
        exact hjk (Prod.mk.inj (hp.trans hq.symm)).2

theorem actual_higher_mass_response {X s : ℝ} (hX : exp 2 ≤ X)
    (hs : 0 < s) (hs2 : s ≤ 1 / 2) :
    0 ≤ higherMass (strictInteger ((1 - s) * referencePrice X)) -
      higherMass (strictInteger ((1 + s) * referencePrice X)) ∧
    higherMass (strictInteger ((1 - s) * referencePrice X)) -
      higherMass (strictInteger ((1 + s) * referencePrice X)) ≤
      400 * (s * sqrt X * log X + log X ^ 2) := by
  classical
  have hX0 : 0 < X := (exp_pos 2).trans_le hX
  have hL : 2 ≤ log X := (le_log_iff_exp_le hX0).mpr hX
  have hL0 : 0 < log X := by linarith
  have hX4 : 4 ≤ X := by
    have he1 : 2 < exp 1 := by
      have hh := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
      linarith
    have he2 : exp (2 : ℝ) = exp 1 ^ 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
      ring
    nlinarith
  let lam := referencePrice X
  let ηm := (1 - s) * lam
  let ηp := (1 + s) * lam
  have hlam : 0 < lam := one_div_pos.mpr (mul_pos hX0 hL0)
  have hm : 0 < ηm := mul_pos (by linarith) hlam
  have hp : 0 < ηp := mul_pos (by linarith) hlam
  have hmp : ηm ≤ ηp := mul_le_mul_of_nonneg_right (by linarith) hlam.le
  let Cm := coordinates (strictInteger ηm)
  let Cp := coordinates (strictInteger ηp)
  let C := Cm \ Cp
  let J := C.image Prod.snd
  have hsub : Cp ⊆ Cm := canonical_coordinates_antitone hm hp hmp
  have hmass : higherMass (strictInteger ηm) - higherMass (strictInteger ηp) =
      ∑ c ∈ C, log (c.1 : ℝ) := by
    simpa only [higherMass_eq_coordinate_sum] using
      (Finset.sum_sdiff_eq_sub (f := fun c : ℕ × ℕ => log (c.1 : ℝ)) hsub).symm
  have hC (p j : ℕ) (hc : (p, j) ∈ C) :
      p.Prime ∧ 2 ≤ j ∧
      cutoff j ηp ≤ (p : ℝ) ∧ (p : ℝ) < cutoff j ηm := by
    obtain ⟨hcm, hcp⟩ := mem_sdiff.mp hc
    obtain ⟨hpp, hj, hgm⟩ := (canonical_mem hm).mp hcm
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hbm : ηm < beta j (p : ℝ) := by rwa [beta_nat hpp (by omega)]
    have hbp : ¬ ηp < beta j (p : ℝ) := by
      rw [beta_nat hpp (by omega)]
      intro hh
      exact hcp ((canonical_mem hp).mpr ⟨hpp, hj, hh⟩)
    exact ⟨hpp, hj, le_of_not_gt (fun h => hbp ((cutoff_occupancy hj hp hp2).mpr h)),
      (cutoff_occupancy hj hm hp2).mp hbm⟩
  have hηm : ηm = (1 - s) / (X * log X) := by dsimp [ηm, lam, referencePrice]; ring
  have hJ (j : ℕ) (hj : j ∈ J) : 2 ≤ j ∧ 2 < cutoff j ((1 - s) / (X * log X)) := by
    obtain ⟨⟨p, k⟩, hc, hk⟩ := mem_image.mp hj
    dsimp at hk
    subst k
    have hh := hC p j hc
    refine ⟨hh.2.1, ?_⟩
    rw [← hηm]
    exact (by exact_mod_cast hh.1.two_le : (2 : ℝ) ≤ p).trans_lt hh.2.2.2
  have hcardJ := active_layer_card hX hs hs2 J hJ
  have hsumJ := (active_cutoff_sum hX hs hs2 J hJ).le
  have hcutmono (j : ℕ) (hj : j ∈ J) : cutoff j ηp ≤ cutoff j ηm :=
    cutoff_antitone (hJ j hj).1 hm hp hmp
  have hpoint (j : ℕ) (hj : j ∈ J) :
      (∑ p ∈ layerPrimes C j, log (p : ℝ)) ≤
        (cutoff j ηm - cutoff j ηp + 1) * log X := by
    have hj2 := (hJ j hj).1
    have hc := integer_interval_card (layerPrimes C j) (hcutmono j hj) (fun p hp =>
      ⟨(hC p j (mem_layerPrimes.mp hp)).2.2.1, (hC p j (mem_layerPrimes.mp hp)).2.2.2⟩)
    have hpX (p : ℕ) (hp : p ∈ layerPrimes C j) : (p : ℝ) ≤ X := by
      have hh := hC p j (mem_layerPrimes.mp hp)
      have hb := (active_root_bounds hX hs hs2 hj2 (hJ j hj).2).1.trans
        (active_root_bounds hX hs hs2 hj2 (hJ j hj).2).2.1
      rw [← hηm] at hb
      have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj2
      have he : 1 / (j : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hjr
      have hr := rpow_le_rpow_of_exponent_le (show 1 ≤ X by linarith) he
      rw [← sqrt_eq_rpow] at hr
      have hsqrt : 2 * sqrt X ≤ X := by
        have htwo : 2 ≤ sqrt X := (le_sqrt (by norm_num) hX0.le).mpr (by
          convert hX4 using 1 <;> norm_num)
        have hh := mul_le_mul_of_nonneg_right htwo (sqrt_nonneg X)
        rwa [← pow_two, sq_sqrt hX0.le] at hh
      exact hh.2.2.2.le.trans (hb.trans ((mul_le_mul_of_nonneg_left hr (by norm_num)).trans hsqrt))
    calc
      _ ≤ ∑ _p ∈ layerPrimes C j, log X := by
        apply sum_le_sum
        intro p hp
        have hprime := (hC p j (mem_layerPrimes.mp hp)).1
        exact log_le_log (by exact_mod_cast hprime.pos) (hpX p hp)
      _ = ((layerPrimes C j).card : ℝ) * log X := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hL0.le
  have hmovement (j : ℕ) (hj : j ∈ J) :
      cutoff j ηm - cutoff j ηp ≤ 9 * s * (cutoff j ηm / j) := by
    simpa [ηm, ηp, div_eq_mul_inv, mul_assoc] using
      cutoff_movement (hJ j hj).1 hlam hs hs2
  have hmoveSum : (∑ j ∈ J, (cutoff j ηm - cutoff j ηp)) ≤ 333 * s * sqrt X := by
    have hh := sum_le_sum hmovement
    have hn : 0 ≤ 9 * s := by positivity
    rw [← mul_sum] at hh
    have he : (∑ j ∈ J, cutoff j ηm / j) ≤ 37 * sqrt X := by rwa [hηm]
    have hscaled := mul_le_mul_of_nonneg_left he hn
    calc
      (∑ j ∈ J, (cutoff j ηm - cutoff j ηp)) ≤
          9 * s * (∑ j ∈ J, cutoff j ηm / j) := hh
      _ ≤ 9 * s * (37 * sqrt X) := hscaled
      _ = 333 * s * sqrt X := by ring
  have hsum : (∑ j ∈ J, (cutoff j ηm - cutoff j ηp + 1) * log X) ≤
      333 * s * sqrt X * log X + 6 * log X ^ 2 := by
    rw [← sum_mul, sum_add_distrib]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    have hh := add_le_add hmoveSum hcardJ
    have hm := mul_le_mul_of_nonneg_right hh hL0.le
    convert hm using 1 <;> (try rw [sum_sub_distrib]) <;> ring
  rw [hmass]
  refine ⟨sum_nonneg (fun c hc => ?_), ?_⟩
  · exact (hC c.1 c.2 hc).1.log_pos.le
  · rw [sum_by_layer]
    exact (sum_le_sum hpoint).trans (hsum.trans (by
      nlinarith [mul_nonneg (mul_nonneg hs.le (sqrt_nonneg X)) hL0.le, sq_nonneg (log X)]))
end D5.S3.Arith.Robin.PriceRecord.ActualHigherMassResponse
