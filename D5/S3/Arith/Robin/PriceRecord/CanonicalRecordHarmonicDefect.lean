/- GID: D5/S3/Arith/Robin/PriceRecord/CanonicalRecordHarmonicDefect
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/CanonicalRecordHarmonicDefect
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: Weighted harmonic bounds for the complete canonical record defect. -/
import D5.S3.Arith.Robin.PriceRecord.CanonicalRecordPowerDefect
import D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! Harmonic higher-inventory response and complete loss for the exact real record family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect

open Finset Real
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask (actualDefect)
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
open D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open D5.S3.Arith.Robin.PriceRecord.CompleteHigherInventoryDuality
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff

/-- At ordered positive prices, the mass difference sums the extra strict coordinates. -/
private theorem canonical_higher_mass_sub_eq_sum_sdiff {η ζ : ℝ}
    (hη : 0 < η) (hζ : 0 < ζ) (hle : η ≤ ζ) :
    higherMass (strictInteger η) - higherMass (strictInteger ζ) =
      ∑ c ∈ coordinates (strictInteger η) \ coordinates (strictInteger ζ), log (c.1 : ℝ) := by
  classical
  rw [higherMass_eq_coordinate_sum, higherMass_eq_coordinate_sum]
  exact (Finset.sum_sdiff_eq_sub
    (f := fun c : ℕ × ℕ => log (c.1 : ℝ)) (canonical_coordinates_antitone hη hζ hle)).symm

private theorem mass_sub_nonneg_of_le_of_le {a b c d : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    0 ≤ higherMass (strictInteger b) - higherMass (strictInteger c) ∧
    higherMass (strictInteger b) - higherMass (strictInteger c) ≤
      higherMass (strictInteger a) - higherMass (strictInteger d) := by
  classical
  have hb := ha.trans_le hab
  have hc := hb.trans_le hbc
  rw [canonical_higher_mass_sub_eq_sum_sdiff hb hc hbc,
    canonical_higher_mass_sub_eq_sum_sdiff ha hd (hab.trans (hbc.trans hcd))]
  constructor
  · exact sum_nonneg fun z hz => (mem_coordinates.mp (mem_sdiff.mp hz).1).1.log_pos.le
  · apply sum_le_sum_of_subset_of_nonneg
    · intro z hz
      obtain ⟨hzb, hzc⟩ := mem_sdiff.mp hz
      exact mem_sdiff.mpr ⟨canonical_coordinates_antitone ha hb hab hzb,
        fun hzd => hzc (canonical_coordinates_antitone hc hd hcd hzd)⟩
    · intro z hz _
      exact (mem_coordinates.mp (mem_sdiff.mp hz).1).1.log_pos.le

/-- A half-open interval of width at most one has at most one natural point. -/
private theorem nat_eq_of_mem_half_open {a b : ℝ} {p q : ℕ} (hwidth : b - a ≤ 1)
    (hp : a ≤ (p : ℝ) ∧ (p : ℝ) < b) (hq : a ≤ (q : ℝ) ∧ (q : ℝ) < b) : p = q := by
  have hgap (m n : ℕ) (hm : a ≤ (m : ℝ)) (hn : (n : ℝ) < b) : ¬ m < n := by
    intro hmn
    have hcast : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (show m + 1 ≤ n by omega)
    linarith only [hm, hn, hwidth, hcast]
  exact le_antisymm (le_of_not_gt (hgap q p hq.1 hp.2)) (le_of_not_gt (hgap p q hp.1 hq.2))

private theorem harmonic_weight_sum_bound {L : ℝ} (hL : 1 ≤ L) :
    (∑ j ∈ Icc 1 ⌊6 * L⌋₊, (log 2 + L / (j : ℝ))) ≤
      L * (6 * log 2 + 1 + log (6 * L)) := by
  let n := ⌊6 * L⌋₊
  have h6 : 1 ≤ 6 * L := by linarith
  have hn : (n : ℝ) ≤ 6 * L := Nat.floor_le (by linarith)
  have hH : (∑ j ∈ Icc 1 n, (j : ℝ)⁻¹) ≤ 1 + log (6 * L) := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
      harmonic_floor_le_one_add_log (6 * L) h6
  change (∑ j ∈ Icc 1 n, (log 2 + L / (j : ℝ))) ≤ _
  calc
    _ = (n : ℝ) * log 2 + L * (∑ j ∈ Icc 1 n, (j : ℝ)⁻¹) := by
      simp only [div_eq_mul_inv, sum_add_distrib, ← mul_sum, sum_const,
        nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
    _ ≤ (6 * L) * log 2 + L * (1 + log (6 * L)) :=
      add_le_add (mul_le_mul_of_nonneg_right hn (log_nonneg (by norm_num)))
        (mul_le_mul_of_nonneg_left hH (by linarith))
    _ = _ := by ring

/-- The strict higher inventory in the relative price bracket has at most
one prime in each active layer, including at the endpoint X = 729. -/
theorem harmonic_higher_mass_response {X : ℝ} (hX : max (exp 4) 729 ≤ X) :
    let q := referencePrice X
    let ηm := (1 - 3 / X) * q
    let ηp := (1 + 3 / X) * q
    0 ≤ higherMass (strictInteger ηm) - higherMass (strictInteger ηp) ∧
    higherMass (strictInteger ηm) - higherMass (strictInteger ηp) ≤
      log X * (6 * log 2 + 1 + log (6 * log X)) := by
  classical
  have hX4 := (le_max_left (exp 4) (729 : ℝ)).trans hX
  have hX729 := (le_max_right (exp 4) (729 : ℝ)).trans hX
  have hX2 : exp 2 ≤ X := (exp_le_exp.mpr (by norm_num : (2 : ℝ) ≤ 4)).trans hX4
  have hX0 : 0 < X := by linarith
  have hL4 : 4 ≤ log X := (le_log_iff_exp_le hX0).mpr hX4
  let s : ℝ := 3 / X
  let q := referencePrice X
  let ηm := (1 - s) * q
  let ηp := (1 + s) * q
  change (0 ≤ higherMass (strictInteger ηm) - higherMass (strictInteger ηp)) ∧
    higherMass (strictInteger ηm) - higherMass (strictInteger ηp) ≤
      log X * (6 * log 2 + 1 + log (6 * log X))
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s ≤ 1 / 2 := (div_le_iff₀ hX0).mpr (by linarith)
  have hq : 0 < q := reference_price_pos (by linarith)
  have hηm : 0 < ηm := mul_pos (by linarith) hq
  have hηp : 0 < ηp := mul_pos (by linarith) hq
  have hmp : ηm ≤ ηp := mul_le_mul_of_nonneg_right (by linarith) hq.le
  have hηm' : ηm = (1 - s) / (X * log X) := by
    dsimp [ηm, q, referencePrice]
    ring
  let C := coordinates (strictInteger ηm) \ coordinates (strictInteger ηp)
  let J := C.image Prod.snd
  let a := fun j => cutoff j ηp
  let b := fun j => cutoff j ηm
  have hC {p j : ℕ} (hc : (p, j) ∈ C) :
      p.Prime ∧ 2 ≤ j ∧ a j ≤ (p : ℝ) ∧ (p : ℝ) < b j := by
    obtain ⟨hcm, hcp⟩ := mem_sdiff.mp hc
    obtain ⟨hp, hj, hgm⟩ := (canonical_mem hηm).mp hcm
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hbm : ηm < beta j (p : ℝ) := by rwa [beta_nat hp (by omega : 1 ≤ j)]
    have hbp : ¬ ηp < beta j (p : ℝ) := by
      rw [beta_nat hp (by omega : 1 ≤ j)]
      exact fun h => hcp ((canonical_mem hηp).mpr ⟨hp, hj, h⟩)
    exact ⟨hp, hj, le_of_not_gt (fun h => hbp ((cutoff_occupancy hj hηp hp2).mpr h)),
      (cutoff_occupancy hj hηm hp2).mp hbm⟩
  have hroot {j : ℕ} (hj : j ∈ J) :
      2 ≤ j ∧ b j ≤ 2 * X ^ (1 / (j : ℝ)) ∧ (j : ℝ) < 6 * log X := by
    obtain ⟨⟨p, k⟩, hc, rfl⟩ := mem_image.mp hj
    obtain ⟨hp, hk, _, hpb⟩ := hC hc
    have hactive : 2 < b k :=
      (by exact_mod_cast hp.two_le : (2 : ℝ) ≤ p).trans_lt hpb
    dsimp [b] at hactive
    rw [hηm'] at hactive
    obtain ⟨hroot₁, hroot₂, hkL⟩ := active_root_bounds hX2 hs hs2 hk hactive
    exact ⟨hk, by simpa only [b, hηm'] using hroot₁.trans hroot₂, hkL⟩
  have hsqrt : 27 ≤ sqrt X :=
    (le_sqrt (by norm_num : (0 : ℝ) ≤ 27) hX0.le).mpr (by
      convert hX729 using 1 <;> norm_num)
  have hwidth {j : ℕ} (hj : j ∈ J) : b j - a j ≤ 1 := by
    obtain ⟨hj2, hb, _⟩ := hroot hj
    have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj2
    have hj0 : (0 : ℝ) < j := by linarith
    have he : 1 / (j : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hjr
    have hr := rpow_le_rpow_of_exponent_le (show 1 ≤ X by linarith) he
    rw [← sqrt_eq_rpow] at hr
    have hb' : b j ≤ 2 * sqrt X := hb.trans (mul_le_mul_of_nonneg_left hr (by norm_num))
    have hpow : sqrt X ^ 2 = X := sq_sqrt hX0.le
    calc
      b j - a j ≤ 9 * s * b j / (j : ℝ) := cutoff_movement hj2 hq hs hs2
      _ ≤ 9 * s * (2 * sqrt X) / 2 := by
        apply (div_le_div_iff₀ hj0 (by norm_num)).mpr
        have hmul := mul_le_mul_of_nonneg_left hb' (show 0 ≤ 9 * s by positivity)
        have hscale := mul_le_mul_of_nonneg_left hjr (show 0 ≤ 9 * s * (2 * sqrt X) by positivity)
        linarith only [mul_le_mul_of_nonneg_right hmul (by norm_num : (0 : ℝ) ≤ 2), hscale]
      _ ≤ 1 := by
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
        dsimp [s]
        have hh : 27 * sqrt X ≤ X := by
          calc
            27 * sqrt X ≤ sqrt X * sqrt X :=
              mul_le_mul_of_nonneg_right hsqrt (sqrt_nonneg X)
            _ = X := by simpa only [pow_two] using hpow
        have ht := (div_le_one hX0).mpr hh
        have hid : 9 * (3 / X) * (2 * sqrt X) = 2 * ((27 * sqrt X) / X) := by ring
        rw [hid]
        linarith only [ht]
  have hinj (c : ℕ × ℕ) (hc : c ∈ C) (d : ℕ × ℕ) (hd : d ∈ C)
      (h : c.2 = d.2) : c = d := by
    rcases c with ⟨p, j⟩
    rcases d with ⟨p', j'⟩
    dsimp at h
    subst j'
    have hj : j ∈ J := mem_image_of_mem Prod.snd hc
    have heq := nat_eq_of_mem_half_open (hwidth hj) (hC hc).2.2 (hC hd).2.2
    rw [heq]
  let weight := fun j : ℕ => log 2 + log X / (j : ℝ)
  have hweight (j : ℕ) : 0 ≤ weight j :=
    add_nonneg (log_nonneg (by norm_num)) (div_nonneg (by linarith) (Nat.cast_nonneg j))
  have hpoint (c : ℕ × ℕ) (hc : c ∈ C) : log (c.1 : ℝ) ≤ weight c.2 := by
    obtain ⟨hp, _, _, hpb⟩ := hC (p := c.1) (j := c.2) hc
    have hj : c.2 ∈ J := mem_image_of_mem Prod.snd hc
    calc
      log (c.1 : ℝ) ≤ log (2 * X ^ (1 / (c.2 : ℝ))) :=
        log_le_log (by exact_mod_cast hp.pos) (hpb.le.trans (hroot hj).2.1)
      _ = weight c.2 := by
        rw [log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (rpow_pos_of_pos hX0 (1 / (c.2 : ℝ))).ne', log_rpow hX0]
        dsimp [weight]
        ring
  have hJ : J ⊆ Icc 1 ⌊6 * log X⌋₊ := by
    intro j hj
    obtain ⟨hj2, _, hjL⟩ := hroot hj
    exact mem_Icc.mpr ⟨by omega, Nat.le_floor hjL.le⟩
  rw [canonical_higher_mass_sub_eq_sum_sdiff hηm hηp hmp]
  change (0 ≤ ∑ c ∈ C, log (c.1 : ℝ)) ∧
    (∑ c ∈ C, log (c.1 : ℝ)) ≤ _
  constructor
  · exact sum_nonneg fun c hc => (hC (p := c.1) (j := c.2) hc).1.log_pos.le
  · calc
      _ ≤ ∑ c ∈ C, weight c.2 := sum_le_sum hpoint
      _ = ∑ j ∈ J, weight j := (sum_image hinj).symm
      _ ≤ ∑ j ∈ Icc 1 ⌊6 * log X⌋₊, weight j :=
        sum_le_sum_of_subset_of_nonneg hJ (fun j _ _ => hweight j)
      _ ≤ _ := harmonic_weight_sum_bound (by linarith)

/-- The literal change in higher mass at the deterministic strict optimizer,
measured against the strict optimizer of the reference price. -/
theorem deterministic_harmonic_inventory_bound {X : ℝ} (hX : max (exp 4) 729 ≤ X) :
    let m := strictInteger (firstLayerPrice (X + 1))
    let M := higherMass m - higherMass (strictInteger (referencePrice X))
    0 ≤ M ∧ M ≤ log X * (6 * log 2 + 1 + log (6 * log X)) := by
  have hX4 := (le_max_left (exp 4) (729 : ℝ)).trans hX
  have hX729 := (le_max_right (exp 4) (729 : ℝ)).trans hX
  have hX0 : 0 < X := by linarith
  have hq : 0 < referencePrice X := reference_price_pos (by linarith)
  have hs : 0 < 3 / X := by positivity
  have hs1 : 3 / X < 1 := (div_lt_one hX0).mpr (by linarith)
  obtain ⟨_, _, _, _, hlow, hhigh, _, _, _, _, _, _, _, _⟩ :=
    CanonicalRecordPowerDefect.canonical_record_power_defect X hX4
  have hsub := mass_sub_nonneg_of_le_of_le
    (mul_pos (by linarith : 0 < 1 - 3 / X) hq)
    (mul_pos (by linarith : 0 < 1 + 3 / X) hq) hlow hhigh.le
    (le_mul_of_one_le_left hq.le (by linarith : 1 ≤ 1 + 3 / X))
  exact ⟨hsub.1, hsub.2.trans (harmonic_higher_mass_response hX).2⟩

/-- The combined second- and higher-layer loss has the harmonic upper bound. -/
theorem canonical_record_higher_loss_bound {X : ℝ} (hX : max (exp 4) 729 ≤ X) :
    let m := strictInteger (firstLayerPrice (X + 1))
    let H := completeSecondLayerLoss X m + completeHigherLayerLoss X m
    0 ≤ H ∧ H ≤ 3 * (6 * log 2 + 1 + log (6 * log X)) / X ^ 2 := by
  classical
  have hX4 := (le_max_left (exp 4) (729 : ℝ)).trans hX
  have hX1 : 1 < X := (by norm_num : (1 : ℝ) < 729).trans_le
    ((le_max_right (exp 4) (729 : ℝ)).trans hX)
  have hX0 : 0 < X := zero_lt_one.trans hX1
  have hL0 : 0 < log X := log_pos hX1
  let mu := firstLayerPrice (X + 1)
  let m := strictInteger mu
  let q := referencePrice X
  let A := coordinates m
  let C := coordinates (strictInteger q)
  let M := higherMass m - higherMass (strictInteger q)
  let B := 6 * log 2 + 1 + log (6 * log X)
  obtain ⟨hmu, _, _, _, hlow, hhigh, _, _, _, _, _, _, _, _⟩ :=
    CanonicalRecordPowerDefect.canonical_record_power_defect X hX4
  change 0 < mu at hmu
  change mu < q at hhigh
  have hq : 0 < q := reference_price_pos hX1
  have hCA : C ⊆ A := canonical_coordinates_antitone hmu hq hhigh.le
  have hsum : completeSecondLayerLoss X m + completeHigherLayerLoss X m =
      ∑ c ∈ A \ C, layerLoss X m c.1 c.2 := by
    have hunion : C ∪ A = A := union_eq_right.mpr hCA
    have hcoords := complete_loss_coordinates hX1 m
    change (∑ c ∈ C ∪ A, layerLoss X m c.1 c.2) = _ at hcoords
    rw [hunion] at hcoords
    rw [← hcoords]
    symm
    apply sum_subset sdiff_subset
    intro c hc hnot
    have hcC : c ∈ C := by
      by_contra hn
      exact hnot (mem_sdiff.mpr ⟨hc, hn⟩)
    obtain ⟨_, _, hv⟩ := mem_coordinates.mp hc
    obtain ⟨hp, _, hg⟩ := (canonical_mem hq).mp hcC
    have hmargin : 0 ≤ rawLayerMargin X c.1 c.2 :=
      mul_nonneg hp.log_pos.le (sub_nonneg.mpr hg.le)
    simp only [layerLoss, if_pos hv, max_eq_left hmargin, sub_self]
  have hgap : q - mu ≤ (3 / X) * q := by
    change (1 - 3 / X) * q ≤ mu at hlow
    nlinarith only [hlow]
  have hscale : 0 ≤ (3 / X) * q := mul_nonneg (by positivity) hq.le
  have hM : 0 ≤ M ∧ M ≤ log X * B := deterministic_harmonic_inventory_bound hX
  change 0 ≤ completeSecondLayerLoss X m + completeHigherLayerLoss X m ∧
    completeSecondLayerLoss X m + completeHigherLayerLoss X m ≤ 3 * B / X ^ 2
  rw [hsum]
  refine ⟨sum_nonneg (fun c _ => layer_loss_nonneg X m c.1 c.2), ?_⟩
  calc
    _ ≤ ∑ c ∈ A \ C, (q - mu) * log (c.1 : ℝ) := by
      apply sum_le_sum
      intro c hc
      obtain ⟨hcA, hcC⟩ := mem_sdiff.mp hc
      obtain ⟨hp, hj, hg⟩ := (canonical_mem hmu).mp hcA
      have hv := (mem_coordinates.mp hcA).2.2
      have hgq : goldenLayerMarginal c.1 c.2 ≤ q :=
        le_of_not_gt fun h => hcC ((canonical_mem hq).mpr ⟨hp, hj, h⟩)
      have hmargin : rawLayerMargin X c.1 c.2 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hp.log_pos.le (sub_nonpos.mpr hgq)
      rw [layerLoss, if_pos hv, max_eq_right hmargin, zero_sub]
      change -(log (c.1 : ℝ) * (goldenLayerMarginal c.1 c.2 - q)) ≤ _
      nlinarith only [mul_le_mul_of_nonneg_right hg.le hp.log_pos.le]
    _ = (q - mu) * M := by
      dsimp only [M]
      rw [← mul_sum, canonical_higher_mass_sub_eq_sum_sdiff hmu hq hhigh.le]
    _ ≤ ((3 / X) * q) * M := mul_le_mul_of_nonneg_right hgap hM.1
    _ ≤ ((3 / X) * q) * (log X * B) := mul_le_mul_of_nonneg_left hM.2 hscale
    _ = 3 * B / X ^ 2 := by
      dsimp [q, referencePrice]
      field_simp [hX0.ne', hL0.ne'] <;> ring

/-- Higher loss and complete defect for the deterministic strict optimizer
at each real reference at least the maximum of exp(4) and 729. -/
theorem canonical_record_harmonic_defect {X : ℝ} (hX : max (exp 4) 729 ≤ X) :
    let m := strictInteger (firstLayerPrice (X + 1))
    let R := actualDefect X m - completeFirstLayerLoss X m
    let D := actualDefect X m
    0 ≤ R ∧ R ≤ 3 * (6 * log 2 + 1 + log (6 * log X)) / X ^ 2 ∧
    0 ≤ D ∧ D ≤ (3 * (6 * log 2 + 1 + log (6 * log X)) + 7 / 4) / X ^ 2 := by
  have hX4 := (le_max_left (exp 4) (729 : ℝ)).trans hX
  have hX1 : 1 < X := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 4)).trans_le hX4
  let m := strictInteger (firstLayerPrice (X + 1))
  let R := actualDefect X m - completeFirstLayerLoss X m
  let B := 6 * log 2 + 1 + log (6 * log X)
  obtain ⟨hmu, _, _, _, _, _, _, _, _, _, _, hfirst, hD0, _⟩ :=
    CanonicalRecordPowerDefect.canonical_record_power_defect X hX4
  have hR : R = completeSecondLayerLoss X m + completeHigherLayerLoss X m := by
    dsimp only [R]
    linarith only [actual_defect_decomposition hX1 (n := m) (strictInteger_pos hmu)]
  have hbound : 0 ≤ R ∧ R ≤ 3 * B / X ^ 2 := by
    rw [hR]
    exact canonical_record_higher_loss_bound hX
  change 0 ≤ R ∧ R ≤ 3 * B / X ^ 2 ∧
    0 ≤ actualDefect X m ∧ actualDefect X m ≤ (3 * B + 7 / 4) / X ^ 2
  refine ⟨hbound.1, hbound.2, hD0, ?_⟩
  calc
    actualDefect X m = R + completeFirstLayerLoss X m := by
      dsimp only [R]
      ring
    _ ≤ 3 * B / X ^ 2 + (7 / 4) / X ^ 2 := add_le_add hbound.2 hfirst
    _ = _ := by rw [add_div]

open Filter Asymptotics
open scoped Topology

private theorem isLittleO_log_div_sq_of_bound {f : ℝ → ℝ} {a : ℝ}
    (hbound : ∀ᶠ X : ℝ in atTop, 0 ≤ f X ∧
      f X ≤ (3 * (6 * log 2 + 1 + log (6 * log X)) + a) / X ^ 2) :
    f =o[atTop] (fun X : ℝ => log X / X ^ 2) := by
  let constant : ℝ := 3 * (6 * log 2 + 1 + log 6) + a
  let upper := fun X : ℝ => (constant + 3 * log (log X)) / log X
  have hconstant := (isLittleO_const_log_atTop (c := constant)).tendsto_div_nhds_zero
  have hlog := (isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_log_atTop).const_mul 3
  have hupper : Tendsto upper atTop (𝓝 0) := by
    simpa [upper, add_div, mul_div_assoc, Function.comp_def] using hconstant.add hlog
  have hpositive : ∀ᶠ X : ℝ in atTop, 1 < X := eventually_gt_atTop 1
  apply isLittleO_of_tendsto'
  · filter_upwards [hpositive] with X hX hz
    exact ((div_pos (log_pos hX) (sq_pos_of_pos (zero_lt_one.trans hX))).ne' hz).elim
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · filter_upwards [hpositive, hbound] with X hX hf
      exact div_nonneg hf.1 (div_nonneg (log_pos hX).le (sq_nonneg X))
    · filter_upwards [hpositive, hbound] with X hX hf
      have hX0 : 0 < X := zero_lt_one.trans hX
      have hL : 0 < log X := log_pos hX
      calc
        _ ≤ ((3 * (6 * log 2 + 1 + log (6 * log X)) + a) / X ^ 2) /
              (log X / X ^ 2) := div_le_div_of_nonneg_right hf.2 (by positivity)
        _ = upper X := by
          rw [log_mul (by norm_num : (6 : ℝ) ≠ 0) hL.ne']
          dsimp [upper, constant]
          field_simp [hX0.ne', hL.ne'] <;> ring

/-- The complete loss from layers two and higher is little-o of the power bound scale. -/
theorem canonical_record_higher_loss_isLittleO :
    (fun X : ℝ =>
      let m := strictInteger (firstLayerPrice (X + 1))
      completeSecondLayerLoss X m + completeHigherLayerLoss X m) =o[atTop]
      (fun X : ℝ => log X / X ^ 2) := by
  apply isLittleO_log_div_sq_of_bound (a := 0)
  filter_upwards [eventually_ge_atTop (max (exp 4) 729)] with X hX
  simpa only [add_zero] using canonical_record_higher_loss_bound hX

/-- The complete deterministic defect is little-o of the power bound scale. -/
theorem canonical_record_defect_isLittleO :
    (fun X : ℝ => actualDefect X (strictInteger (firstLayerPrice (X + 1)))) =o[atTop]
      (fun X : ℝ => log X / X ^ 2) := by
  apply isLittleO_log_div_sq_of_bound (a := 7 / 4)
  filter_upwards [eventually_ge_atTop (max (exp 4) 729)] with X hX
  exact (canonical_record_harmonic_defect hX).2.2

end D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect
