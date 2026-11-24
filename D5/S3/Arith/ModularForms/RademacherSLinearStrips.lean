/- GID: D5/S3/Arith/ModularForms/RademacherSLinearStrips
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative vanishing of the anchored linear sums on both literal rectangular boundary strips. -/

import D5.S3.Arith.ModularForms.IncompleteKloostermanFourier
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries

open Filter
open scoped BigOperators Matrix Topology UpperHalfPlane

namespace D5.S3.Arith.ModularForms.RademacherSLinearStrips

open RademacherVacuum
open IncompleteKloostermanFourier
open RademacherPhaseRamanujan (sum_vacuumPhase_eq_moebius)

set_option autoImplicit false

noncomputable section

private def kappa : ℂ := (2 * (Real.pi : ℂ)) * Complex.I

/-- The difference of the linear weights at `τ` and at the fixed point `i`. -/
def anchoredWeight (c d : ℤ) (τ : ℍ) : ℂ :=
  kappa * (Complex.I - (τ : ℂ)) / (denominator c d τ * denominator c d UpperHalfPlane.I)

private theorem strip_denominator_bound {A η : ℝ} (hη : 0 < η) {τ : ℍ}
    (hτ : τ ∈ UpperHalfPlane.verticalStrip A η) {c : ℤ} (hc : 0 < c) (d : ℤ) :
    EisensteinSeries.r ⟨⟨A, η⟩, hη⟩ * max (c : ℝ) |(d : ℝ)| ≤
      ‖denominator c d τ‖ := by
  let x : Fin 2 → ℤ := ![c, d]
  have hx : x ≠ 0 := by
    intro h
    exact hc.ne' (by simpa [x] using congrFun h (0 : Fin 2))
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hcNorm : (c : ℝ) ≤ ‖x‖ := by
    simpa only [x, abs_of_pos hc, Int.cast_abs, abs_of_pos hcR] using
      EisensteinSeries.abs_le_left_of_norm d c
  have hdNorm : |(d : ℝ)| ≤ ‖x‖ := by
    simpa only [x, Int.cast_abs] using EisensteinSeries.abs_le_right_of_norm d c
  calc
    _ ≤ EisensteinSeries.r ⟨⟨A, η⟩, hη⟩ * ‖x‖ :=
      mul_le_mul_of_nonneg_left (max_le hcNorm hdNorm) (EisensteinSeries.r_pos _).le
    _ ≤ EisensteinSeries.r τ * ‖x‖ :=
      mul_le_mul_of_nonneg_right (EisensteinSeries.r_lower_bound_on_verticalStrip τ hη hτ)
        (norm_nonneg x)
    _ ≤ _ := by simpa [x, denominator] using EisensteinSeries.r_mul_max_le τ hx

theorem denominator_ne_zero {c : ℤ} (hc : 0 < c) (d : ℤ) (τ : ℍ) :
    denominator c d τ ≠ 0 := by
  have him : (denominator c d τ).im = (c : ℝ) * τ.im := by
    simp [denominator, ← Complex.ofReal_intCast]
  have hp : 0 < (c : ℝ) * τ.im := mul_pos (by exact_mod_cast hc) τ.im_pos
  intro h
  rw [h, Complex.zero_im] at him
  linarith

theorem linearSummand_sub_anchor {c : ℤ} (hc : 0 < c) (d : ℤ) (τ : ℍ) :
    linearSummand c d τ - linearSummand c d UpperHalfPlane.I =
      vacuumPhase c d * anchoredWeight c d τ := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hd₁ := denominator_ne_zero hc d τ
  have hd₂ := denominator_ne_zero hc d UpperHalfPlane.I
  simp only [linearSummand, vacuumArgument, anchoredWeight, kappa,
    Complex.ofReal_mul, Complex.ofReal_ofNat, ← mul_sub]
  congr 1
  field_simp [hcC, hd₁, hd₂]
  simp only [denominator, UpperHalfPlane.coe_I]
  ring

private theorem inverse_step {c d : ℤ} (hc : 0 < c) (z : ℍ) :
    (denominator c (d + 1) z)⁻¹ - (denominator c d z)⁻¹ =
      -((denominator c (d + 1) z)⁻¹ * (denominator c d z)⁻¹) := by
  field_simp [denominator_ne_zero hc d z, denominator_ne_zero hc (d + 1) z]
  simp only [denominator, Int.cast_add, Int.cast_one]
  ring

/-- A compact-uniform bound for the weight and for the adjacent variation. The variation
uses any common lower bound for the two adjacent values of `max c |d|`. -/
theorem anchoredWeight_compact_bounds {K : Set ℍ} (hK : IsCompact K) :
    ∃ D : ℝ, 0 < D ∧ ∀ τ ∈ K, ∀ (c d : ℤ) (t : ℝ), 0 < c → 0 < t →
      t ≤ max (c : ℝ) |(d : ℝ)| →
      ‖anchoredWeight c d τ‖ ≤ D / t ^ 2 ∧
        (t ≤ max (c : ℝ) |((d + 1 : ℤ) : ℝ)| →
          ‖anchoredWeight c (d + 1) τ - anchoredWeight c d τ‖ ≤ D / t ^ 3) := by
  have hKI : IsCompact (insert UpperHalfPlane.I K) := hK.insert _
  obtain ⟨A, η, hη, hstrip⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hKI
  let r := EisensteinSeries.r ⟨⟨A, η⟩, hη⟩
  have hr : 0 < r := EisensteinSeries.r_pos _
  obtain ⟨B₀, hB₀⟩ := hK.bddAbove_image
    ((continuous_const.mul (continuous_const.sub UpperHalfPlane.continuous_coe)).norm :
      Continuous (fun τ : ℍ => ‖kappa * (Complex.I - (τ : ℂ))‖)).continuousOn
  let B : ℝ := max 1 B₀
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  let D := B / r ^ 2 + 2 * B / r ^ 3
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro τ hτ c d t hc ht htd
  let u : ℂ := kappa * (Complex.I - (τ : ℂ))
  let R : ℝ := (r * t)⁻¹
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hu : ‖u‖ ≤ B :=
    (hB₀ (Set.mem_image_of_mem _ hτ)).trans (le_max_right _ _)
  have hinv (z : ℍ) (hz : z ∈ insert UpperHalfPlane.I K) (e : ℤ)
      (he : t ≤ max (c : ℝ) |(e : ℝ)|) : ‖(denominator c e z)⁻¹‖ ≤ R := by
    have hl : r * t ≤ ‖denominator c e z‖ :=
      (mul_le_mul_of_nonneg_left he hr.le).trans (strip_denominator_bound hη (hstrip hz) hc e)
    rw [norm_inv]
    exact inv_anti₀ (mul_pos hr ht) hl
  have hz : τ ∈ insert UpperHalfPlane.I K := Set.mem_insert_of_mem _ hτ
  have hi : UpperHalfPlane.I ∈ insert UpperHalfPlane.I K := Set.mem_insert _ _
  have hweight (e : ℤ) : anchoredWeight c e τ =
      u * ((denominator c e τ)⁻¹ * (denominator c e UpperHalfPlane.I)⁻¹) := by
    simp [anchoredWeight, u, div_eq_mul_inv, mul_inv_rev, mul_comm]
  have hR2 : B * (R * R) = (B / r ^ 2) / t ^ 2 := by
    dsimp [R]
    field_simp [hr.ne', ht.ne']
  have hR3 : B * (R * R * R + R * (R * R)) = (2 * B / r ^ 3) / t ^ 3 := by
    dsimp [R]
    field_simp [hr.ne', ht.ne']
    ring
  refine ⟨?_, ?_⟩
  · rw [hweight]
    simp only [norm_mul]
    calc
      _ ≤ B * (R * R) := mul_le_mul hu
        (mul_le_mul (hinv τ hz d htd) (hinv _ hi d htd) (norm_nonneg _) hR)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hB.le
      _ ≤ D / t ^ 2 := by
        rw [hR2]
        exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  · intro htd'
    let a := (denominator c d τ)⁻¹
    let b := (denominator c d UpperHalfPlane.I)⁻¹
    let a' := (denominator c (d + 1) τ)⁻¹
    let b' := (denominator c (d + 1) UpperHalfPlane.I)⁻¹
    have ha : ‖a‖ ≤ R := hinv τ hz d htd
    have hb : ‖b‖ ≤ R := hinv _ hi d htd
    have ha' : ‖a'‖ ≤ R := hinv τ hz (d + 1) htd'
    have hb' : ‖b'‖ ≤ R := hinv _ hi (d + 1) htd'
    have hda : ‖a' - a‖ ≤ R * R := by
      change ‖(denominator c (d + 1) τ)⁻¹ - (denominator c d τ)⁻¹‖ ≤ _
      rw [inverse_step hc, norm_neg, norm_mul]
      exact mul_le_mul ha' ha (norm_nonneg _) hR
    have hdb : ‖b' - b‖ ≤ R * R := by
      change ‖(denominator c (d + 1) UpperHalfPlane.I)⁻¹ -
        (denominator c d UpperHalfPlane.I)⁻¹‖ ≤ _
      rw [inverse_step hc, norm_neg, norm_mul]
      exact mul_le_mul hb' hb (norm_nonneg _) hR
    rw [hweight, hweight, ← mul_sub]
    change ‖u * (a' * b' - a * b)‖ ≤ _
    rw [show a' * b' - a * b = (a' - a) * b + a' * (b' - b) by ring, norm_mul]
    calc
      _ ≤ B * (‖(a' - a) * b‖ + ‖a' * (b' - b)‖) :=
        mul_le_mul hu (norm_add_le _ _) (norm_nonneg _) hB.le
      _ ≤ B * (R * R * R + R * (R * R)) := by
        apply mul_le_mul_of_nonneg_left _ hB.le
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul hda hb (norm_nonneg _) (mul_nonneg hR hR))
          (mul_le_mul ha' hdb (norm_nonneg _) hR)
      _ ≤ D / t ^ 3 := by
        rw [hR3]
        exact div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)

private def fourierConstant : ℝ := 17 * (4 : ℝ) ^ (4 ^ 8 : ℕ)

/-- Uniform upper bound for the modulus of a centered native-phase interval sum. -/
def fourierBound (c : ℕ) : ℝ := fourierConstant * (c : ℝ) ^ (15 / 16 : ℝ)

private theorem fourierConstant_pos : 0 < fourierConstant := by
  unfold fourierConstant
  positivity

private theorem norm_phaseMean_le (c : ℕ) [NeZero c] :
    ‖phaseMean c‖ ≤ 1 / (c : ℝ) := by
  rw [phaseMean_eq_sum_vacuumPhase, sum_vacuumPhase_eq_moebius c (NeZero.pos c),
    norm_div, Complex.norm_intCast, Complex.norm_natCast, ← Int.cast_abs]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := c))) (Nat.cast_nonneg c)

/-- Finite Abel summation on a consecutive interval written with its starting integer
and length. Every centered prefix uses the native incomplete Kloosterman estimate. -/
theorem norm_weighted_native_range_le (c : ℕ) [NeZero c] (A : ℤ) (L : ℕ) (w : ℤ → ℂ) :
    ‖∑ j ∈ Finset.range L, w (A + (j : ℤ)) * nativePhase c ((A + (j : ℤ) : ℤ) : ZMod c)‖ ≤
      fourierBound c *
        (‖w (A + ((L - 1 : ℕ) : ℤ))‖ +
          ∑ j ∈ Finset.range (L - 1), ‖w (A + (j : ℤ) + 1) - w (A + (j : ℤ))‖) +
        (1 / (c : ℝ)) * ∑ j ∈ Finset.range L, ‖w (A + (j : ℤ))‖ := by
  let f (j : ℕ) := w (A + (j : ℤ))
  let g (j : ℕ) := centeredPhase c ((A + (j : ℤ) : ℤ) : ZMod c)
  have hF : 0 ≤ fourierBound c :=
    mul_nonneg fourierConstant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg c) _)
  have hprefix (l : ℕ) : ‖∑ j ∈ Finset.range l, g j‖ ≤ fourierBound c := by
    have h := norm_sum_centeredPhase_Ico_le c A (A + (l : ℤ))
    rw [Int.Ico_eq_finset_map, Finset.sum_map,
      show (A + (l : ℤ) - A).toNat = l by omega] at h
    simpa only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply,
      g, centeredPhase, fourierBound, fourierConstant] using h
  have hparts := Finset.sum_range_by_parts f g L
  simp only [smul_eq_mul] at hparts
  have hcenter : ‖∑ j ∈ Finset.range L, f j * g j‖ ≤
      fourierBound c * (‖f (L - 1)‖ + ∑ j ∈ Finset.range (L - 1), ‖f (j + 1) - f j‖) := by
    rw [hparts]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, mul_add, Finset.mul_sum]
    apply add_le_add
    · rw [mul_comm (fourierBound c)]
      exact mul_le_mul_of_nonneg_left (hprefix L) (norm_nonneg _)
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul, mul_comm (fourierBound c)]
      exact mul_le_mul_of_nonneg_left (hprefix (j + 1)) (norm_nonneg _)
  have hmean : ‖∑ j ∈ Finset.range L, f j * phaseMean c‖ ≤
      (1 / (c : ℝ)) * ∑ j ∈ Finset.range L, ‖f j‖ := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, mul_comm (1 / (c : ℝ))]
    exact mul_le_mul_of_nonneg_left (norm_phaseMean_le c) (norm_nonneg _)
  have hsplit (j : ℕ) :
      w (A + (j : ℤ)) * nativePhase c ((A + (j : ℤ) : ℤ) : ZMod c) =
        f j * g j + f j * phaseMean c := by
    simp only [f, g, centeredPhase]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib]
  simpa only [f, Nat.cast_add, Nat.cast_one, add_assoc] using
    (norm_add_le _ _).trans (add_le_add hcenter hmean)

private def row (c : ℕ) [NeZero c] (A B : ℤ) (τ : ℍ) : ℂ :=
  ∑ d ∈ Finset.Ico A B, anchoredWeight (c : ℤ) d τ * nativePhase c (d : ZMod c)

/-- The weight summed over an interval of length at most `2c`, using the scale `c`. -/
private theorem norm_row_short_le {D : ℝ} (hD : 0 < D)
    (c : ℕ) [NeZero c] (A B : ℤ) (τ : ℍ) (hlen : (B - A).toNat ≤ 2 * c)
    (hw : ∀ d : ℤ, ‖anchoredWeight (c : ℤ) d τ‖ ≤ D / (c : ℝ) ^ 2)
    (hd : ∀ d : ℤ, ‖anchoredWeight (c : ℤ) (d + 1) τ -
      anchoredWeight (c : ℤ) d τ‖ ≤ D / (c : ℝ) ^ 3) :
    ‖row c A B τ‖ ≤
      fourierBound c * (3 * D / (c : ℝ) ^ 2) + 2 * D / (c : ℝ) ^ 2 := by
  let L := (B - A).toNat
  let w := fun d => anchoredWeight (c : ℤ) d τ
  have hc : 0 < (c : ℝ) := Nat.cast_pos.mpr (NeZero.pos c)
  have hL : (L : ℝ) ≤ 2 * (c : ℝ) := by exact_mod_cast hlen
  have hL' : ((L - 1 : ℕ) : ℝ) ≤ 2 * (c : ℝ) :=
    (Nat.cast_le.mpr (Nat.sub_le _ _)).trans hL
  have hvar : (∑ j ∈ Finset.range (L - 1), ‖w (A + (j : ℤ) + 1) - w (A + (j : ℤ))‖)
      ≤ 2 * D / (c : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (L - 1), D / (c : ℝ) ^ 3 :=
        Finset.sum_le_sum fun j _ => hd (A + (j : ℤ))
      _ ≤ (2 * (c : ℝ)) * (D / (c : ℝ) ^ 3) := by
        simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
          mul_le_mul_of_nonneg_right hL' (by positivity : 0 ≤ D / (c : ℝ) ^ 3)
      _ = _ := by field_simp [hc.ne']
  have hmass : (∑ j ∈ Finset.range L, ‖w (A + (j : ℤ))‖)
      ≤ 2 * D / (c : ℝ) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range L, D / (c : ℝ) ^ 2 :=
        Finset.sum_le_sum fun j _ => hw (A + (j : ℤ))
      _ ≤ (2 * (c : ℝ)) * (D / (c : ℝ) ^ 2) := by
        simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
          mul_le_mul_of_nonneg_right hL (by positivity : 0 ≤ D / (c : ℝ) ^ 2)
      _ = _ := by field_simp [hc.ne']
  have hF : 0 ≤ fourierBound c := mul_nonneg fourierConstant_pos.le
    (Real.rpow_nonneg hc.le _)
  unfold row
  rw [Int.Ico_eq_finset_map, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
  refine (norm_weighted_native_range_le c A L w).trans ?_
  have he : ‖w (A + ((L - 1 : ℕ) : ℤ))‖ + 2 * D / (c : ℝ) ^ 2 ≤
      3 * D / (c : ℝ) ^ 2 := by
    calc
      _ ≤ D / (c : ℝ) ^ 2 + 2 * D / (c : ℝ) ^ 2 := add_le_add_left (hw _) _
      _ = _ := by ring
  refine add_le_add (mul_le_mul_of_nonneg_left ((add_le_add_right hvar _).trans he) hF) ?_
  calc
    _ ≤ (1 / (c : ℝ)) * (2 * D / (c : ℝ)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

private def reciprocalPotential (d : ℤ) : ℝ := -1 / (d : ℝ)

private theorem potential_step {d : ℤ} (h₀ : 1 ≤ |d|) (h₁ : 1 ≤ |d + 1|) :
    0 < (d : ℝ) * ((d + 1 : ℤ) : ℝ) ∧
    (d : ℝ) * ((d + 1 : ℤ) : ℝ) ≤
      2 * (min |(d : ℝ)| |((d + 1 : ℤ) : ℝ)|) ^ 2 ∧
    reciprocalPotential (d + 1) - reciprocalPotential d =
      1 / ((d : ℝ) * ((d + 1 : ℤ) : ℝ)) := by
  have hsign : 1 ≤ d ∨ d + 1 ≤ -1 := by
    rcases le_or_gt 0 d with hd | hd
    · left
      rwa [abs_of_nonneg hd] at h₀
    · right
      have hd' : d + 1 ≤ 0 := by omega
      rw [abs_of_nonpos hd'] at h₁
      omega
  have hprod : 0 < (d : ℝ) * ((d + 1 : ℤ) : ℝ) := by
    rcases hsign with h | h
    · exact mul_pos (by exact_mod_cast (show 0 < d by omega))
        (by exact_mod_cast (show 0 < d + 1 by omega))
    · exact mul_pos_of_neg_of_neg (by exact_mod_cast (show d < 0 by omega))
        (by exact_mod_cast (show d + 1 < 0 by omega))
  refine ⟨hprod, ?_, ?_⟩
  · push_cast
    rcases hsign with h | h
    · have hd : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith : 0 ≤ (d : ℝ)),
        abs_of_nonneg (by linarith : 0 ≤ (d : ℝ) + 1),
        min_eq_left (by linarith : (d : ℝ) ≤ (d : ℝ) + 1)]
      nlinarith [mul_nonneg (by linarith : 0 ≤ (d : ℝ)) (sub_nonneg.mpr hd)]
    · have hd : (d : ℝ) + 1 ≤ -1 := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith : (d : ℝ) ≤ 0),
        abs_of_nonpos (by linarith : (d : ℝ) + 1 ≤ 0),
        min_eq_right (by linarith : -((d : ℝ) + 1) ≤ -(d : ℝ))]
      nlinarith [mul_nonneg (by linarith : 0 ≤ -((d : ℝ) + 1))
        (by linarith : 0 ≤ -((d : ℝ) + 1) - 1)]
  · have hd : (d : ℝ) ≠ 0 := (mul_ne_zero_iff.mp hprod.ne').1
    have hd' : ((d + 1 : ℤ) : ℝ) ≠ 0 := (mul_ne_zero_iff.mp hprod.ne').2
    unfold reciprocalPotential
    field_simp [hd, hd']
    push_cast
    ring

private theorem norm_row_far_le {D : ℝ} (hD : 0 < D)
    (c : ℕ) [NeZero c] (N : ℕ) (hN : 2 ≤ N) (A B : ℤ) (τ : ℍ)
    (hfar : ∀ d ∈ Finset.Ico A B, (N : ℤ) ≤ |d|)
    (hclose : ∀ j ≤ (B - A).toNat, (N : ℤ) - 1 ≤ |A + (j : ℤ)|)
    (hb : ∀ (d : ℤ) (t : ℝ), 0 < t → t ≤ max (c : ℝ) |(d : ℝ)| →
      ‖anchoredWeight (c : ℤ) d τ‖ ≤ D / t ^ 2 ∧
        (t ≤ max (c : ℝ) |((d + 1 : ℤ) : ℝ)| →
          ‖anchoredWeight (c : ℤ) (d + 1) τ - anchoredWeight (c : ℤ) d τ‖ ≤ D / t ^ 3)) :
    ‖row c A B τ‖ ≤
      fourierBound c * (9 * D / (N : ℝ) ^ 2) + 8 * D / ((c : ℝ) * (N : ℝ)) := by
  let L := (B - A).toNat
  let w := fun d => anchoredWeight (c : ℤ) d τ
  let e (j : ℕ) : ℤ := A + (j : ℤ)
  let P (j : ℕ) : ℝ := reciprocalPotential (e j)
  have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn : 0 < (N : ℝ) := by linarith
  have hc : 0 < (c : ℝ) := Nat.cast_pos.mpr (NeZero.pos c)
  have he (j : ℕ) : e (j + 1) = e j + 1 := by simp [e, add_assoc]
  have hnear (j : ℕ) (hj : j ≤ L) : (N : ℝ) - 1 ≤ |(e j : ℝ)| := by
    exact_mod_cast (hclose j hj)
  have hfar' (j : ℕ) (hj : j < L) : (N : ℝ) ≤ |(e j : ℝ)| := by
    have hm : e j ∈ Finset.Ico A B := by
      have hj' : j < (B - A).toNat := hj
      simp only [Finset.mem_Ico, e]
      omega
    exact_mod_cast hfar (e j) hm
  have hP (j : ℕ) (hj : j ≤ L) : |P j| ≤ 2 / (N : ℝ) := by
    have hx : 0 < |(e j : ℝ)| := by linarith [hnear j hj]
    change |(-1 : ℝ) / (e j : ℝ)| ≤ _
    rw [abs_div, abs_neg, abs_one]
    apply (div_le_div_iff₀ hx hn).mpr
    linarith [hnear j hj]
  have htel (l : ℕ) (hl : l ≤ L) :
      (∑ j ∈ Finset.range l, (P (j + 1) - P j)) ≤ 4 / (N : ℝ) := by
    rw [Finset.sum_range_sub]
    have hlast := (abs_le.mp (hP l hl)).2
    have hfirst := (abs_le.mp (hP 0 (Nat.zero_le _))).1
    calc
      _ ≤ 2 / (N : ℝ) - -(2 / (N : ℝ)) := sub_le_sub hlast hfirst
      _ = _ := by ring
  have hstep (j : ℕ) (hj : j < L) :
      let t := min |(e j : ℝ)| |(e (j + 1) : ℝ)|
      0 < t ∧ 1 / t ^ 2 ≤ 2 * (P (j + 1) - P j) := by
    dsimp only
    have h₀ : 1 ≤ |e j| := by
      exact_mod_cast (show (1 : ℝ) ≤ |(e j : ℝ)| by linarith [hnear j hj.le])
    have h₁ : 1 ≤ |e j + 1| := by
      rw [← he]
      exact_mod_cast (show (1 : ℝ) ≤ |(e (j + 1) : ℝ)| by
        linarith [hnear (j + 1) (Nat.succ_le_of_lt hj)])
    obtain ⟨hp, hprod, hpot⟩ := potential_step h₀ h₁
    have ht : 0 < min |(e j : ℝ)| |(e (j + 1) : ℝ)| :=
      lt_min (by linarith [hnear j hj.le]) (by linarith [hnear (j + 1) (Nat.succ_le_of_lt hj)])
    refine ⟨ht, ?_⟩
    change 1 / (min |(e j : ℝ)| |(e (j + 1) : ℝ)|) ^ 2 ≤
      2 * (reciprocalPotential (e (j + 1)) - reciprocalPotential (e j))
    rw [he, hpot, ← mul_div_assoc, mul_one]
    have ht' : 0 < (min |(e j : ℝ)| |(e (j + 1) : ℝ)|) ^ 2 := pow_pos ht 2
    refine (div_le_div_iff₀ (by simpa only [he] using ht') hp).mpr ?_
    simpa only [one_mul] using hprod
  have hmassStep (j : ℕ) (hj : j ∈ Finset.range L) :
      ‖w (e j)‖ ≤ (2 * D) * (P (j + 1) - P j) := by
    let t := min |(e j : ℝ)| |(e (j + 1) : ℝ)|
    obtain ⟨ht, hs⟩ := hstep j (Finset.mem_range.mp hj)
    calc
      _ ≤ D / t ^ 2 := (hb (e j) t ht ((min_le_left _ _).trans (le_max_right _ _))).1
      _ = D * (1 / t ^ 2) := by ring
      _ ≤ D * (2 * (P (j + 1) - P j)) := mul_le_mul_of_nonneg_left hs hD.le
      _ = _ := by ring
  have hvarStep (j : ℕ) (hj : j ∈ Finset.range (L - 1)) :
      ‖w (e j + 1) - w (e j)‖ ≤ (2 * D / (N : ℝ)) * (P (j + 1) - P j) := by
    have hj' : j + 1 < L := by have := Finset.mem_range.mp hj; omega
    let t := min |(e j : ℝ)| |(e (j + 1) : ℝ)|
    obtain ⟨ht, hs⟩ := hstep j (Nat.lt_of_succ_lt hj')
    have hnt : (N : ℝ) ≤ t := le_min (hfar' j (Nat.lt_of_succ_lt hj')) (hfar' (j + 1) hj')
    have hd := (hb (e j) t ht ((min_le_left _ _).trans (le_max_right _ _))).2
      (by rw [← he]; exact (min_le_right _ _).trans (le_max_right _ _))
    calc
      _ ≤ D / t ^ 3 := hd
      _ = (D / t) * (1 / t ^ 2) := by ring
      _ ≤ (D / (N : ℝ)) * (1 / t ^ 2) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hD.le hn hnt) (by positivity)
      _ ≤ (D / (N : ℝ)) * (2 * (P (j + 1) - P j)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have hmass : (∑ j ∈ Finset.range L, ‖w (e j)‖) ≤ 8 * D / (N : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range L, (2 * D) * (P (j + 1) - P j) := Finset.sum_le_sum hmassStep
      _ ≤ (2 * D) * (4 / (N : ℝ)) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (htel L le_rfl) (by positivity)
      _ = _ := by ring
  have hvar : (∑ j ∈ Finset.range (L - 1), ‖w (e j + 1) - w (e j)‖)
      ≤ 8 * D / (N : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range (L - 1), (2 * D / (N : ℝ)) * (P (j + 1) - P j) :=
        Finset.sum_le_sum hvarStep
      _ ≤ (2 * D / (N : ℝ)) * (4 / (N : ℝ)) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (htel (L - 1) (Nat.sub_le _ _)) (by positivity)
      _ = _ := by ring
  have hF : 0 ≤ fourierBound c := mul_nonneg fourierConstant_pos.le (Real.rpow_nonneg hc.le _)
  unfold row
  rw [Int.Ico_eq_finset_map, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
  by_cases hL : L = 0
  · rw [show (B - A).toNat = 0 from hL, Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  · refine (norm_weighted_native_range_le c A L w).trans ?_
    have hend : ‖w (e (L - 1))‖ ≤ D / (N : ℝ) ^ 2 :=
      (hb _ _ hn ((hfar' _ (by omega)).trans (le_max_right _ _))).1
    have hvar' : ‖w (e (L - 1))‖ +
        (∑ j ∈ Finset.range (L - 1), ‖w (e j + 1) - w (e j)‖) ≤ 9 * D / (N : ℝ) ^ 2 :=
      (add_le_add hend hvar).trans_eq (by ring)
    refine add_le_add (mul_le_mul_of_nonneg_left hvar' hF) ?_
    calc
      _ ≤ (1 / (c : ℝ)) * (8 * D / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := by ring

/-- The primitive positive rows in the literal transposed rectangle. -/
def transposedPairs (N : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Ioo 0 ((N : ℤ) ^ 2)).product (Finset.Ioo (-(N : ℤ)) (N : ℤ))).filter
    fun p => Int.gcd p.1 p.2 = 1

theorem mem_transposedPairs {N : ℕ} {c d : ℤ} :
    (c, d) ∈ transposedPairs N ↔
      0 < c ∧ c < (N : ℤ) ^ 2 ∧ |d| < (N : ℤ) ∧ Int.gcd c d = 1 := by
  simp only [transposedPairs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Ioo,
    abs_lt]
  tauto

/-- The linear contribution of a finite set of rows after subtraction at `i`. -/
def anchoredLinearSum (s : Finset (ℤ × ℤ)) (τ : ℍ) : ℂ :=
  ∑ p ∈ s, (linearSummand p.1 p.2 τ - linearSummand p.1 p.2 UpperHalfPlane.I)

private def positiveRow : ℕ ↪ ℤ where
  toFun k := ((k + 1 : ℕ) : ℤ)
  inj' := by
    intro x y h
    change ((x + 1 : ℕ) : ℤ) = ((y + 1 : ℕ) : ℤ) at h
    omega

private def primitiveRectangle (s : Finset ℕ) (J : Finset ℤ) : Finset (ℤ × ℤ) :=
  ((s.map positiveRow).product J).filter fun p => Int.gcd p.1 p.2 = 1

private theorem mem_primitiveRectangle {s : Finset ℕ} {J : Finset ℤ} {c d : ℤ} :
    (c, d) ∈ primitiveRectangle s J ↔
      (∃ k ∈ s, ((k + 1 : ℕ) : ℤ) = c) ∧ d ∈ J ∧ Int.gcd c d = 1 := by
  simp only [primitiveRectangle, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_map,
    and_assoc]
  rfl

private theorem nativePhase_eq_zero_of_not_primitive (c : ℕ) [NeZero c] (d : ℤ)
    (h : Int.gcd (c : ℤ) d ≠ 1) : nativePhase c (d : ZMod c) = 0 := by
  unfold nativePhase
  apply ite_eq_right
  rwa [Nat.coprime_iff_gcd_eq_one, ← Int.gcd_natCast_natCast, ZMod.val_intCast,
    Int.gcd_emod, Int.gcd_comm d (c : ℤ)]

private theorem anchoredLinearSum_primitiveRectangle (s : Finset ℕ) (J : Finset ℤ) (τ : ℍ) :
    anchoredLinearSum (primitiveRectangle s J) τ =
      ∑ k ∈ s, ∑ d ∈ J,
        anchoredWeight ((k + 1 : ℕ) : ℤ) d τ * nativePhase (k + 1) (d : ZMod (k + 1)) := by
  rw [anchoredLinearSum, primitiveRectangle, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product,
    Finset.sum_map]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun d _ => ?_))
  change (if Int.gcd ((k + 1 : ℕ) : ℤ) d = 1 then
    linearSummand ((k + 1 : ℕ) : ℤ) d τ -
      linearSummand ((k + 1 : ℕ) : ℤ) d UpperHalfPlane.I else 0) = _
  by_cases hd : Int.gcd ((k + 1 : ℕ) : ℤ) d = 1
  · rw [ite_eq_left hd, linearSummand_sub_anchor (by omega),
      nativePhase_intCast_of_gcd_eq_one ((Int.gcd_comm _ _).trans hd), mul_comm]
  · rw [ite_eq_right hd, nativePhase_eq_zero_of_not_primitive _ _ hd, mul_zero]

/-- The positive moduli in the transposed-only strip, indexed by their predecessors. -/
def shortIndices (N : ℕ) := Finset.Ico (N - 1) (N ^ 2 - 1)
/-- The positive moduli in the original-only strip, indexed by their predecessors. -/
def longIndices (N : ℕ) := Finset.range (N - 1)
private def shortInterval (N : ℕ) := Finset.Ico (-(N : ℤ) + 1) (N : ℤ)
private def positiveInterval (N : ℕ) := Finset.Ico (N : ℤ) ((N : ℤ) ^ 2)
private def negativeInterval (N : ℕ) := Finset.Ico (-((N : ℤ) ^ 2) + 1) (-(N : ℤ) + 1)

private theorem shortStrip_eq {N : ℕ} (hN : 2 ≤ N) :
    transposedPairs N \ cutoffPairs N = primitiveRectangle (shortIndices N) (shortInterval N) := by
  apply Finset.ext
  rintro ⟨c, d⟩
  simp only [Finset.mem_sdiff, mem_transposedPairs, mem_cutoffPairs, mem_primitiveRectangle,
    shortIndices, shortInterval, Finset.mem_Ico, abs_lt]
  have hsq : (N : ℤ) ≤ (N : ℤ) ^ 2 := Int.le_self_sq _
  have hcast : ((N ^ 2 : ℕ) : ℤ) = (N : ℤ) ^ 2 := Nat.cast_pow N 2
  constructor
  · rintro ⟨⟨hc, hc₂, hd, hp⟩, hnot⟩
    have hc₁ : (N : ℤ) ≤ c := by
      by_contra! hc₁
      exact hnot ⟨hc, hc₁, by omega, hp⟩
    refine ⟨⟨(c - 1).toNat, ?_, by omega⟩, by omega, hp⟩
    omega
  · rintro ⟨⟨k, hk, rfl⟩, hd, hp⟩
    exact ⟨⟨by omega, by omega, by omega, hp⟩, by omega⟩

private theorem longStrip_eq {N : ℕ} (hN : 2 ≤ N) :
    cutoffPairs N \ transposedPairs N =
      primitiveRectangle (longIndices N) (positiveInterval N ∪ negativeInterval N) := by
  apply Finset.ext
  rintro ⟨c, d⟩
  simp only [Finset.mem_sdiff, mem_transposedPairs, mem_cutoffPairs, mem_primitiveRectangle,
    longIndices, positiveInterval, negativeInterval, Finset.mem_range, Finset.mem_union,
    Finset.mem_Ico, abs_lt]
  have hsq : (N : ℤ) ≤ (N : ℤ) ^ 2 := Int.le_self_sq _
  constructor
  · rintro ⟨⟨hc, hc₁, hd, hp⟩, hnot⟩
    have hd' : ¬ (-(N : ℤ) < d ∧ d < (N : ℤ)) := by
      intro ht
      exact hnot ⟨hc, hc₁.trans_le hsq, ht, hp⟩
    exact ⟨⟨(c - 1).toNat, by omega, by omega⟩, by omega, hp⟩
  · rintro ⟨⟨k, hk, rfl⟩, hd, hp⟩
    exact ⟨⟨by omega, by omega, by omega, hp⟩, by omega⟩

/-- Row majorant for the transposed-only strip. -/
def shortBound (D : ℝ) (c : ℕ) : ℝ :=
  fourierBound c * (3 * D / (c : ℝ) ^ 2) + 2 * D / (c : ℝ) ^ 2

/-- Row majorant for the original-only strip, including both signs of the denominator. -/
def longBound (D : ℝ) (N c : ℕ) : ℝ :=
  2 * (fourierBound c * (9 * D / (N : ℝ) ^ 2) + 8 * D / ((c : ℝ) * (N : ℝ)))

/-- Simultaneous compact-uniform quantitative estimates for the two literal differences. -/
theorem norm_anchoredLinearSum_strips_le {K : Set ℍ} (hK : IsCompact K) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, 2 ≤ N → ∀ τ ∈ K,
      ‖anchoredLinearSum (transposedPairs N \ cutoffPairs N) τ‖ ≤
        ∑ k ∈ shortIndices N, shortBound D (k + 1) ∧
      ‖anchoredLinearSum (cutoffPairs N \ transposedPairs N) τ‖ ≤
        ∑ k ∈ longIndices N, longBound D N (k + 1) := by
  obtain ⟨D, hD, hbound⟩ := anchoredWeight_compact_bounds hK
  refine ⟨D, hD, ?_⟩
  intro N hN τ hτ
  have hsq : (N : ℤ) ≤ (N : ℤ) ^ 2 := Int.le_self_sq _
  have hcast : ((N ^ 2 : ℕ) : ℤ) = (N : ℤ) ^ 2 := Nat.cast_pow N 2
  constructor
  · rw [shortStrip_eq hN, anchoredLinearSum_primitiveRectangle]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hk' : N ≤ k + 1 := by
      have := (Finset.mem_Ico.mp hk).1
      omega
    have hc : 0 < ((k + 1 : ℕ) : ℤ) := by omega
    have hcr : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
    have hw (d : ℤ) := hbound τ hτ ((k + 1 : ℕ) : ℤ) d ((k + 1 : ℕ) : ℝ) hc hcr
      (by push_cast; exact le_max_left _ _)
    have hlen : ((N : ℤ) - (-(N : ℤ) + 1)).toNat ≤ 2 * (k + 1) := by omega
    exact norm_row_short_le hD (k + 1) _ _ τ hlen
      (fun d => (hw d).1) (fun d => (hw d).2 (by push_cast; exact le_max_left _ _))
  · rw [longStrip_eq hN, anchoredLinearSum_primitiveRectangle]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have hd : Disjoint (positiveInterval N) (negativeInterval N) := by
      rw [Finset.disjoint_left]
      intro d hp hn
      simp only [positiveInterval, negativeInterval, Finset.mem_Ico] at hp hn
      omega
    rw [Finset.sum_union hd]
    refine (norm_add_le _ _).trans ?_
    have hb (d : ℤ) (t : ℝ) (ht : 0 < t) (h : t ≤ max ((k + 1 : ℕ) : ℝ) |(d : ℝ)|) :=
      hbound τ hτ ((k + 1 : ℕ) : ℤ) d t (by omega) ht (by simpa only [Int.cast_natCast] using h)
    have hp := norm_row_far_le hD (k + 1) N hN (N : ℤ) ((N : ℤ) ^ 2) τ
      (fun d hd => by
        have h := (Finset.mem_Ico.mp hd).1
        rwa [abs_of_nonneg (by omega)])
      (fun j _ => by rw [abs_of_nonneg (by omega)]; omega) hb
    have hn := norm_row_far_le hD (k + 1) N hN (-((N : ℤ) ^ 2) + 1) (-(N : ℤ) + 1) τ
      (fun d hd => by
        have h := (Finset.mem_Ico.mp hd).2
        rw [abs_of_nonpos (by omega)]
        omega)
      (fun j hj => by
        have h : -((N : ℤ) ^ 2) + 1 + (j : ℤ) ≤ -(N : ℤ) + 1 := by omega
        rw [abs_of_nonpos (by omega)]
        omega) hb
    exact (add_le_add hp hn).trans_eq (by unfold longBound; ring)

private theorem fourierBound_div_sq (c : ℕ) (hc : 0 < c) :
    fourierBound c / (c : ℝ) ^ 2 = fourierConstant * (c : ℝ) ^ (-(17 / 16) : ℝ) := by
  have hcr : 0 < (c : ℝ) := Nat.cast_pos.mpr hc
  rw [fourierBound, mul_div_assoc, ← Real.rpow_natCast _ 2, ← Real.rpow_sub hcr,
    show (15 / 16 : ℝ) - ((2 : ℕ) : ℝ) = -(17 / 16) by norm_num]

private theorem summable_stripMajorant (A B : ℝ) :
    Summable (fun k : ℕ => A * ((k + 1 : ℕ) : ℝ) ^ (-(17 / 16) : ℝ) +
      B * (1 / ((k + 1 : ℕ) : ℝ) ^ 2)) := by
  have h₁ : Summable (fun k : ℕ => (k : ℝ) ^ (-(17 / 16) : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have h₂ : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  exact (summable_nat_add_iff 1).2 ((h₁.mul_left A).add (h₂.mul_left B))

private theorem tendsto_shortStrip_bound_zero {D : ℝ} (hD : 0 < D) :
    Tendsto (fun N => ∑ k ∈ shortIndices N, shortBound D (k + 1)) atTop (𝓝 0) := by
  let f (N k : ℕ) := if k ∈ shortIndices N then shortBound D (k + 1) else 0
  have hsum : Summable (fun k : ℕ => shortBound D (k + 1)) := by
    convert summable_stripMajorant (3 * D * fourierConstant) (2 * D) using 1
    ext k
    unfold shortBound
    rw [show fourierBound (k + 1) * (3 * D / ((k + 1 : ℕ) : ℝ) ^ 2) =
      (3 * D) * (fourierBound (k + 1) / ((k + 1 : ℕ) : ℝ) ^ 2) by ring,
      fourierBound_div_sq _ (Nat.succ_pos k)]
    ring
  have hpt (k : ℕ) : Tendsto (f · k) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (k + 2)] with N hN
    have hk : k ∉ shortIndices N := by
      simp only [shortIndices, Finset.mem_Ico]
      omega
    simp [f, hk]
  have hdom : ∀ᶠ N in atTop, ∀ k, ‖f N k‖ ≤ shortBound D (k + 1) := by
    refine Eventually.of_forall fun N k => ?_
    have hnon : 0 ≤ shortBound D (k + 1) := by
      unfold shortBound fourierBound
      exact add_nonneg (mul_nonneg (mul_nonneg fourierConstant_pos.le
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by positivity)) (by positivity)
    by_cases hk : k ∈ shortIndices N <;> simp [f, hk, Real.norm_of_nonneg hnon, hnon]
  have h := tendsto_tsum_of_dominated_convergence hsum hpt hdom
  have heq (N : ℕ) : (∑' k, f N k) = ∑ k ∈ shortIndices N, shortBound D (k + 1) := by
    rw [tsum_eq_sum (s := shortIndices N) (fun k hk => by simp [f, hk])]
    exact Finset.sum_congr rfl (fun k hk => by simp [f, hk])
  simpa only [heq, tsum_zero] using h

private theorem norm_longBound_le {D : ℝ} (hD : 0 < D) (N c : ℕ) (hc : 0 < c)
    (hcN : c ≤ N) : ‖longBound D N c‖ ≤ longBound D c c := by
  have hc' : 0 < (c : ℝ) := Nat.cast_pos.mpr hc
  have hle : (c : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcN
  have hF : 0 ≤ fourierBound c :=
    mul_nonneg fourierConstant_pos.le (Real.rpow_nonneg hc'.le _)
  have hn : 0 ≤ longBound D N c := by unfold longBound; positivity
  rw [Real.norm_of_nonneg hn]
  unfold longBound
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ hc'.le hle 2)) hF
  · exact div_le_div_of_nonneg_left (by positivity) (mul_pos hc' hc')
      (mul_le_mul_of_nonneg_left hle hc'.le)

private theorem tendsto_longStrip_bound_zero {D : ℝ} (hD : 0 < D) :
    Tendsto (fun N => ∑ k ∈ longIndices N, longBound D N (k + 1)) atTop (𝓝 0) := by
  let f (N k : ℕ) := if k ∈ longIndices N then longBound D N (k + 1) else 0
  have hsum : Summable (fun k : ℕ => longBound D (k + 1) (k + 1)) := by
    convert summable_stripMajorant (18 * D * fourierConstant) (16 * D) using 1
    ext k
    unfold longBound
    rw [show fourierBound (k + 1) * (9 * D / ((k + 1 : ℕ) : ℝ) ^ 2) =
      (9 * D) * (fourierBound (k + 1) / ((k + 1 : ℕ) : ℝ) ^ 2) by ring,
      fourierBound_div_sq _ (Nat.succ_pos k)]
    ring
  have hpt (k : ℕ) : Tendsto (f · k) atTop (𝓝 0) := by
    have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_nhds_zero_nat
    have h := ((hi.pow 2).const_mul (fourierBound (k + 1) * (9 * D))).add
      (hi.const_mul (8 * D / ((k + 1 : ℕ) : ℝ)))
    have h' := h.const_mul (2 : ℝ)
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at h'
    refine h'.congr' ?_
    filter_upwards [eventually_ge_atTop (k + 2)] with N hN
    have hk : k ∈ longIndices N := by simp only [longIndices, Finset.mem_range]; omega
    simp only [f, hk, ite_eq_left, longBound, div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring
  have hdom : ∀ᶠ N in atTop, ∀ k, ‖f N k‖ ≤ longBound D (k + 1) (k + 1) := by
    refine Eventually.of_forall fun N k => ?_
    by_cases hk : k ∈ longIndices N
    · have hkN : k + 1 ≤ N := by
        simp only [longIndices, Finset.mem_range] at hk
        omega
      simpa only [f, ite_eq_left hk] using norm_longBound_le hD N (k + 1) (Nat.succ_pos k) hkN
    · simp only [f, ite_eq_right hk, norm_zero, longBound]
      have : 0 ≤ fourierBound (k + 1) :=
        mul_nonneg fourierConstant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      positivity
  have h := tendsto_tsum_of_dominated_convergence hsum hpt hdom
  have heq (N : ℕ) : (∑' k, f N k) = ∑ k ∈ longIndices N, longBound D N (k + 1) := by
    rw [tsum_eq_sum (s := longIndices N) (fun k hk => by simp [f, hk])]
    exact Finset.sum_congr rfl (fun k hk => by simp [f, hk])
  simpa only [heq, tsum_zero] using h

/-- Each of the two literal linear boundary strips vanishes uniformly on compact sets. -/
theorem tendstoUniformlyOn_anchoredLinearSum_strips {K : Set ℍ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun N => anchoredLinearSum (transposedPairs N \ cutoffPairs N))
        (fun _ => 0) atTop K ∧
      TendstoUniformlyOn (fun N => anchoredLinearSum (cutoffPairs N \ transposedPairs N))
        (fun _ => 0) atTop K := by
  obtain ⟨D, hD, hbound⟩ := norm_anchoredLinearSum_strips_le hK
  have hshort := (Metric.tendsto_nhds.mp (tendsto_shortStrip_bound_zero hD))
  have hlong := (Metric.tendsto_nhds.mp (tendsto_longStrip_bound_zero hD))
  constructor
  · refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    filter_upwards [eventually_ge_atTop 2, hshort ε hε] with N hN hs τ hτ
    rw [dist_comm, dist_eq_norm, sub_zero]
    exact ((hbound N hN τ hτ).1.trans (Real.le_norm_self _)).trans_lt
      (by simpa only [dist_eq_norm, sub_zero] using hs)
  · refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    filter_upwards [eventually_ge_atTop 2, hlong ε hε] with N hN hs τ hτ
    rw [dist_comm, dist_eq_norm, sub_zero]
    exact ((hbound N hN τ hτ).2.trans (Real.le_norm_self _)).trans_lt
      (by simpa only [dist_eq_norm, sub_zero] using hs)

end

end D5.S3.Arith.ModularForms.RademacherSLinearStrips
