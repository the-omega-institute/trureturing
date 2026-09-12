/- GID: D5/S3/Observer/GoldenPrimeCircle/GoldenClockCanonicalSection
   generality: G
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:exact-canonical-object-bridge)
   anchors: []
   digest: Identifies the alpha-cut lift with dev betaGolden; canonical and centered returns compose without carry, while old floor returns admit no common injective relabeling when their commutator is nonzero. -/

import D5.S3.Observer.GoldenPrimeCircle.GoldenClockSectionAlgebra
import D5.S3.Observer.GoldenPrimeCircle.GoldenClockComposition
import D5.S1.Deficit.Beatty.BetaBeattyClosedForms

set_option autoImplicit false

namespace D5.S3.Observer.GoldenPrimeCircle.GoldenClockCanonicalSection

open D5.S0.Carrier D5.S1.Scale D5.S1.Deficit
open D5.S1.Deficit.BetaBeattyClosedForms
open D5.S1.Deficit.ZeckendorfDisplacementReading
open GoldenClockLattice GoldenClockComposition GoldenClockSectionAlgebra

noncomputable section

def multiplier (L : ℕ) : GoldenInt := phi ^ (L + 2)
def layer (ρ : ℝ) (L : ℕ) (n : ℤ) : ℤ := projected (multiplier L) ρ n

lemma multiplier_coordinates (L : ℕ) :
    multiplier L = ⟨previous L, boundary L⟩ := by
  simpa [multiplier, previous, boundary, Nat.add_assoc] using
    golden_phi_pow_eq_fib_pair (L + 1)

lemma multiplier_internal (L : ℕ) : internal (multiplier L) = signedWidth L := by
  have hp : internal phi = Real.goldenConj := by simp [internal_apply, phi, angle]
  simp only [multiplier, map_pow, hp, signedWidth]

lemma multiplier_mul (K L : ℕ) : multiplier K * multiplier L = multiplier (K + L + 2) := by
  unfold multiplier
  rw [← pow_add]
  congr 1
  omega

lemma layer_formula (ρ : ℝ) (L : ℕ) (n : ℤ) :
    layer ρ L n = leading L * n + boundary L * select ρ n := by
  unfold layer projected
  rw [multiplier_coordinates]
  change previous L * n + boundary L * select ρ n + boundary L * n = _
  rw [leading_eq]
  ring

lemma layer_zero (L : ℕ) (n : ℤ) : layer 0 L n = entry L n := by
  rw [layer_formula]
  simp [select, entry, angle, alpha]

/-- All resolutions commute with one shared centered section, for every integer input. -/
theorem centered_layer_compose (K L : ℕ) (n : ℤ) :
    layer (1 / 2) K (layer (1 / 2) L n) = layer (1 / 2) (K + L + 2) n := by
  have hL : |internal (multiplier L)| ≤ 1 := by
    rw [multiplier_internal]
    exact le_of_lt (signedWidth_abs_lt_one L)
  unfold layer
  rw [centered_compose _ _ hL, multiplier_mul]

lemma alpha_sq_lt_alpha : alpha ^ 2 < alpha := by
  have hh : (1 / 2 : ℝ) < alpha := by
    by_contra h
    have hle : alpha ≤ 1 / 2 := le_of_not_gt h
    have hp := mul_nonneg (sub_nonneg.mpr hle) (le_of_lt alpha_pos)
    nlinarith [alpha_sq_add]
  nlinarith [alpha_sq_add]

lemma multiplier_internal_le_sq (L : ℕ) : |internal (multiplier L)| ≤ alpha ^ 2 := by
  rw [multiplier_internal, signedWidth_abs]
  change alpha ^ (L + 2) ≤ alpha ^ 2
  have hp : alpha ^ L ≤ 1 := by
    induction L with
    | zero => norm_num
    | succ L ih =>
        rw [pow_succ]
        calc
          _ ≤ 1 * alpha := mul_le_mul_of_nonneg_right ih (le_of_lt alpha_pos)
          _ ≤ 1 := by linarith [alpha_lt_one]
  rw [show L + 2 = 2 + L by omega, pow_add]
  simpa using mul_le_mul_of_nonneg_left hp (sq_nonneg alpha)

/-- The repository's canonical alpha-cut also has zero carry at every clock resolution. -/
theorem canonical_carry_zero (L : ℕ) (n : ℤ) : carry (multiplier L) angle n = 0 := by
  have hb := residual_bounds angle n
  change -alpha ≤ residual angle n ∧ residual angle n < 1 - alpha at hb
  have hr : |residual angle n| ≤ alpha := by
    apply abs_le.mpr
    exact ⟨hb.1, by linarith [alpha_sq_add, alpha_sq_lt_alpha]⟩
  have hprod : |internal (multiplier L) * residual angle n| < alpha ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ alpha ^ 2 * |residual angle n| :=
        mul_le_mul_of_nonneg_right (multiplier_internal_le_sq L) (abs_nonneg _)
      _ ≤ alpha ^ 2 * alpha := mul_le_mul_of_nonneg_left hr (sq_nonneg _)
      _ < alpha ^ 2 := by
        simpa using mul_lt_mul_of_pos_left alpha_lt_one (pow_pos alpha_pos 2)
  have ht := abs_lt.mp hprod
  rw [carry_eq_floor]
  apply Int.floor_eq_zero_iff.mpr
  change 0 ≤ internal (multiplier L) * residual angle n + alpha ∧
    internal (multiplier L) * residual angle n + alpha < 1
  constructor <;> linarith [alpha_sq_add, alpha_sq_lt_alpha]

theorem canonical_layer_compose (K L : ℕ) (n : ℤ) :
    layer angle K (layer angle L n) = layer angle (K + L + 2) n := by
  unfold layer
  rw [projected_compose, canonical_carry_zero, multiplier_mul]
  simp

theorem canonical_layer_commute (K L : ℕ) (n : ℤ) :
    layer angle K (layer angle L n) = layer angle L (layer angle K n) := by
  rw [canonical_layer_compose, canonical_layer_compose]
  congr 1
  omega

/-- Actual equality with the canonical object already used by dev's two-face theory. -/
theorem canonical_lift_eq_betaGolden (n : ℕ) : lift angle (n : ℤ) = betaGolden n := by
  have hs : (displacementDecode n : ℤ) = (n : ℤ) + select angle n := by
    rw [displacement_decode_eq_beatty_floor]
    have hx : ((n : ℝ) + 1) * Real.goldenRatio =
        (((n : ℤ) + 1 : ℤ) : ℝ) + ((n : ℝ) * angle + angle) := by
      push_cast
      dsimp [angle]
      linear_combination ((n : ℝ) + 1) * Real.goldenRatio_add_goldenConj
    rw [hx, Int.floor_intCast_add]
    simp only [select, Int.cast_natCast]
    ring
  have hsR : (displacementDecode n : ℝ) = (n : ℝ) + (select angle n : ℝ) := by
    exact_mod_cast hs
  apply embedding_injective
  change embedding (lift angle (n : ℤ)) = betaReal n
  rw [betaReal_eq_displacement_sub_goldenConj, embedding_apply, lift_a, lift_b, hsR]
  push_cast
  linear_combination (n : ℝ) * Real.goldenRatio_add_goldenConj

lemma canonical_layer_nonnegative (L n : ℕ) : 0 ≤ layer angle L (n : ℤ) := by
  rw [layer_formula]
  have ha : 0 < angle := alpha_pos
  have hs : 0 ≤ select angle (n : ℤ) := by
    unfold select
    apply Int.floor_nonneg.mpr
    positivity
  have hA : 0 ≤ leading L := by unfold leading; positivity
  have hB : 0 ≤ boundary L := by unfold boundary; positivity
  positivity

/-- A scale acts on the original canonical betaGolden objects, with the output index explicit. -/
theorem betaGolden_scale_covariance (L n : ℕ) :
    betaGolden (layer angle L (n : ℤ)).toNat = multiplier L * betaGolden n := by
  rw [← canonical_lift_eq_betaGolden,
    Int.toNat_of_nonneg (canonical_layer_nonnegative L n)]
  unfold layer
  rw [relift_defect, canonical_carry_zero, canonical_lift_eq_betaGolden]
  simp

/-- The earlier extra-return index uses a different input/output anchoring from the canonical shift. -/
theorem entry_as_anchored_canonical_shift (L : ℕ) (m : ℤ) :
    entry L m = leading L + layer angle L (m - 1) := by
  have hs : select angle (m - 1) = ⌊(m : ℝ) * alpha⌋ := by
    unfold select
    congr 1
    change ((m - 1 : ℤ) : ℝ) * alpha + alpha = (m : ℝ) * alpha
    push_cast
    ring
  rw [layer_formula, hs]
  unfold entry
  ring

/-- Restored commutation changes the measured maps. It cannot be achieved by one injective
relabeling intertwining an old noncommuting pair with the canonical commuting pair. -/
theorem no_common_injective_intertwiner (K L : ℕ)
    (hd : boundary L * cutCarry K - boundary K * cutCarry L ≠ 0) :
    ¬ ∃ f : ℤ → ℤ, Function.Injective f ∧
      (∀ n : ℤ, f (entry K n) = layer angle K (f n)) ∧
      (∀ n : ℤ, f (entry L n) = layer angle L (f n)) := by
  rintro ⟨f, hf, hK, hL⟩
  have he : f (entry K (entry L 1)) = f (entry L (entry K 1)) := by
    calc
      _ = layer angle K (f (entry L 1)) := hK _
      _ = layer angle K (layer angle L (f 1)) := by rw [hL]
      _ = layer angle L (layer angle K (f 1)) := canonical_layer_commute K L (f 1)
      _ = layer angle L (f (entry K 1)) := by rw [hK]
      _ = _ := (hL _).symm
  have ht := hf he
  have hc := entry_commutator K L (1 : ℤ) (by decide)
  rw [ht, sub_self] at hc
  exact hd hc.symm

end
end D5.S3.Observer.GoldenPrimeCircle.GoldenClockCanonicalSection
