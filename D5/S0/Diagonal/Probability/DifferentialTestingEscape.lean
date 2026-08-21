/- GID: D5/S0/Diagonal/Probability/DifferentialTestingEscape
   generality: G
   mirror-B: D5/B/S0/Diagonal/Probability/DifferentialTestingEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Uniform directories have the exact diagonal-mutation escape probability. -/

import D5.S0.Diagonal.EscapeCount
import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.Distributions.Uniform

open scoped ENNReal

universe u v

namespace D5.S0.Diagonal.Probability.DifferentialTestingEscape

open D5.S0.Diagonal.EscapeCount

noncomputable section

variable {A : Type u} {Y : Type v}

noncomputable instance directoryFintype [Fintype A] [Fintype Y] : Fintype (A → A → Y) := by
  classical
  infer_instance

example [Fintype A] [Fintype Y] : Fintype (A → A → Y) := inferInstance
example [Fintype A] [Fintype Y] [Nonempty Y] : Nonempty (A → A → Y) := inferInstance

/- The source directory `g : A → Y^A` is Lean's curried function `A → A → Y`.
   Its diagonal mutant is the output twist applied at each reference's own name. -/
def diagonalMutant (f : Y → Y) (g : A → A → Y) : A → Y :=
  fun a => f (g a a)

def directoryEscapes (f : Y → Y) (g : A → A → Y) : Prop :=
  diagonalMutant f g ∉ Set.range g

def directoryEscapeProbability [Fintype A] [Fintype Y] [Nonempty Y]
    (f : Y → Y) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (A → A → Y)).toOuterMeasure
    {g | directoryEscapes f g}

theorem directoryEscapes_iff_isEscaped (f : Y → Y) (g : A → A → Y) :
    directoryEscapes f g ↔ IsEscaped f g := by
  rfl

/- TASK D5-T0048
   The source's reference directory is finite and sampled uniformly. The
   existing EscapeCount theorem counts exactly the same self-application
   directories, so this bridge exposes the source notation without reproving
   the finite diagonal count. -/
theorem directory_escape_probability_exact [Fintype A] [Fintype Y] [Nonempty Y]
    (f : Y → Y) :
    directoryEscapeProbability (A := A) f =
      (1 - (Nat.card {y : Y // f y = y} : ℝ≥0∞) /
          (Fintype.card Y : ℝ≥0∞) ^ Fintype.card A) ^ Fintype.card A := by
  classical
  cases isEmpty_or_nonempty A with
  | inl hA =>
      letI : IsEmpty A := hA
      have hcardA : Fintype.card A = 0 := Fintype.card_eq_zero_iff.mpr hA
      rw [hcardA]
      simp [directoryEscapeProbability, PMF.toOuterMeasure_uniformOfFintype_apply,
        directoryEscapes, diagonalMutant, escaped_listing_card, Nat.card_eq_fintype_card]
  | inr hA =>
      letI : Nonempty A := hA
      rw [directoryEscapeProbability, PMF.toOuterMeasure_uniformOfFintype_apply]
      have hEscapedCard :
          Fintype.card
              ↥({g | directoryEscapes f g} : Set (A → A → Y)) =
            Nat.card {g : A → A → Y // IsEscaped f g} := by
        rw [Nat.card_eq_fintype_card]
        apply Fintype.card_congr
        exact Equiv.setCongr (by
          ext g
          exact directoryEscapes_iff_isEscaped f g)
      have hTotalCard :
          Fintype.card (A → A → Y) = Nat.card (A → A → Y) :=
        Nat.card_eq_fintype_card.symm
      rw [hEscapedCard, hTotalCard]
      change
        (Nat.card {g : A → A → Y // IsEscaped f g} : ℝ≥0∞) /
            (Nat.card (A → A → Y) : ℝ≥0∞) = _
      rw [escaped_listing_card]
      have hden :
          Fintype.card (A → A → Y) =
            Fintype.card Y ^ (Fintype.card A * Fintype.card A) := by
        classical
        rw [Fintype.card_fun, Fintype.card_fun]
        rw [← pow_mul]
      simp only [Nat.card_eq_fintype_card]
      rw [hden]
      simp only [Nat.cast_pow, ENNReal.natCast_sub]
      have hbase : (Fintype.card Y : ℝ≥0∞) ^ Fintype.card A ≠ 0 := by
        exact pow_ne_zero _
          (Nat.cast_ne_zero.mpr (Nat.ne_of_gt Fintype.card_pos))
      have hrewrite :
          ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card A -
              (Fintype.card {y : Y // f y = y} : ℝ≥0∞)) /
              (Fintype.card Y : ℝ≥0∞) ^ Fintype.card A =
            1 - (Fintype.card {y : Y // f y = y} : ℝ≥0∞) /
              (Fintype.card Y : ℝ≥0∞) ^ Fintype.card A := by
        rw [ENNReal.sub_div (by intro _ _; exact hbase)]
        rw [ENNReal.div_self hbase (by simp)]
      have hdivpow (a b : ℝ≥0∞) (n : Nat) :
          a ^ n / b ^ n = (a / b) ^ n := by
        calc
          a ^ n / b ^ n = (b ^ n)⁻¹ * a ^ n := ENNReal.div_eq_inv_mul
          _ = (b⁻¹) ^ n * a ^ n := by rw [ENNReal.inv_pow]
          _ = (b⁻¹ * a) ^ n := by rw [mul_pow]
          _ = (a / b) ^ n := by rw [ENNReal.div_eq_inv_mul]
      calc
        ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card A -
            (Fintype.card {y : Y // f y = y} : ℝ≥0∞)) ^ Fintype.card A /
            (Fintype.card Y : ℝ≥0∞) ^ (Fintype.card A * Fintype.card A) =
            (((Fintype.card Y : ℝ≥0∞) ^ Fintype.card A -
              (Fintype.card {y : Y // f y = y} : ℝ≥0∞)) /
              (Fintype.card Y : ℝ≥0∞) ^ Fintype.card A) ^ Fintype.card A := by
          simpa [pow_mul] using hdivpow
            ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card A -
              (Fintype.card {y : Y // f y = y} : ℝ≥0∞))
            ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card A) (Fintype.card A)
        _ = _ := by rw [hrewrite]

example : Nonempty (Fin 2) := inferInstance

example :
    directoryEscapeProbability (A := Fin 2) (id : Bool → Bool) =
      (1 - (Nat.card {y : Bool // id y = y} : ℝ≥0∞) /
          (Fintype.card Bool : ℝ≥0∞) ^ Fintype.card (Fin 2)) ^ Fintype.card (Fin 2) := by
  exact directory_escape_probability_exact (A := Fin 2) (Y := Bool) id

end

end D5.S0.Diagonal.Probability.DifferentialTestingEscape
