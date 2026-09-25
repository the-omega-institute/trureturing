/- GID: D5/S1/Words/Mechanical/MechanicalDyadicBoundary
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalDyadicBoundary
   mirror-E: none(waiver:actual-mechanical-dyadic-boundary)
   anchors: []
   utility: none
   digest: Dyadic lower slopes converge in precision but miss an exact mechanical boundary bit. -/

import D5.S1.Words.Mechanical.MechanicalSlopeSensitivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S1.Words.Mechanical.MechanicalDyadicBoundary

open D5.S1.Words.Mechanical

def dyadicLower (alpha : ℝ) (p : ℕ) : ℝ :=
  (⌊((2 ^ p : ℕ) : ℝ) * alpha⌋ : ℝ) / ((2 ^ p : ℕ) : ℝ)

/-- Every finite lower binary approximation misses the exact boundary bit,
despite its error being strictly less than the requested binary unit. -/
theorem dyadic_lower_boundary_mismatch
    (alpha : ℝ) (halpha : Irrational alpha) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (p : ℕ) :
    0 ≤ dyadicLower alpha p ∧
      0 < alpha - dyadicLower alpha p ∧
      alpha - dyadicLower alpha p < (1 : ℝ) / ((2 ^ p : ℕ) : ℝ) ∧
      lowerMechanicalWord alpha (1 - alpha) 0 = true ∧
      lowerMechanicalWord (dyadicLower alpha p) (1 - alpha) 0 = false := by
  let N : ℕ := 2 ^ p
  let t : ℝ := (N : ℝ) * alpha
  let beta : ℝ := dyadicLower alpha p
  have hNnat : N ≠ 0 := by dsimp [N]; positivity
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hNnat
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hfloor0 : (0 : ℤ) ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht0
  have hcast0 : (0 : ℝ) ≤ (⌊t⌋ : ℝ) := by exact_mod_cast hfloor0
  have hbetadef : beta = (⌊t⌋ : ℝ) / (N : ℝ) := by rfl
  have hbeta0 : 0 ≤ beta := by rw [hbetadef]; positivity
  have htIrr : Irrational t := by
    dsimp [t]
    exact halpha.natCast_mul hNnat
  have hfloorlt : (⌊t⌋ : ℝ) < t := by
    apply (Int.floor_lt_self_iff).2
    rintro ⟨z, hz⟩
    exact (htIrr.ne_int z) hz.symm
  have hbetalt : beta < alpha := by
    rw [hbetadef]
    apply (div_lt_iff₀ hN).2
    calc
      (⌊t⌋ : ℝ) < t := hfloorlt
      _ = alpha * (N : ℝ) := by dsimp [t]; ring
  have hfloorupper : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one t
  have hbetaupper : alpha < beta + 1 / (N : ℝ) := by
    rw [hbetadef, ← add_div]
    apply (lt_div_iff₀ hN).2
    calc
      alpha * (N : ℝ) = t := by dsimp [t]; ring
      _ < (⌊t⌋ : ℝ) + 1 := hfloorupper
  let x : ℝ := 1 - alpha
  have hx : x ∈ Set.Ico (0 : ℝ) 1 := by
    dsimp [x]
    constructor <;> linarith
  have hfloorx : ⌊x⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr hx
  have hflooralpha : ⌊x + alpha⌋ = (1 : ℤ) := by
    have hxa : x + alpha = 1 := by dsimp [x]; ring
    rw [hxa]
    norm_num
  have hfloorbeta : ⌊x + beta⌋ = (0 : ℤ) := by
    apply Int.floor_eq_zero_iff.mpr
    constructor
    · dsimp [x]
      linarith
    · dsimp [x]
      linarith
  have hletteralpha : lowerMechanicalLetter alpha x 0 = 1 := by
    simp [lowerMechanicalLetter, hflooralpha, hfloorx]
  have hletterbeta : lowerMechanicalLetter beta x 0 = 0 := by
    simp [lowerMechanicalLetter, hfloorbeta, hfloorx]
  refine ⟨hbeta0, by linarith, by dsimp [N] at hbetaupper ⊢; linarith, ?_, ?_⟩
  · change lowerMechanicalWord alpha x 0 = true
    exact (lowerMechanicalWord_eq_true_iff alpha x 0).2 hletteralpha
  · change lowerMechanicalWord beta x 0 = false
    simp [lowerMechanicalWord, hletterbeta]

#print axioms dyadic_lower_boundary_mismatch

end D5.S1.Words.Mechanical.MechanicalDyadicBoundary
