/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact complex algebraic multiplicities and collision exclusion for the actual vortex polygon. -/

import D5.S3.FluidDynamics.Vortices.AlternatingPolygonModes

/-! Complex root multiplicities of the actual Cartesian characteristic polynomial. -/
noncomputable section
open scoped BigOperators
open Matrix Polynomial

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonMultiplicity
open InverseChordCirculant AlternatingPolygonSpectrum AlternatingPolygonModes

/-- The squared spectral value of a folded label. -/
def squaredValue (m r : ℕ) : ℝ :=
  ((m : ℝ) - r) ^ 2 * ((r : ℝ) ^ 2 - 2) / 4

private theorem squaredValue_pos (m r : ℕ) (hr : 2 ≤ r) (hrm : r < m) :
    0 < squaredValue m r := by
  have h := positiveRoot_pos m r hr hrm
  unfold squaredValue
  rw [← positiveRoot_sq m r hr]
  exact sq_pos_of_pos h

private theorem squaredValue_zero (m : ℕ) : squaredValue m m = 0 := by
  simp [squaredValue]

private theorem squaredValue_first (m : ℕ) :
    squaredValue m 0 = -((m : ℝ) ^ 2 / 2) ∧
      squaredValue m 1 = -(((m : ℝ) - 1) ^ 2 / 4) := by
  constructor <;> simp [squaredValue] <;> ring

/-- There are no collisions between different folded squared modes. The
positive-positive case consumes the canonical integer separation proof. -/
theorem squaredValue_injective (m : ℕ) (hm : 1 ≤ m) {r s : ℕ}
    (hr : r ≤ m) (hs : s ≤ m) :
    squaredValue m r = squaredValue m s ↔ r = s := by
  suffices hlt : ∀ r s : ℕ, r < s → s ≤ m →
      squaredValue m r ≠ squaredValue m s by
    constructor
    · intro h
      rcases lt_trichotomy r s with hlt' | heq | hgt
      · exact False.elim (hlt r s hlt' hs h)
      · exact heq
      · exact False.elim (hlt s r hgt hr h.symm)
    · rintro rfl; rfl
  intro r s hrs hsm heq
  by_cases hs0 : s = m
  · subst s
    rw [squaredValue_zero] at heq
    by_cases hr0 : r = 0
    · subst r
      have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      rw [(squaredValue_first m).1] at heq
      nlinarith
    · by_cases hr1 : r = 1
      · subst r
        have hmR : (1 : ℝ) < m := by exact_mod_cast hrs
        rw [(squaredValue_first m).2] at heq
        nlinarith
      · exact (ne_of_gt (squaredValue_pos m r (by omega) hrs)) heq
  · have hsm' : s < m := by omega
    by_cases hr0 : r = 0
    · subst r
      rw [(squaredValue_first m).1] at heq
      by_cases hs1 : s = 1
      · subst s
        rw [(squaredValue_first m).2] at heq
        have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
        nlinarith
      · have hp := squaredValue_pos m s (by omega) hsm'
        nlinarith [sq_nonneg (m : ℝ)]
    · by_cases hr1 : r = 1
      · subst r
        rw [(squaredValue_first m).2] at heq
        have hp := squaredValue_pos m s (by omega) hsm'
        nlinarith [sq_nonneg ((m : ℝ) - 1)]
      · apply distinctness_certificate m r s (by omega) hrs hsm'
        unfold squaredValue at heq
        linarith

private theorem rootMultiplicity_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ[X])
    (hf : ∀ i ∈ s, f i ≠ 0) (μ : ℂ) :
    (∏ i ∈ s, f i).rootMultiplicity μ = ∑ i ∈ s, (f i).rootMultiplicity μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Polynomial.rootMultiplicity_mul (mul_ne_zero (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj)))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

private theorem quadratic_multiplicity (γ μ : ℂ) (hμ : μ ≠ 0) :
    (X ^ 2 - C γ : ℂ[X]).rootMultiplicity μ = if μ ^ 2 = γ then 1 else 0 := by
  classical
  by_cases h : μ ^ 2 = γ
  · have he : (X ^ 2 - C γ : ℂ[X]) = (X - C μ) * (X - C (-μ)) := by
      rw [← h, map_neg, map_pow]
      ring
    rw [he, Polynomial.rootMultiplicity_mul
      (mul_ne_zero (X_sub_C_ne_zero μ) (X_sub_C_ne_zero (-μ))),
      rootMultiplicity_X_sub_C, rootMultiplicity_X_sub_C, if_pos rfl, if_neg]
    · simp [h]
    · intro he
      exact hμ (by linear_combination (1 / 2 : ℂ) * he)
  · rw [if_neg h]
    apply Polynomial.rootMultiplicity_eq_zero
    simpa only [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using h

/-- A nonzero root has exactly one eigenline in each matching Fourier block;
this computes its full algebraic multiplicity, including repeated labels. -/
theorem nonzero_algebraic_multiplicity (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
    (μ : ℂ) (hμ : μ ≠ 0) :
    (((jacobian (2 * m)).map Complex.ofRealHom).charpoly).rootMultiplicity μ =
      (Finset.univ.filter (fun q : ZMod (2 * m) => μ ^ 2 = (gamma m q : ℂ))).card := by
  classical
  rw [complex_charpoly_mode_product m hm, rootMultiplicity_prod _ _
    (fun q _ => X_pow_sub_C_ne_zero (by omega : 0 < 2) (gamma m q : ℂ))]
  simp_rw [quadratic_multiplicity _ _ hμ]
  simp only [Finset.card_filter]

/-- Exact nonzero algebraic multiplicity at a folded squared mode. -/
theorem algebraic_multiplicity_of_mode (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
    {r : ℕ} (hr : r ≤ m) (μ : ℂ) (hμ : μ ≠ 0)
    (hroot : μ ^ 2 = (squaredValue m r : ℂ)) :
    (((jacobian (2 * m)).map Complex.ofRealHom).charpoly).rootMultiplicity μ =
      if r = 0 ∨ r = m then 1 else 2 := by
  rw [nonzero_algebraic_multiplicity m hm μ hμ]
  have he : ∀ q : ZMod (2 * m), μ ^ 2 = (gamma m q : ℂ) ↔ fold m q = r := by
    intro q
    rw [hroot]
    change (squaredValue m r : ℂ) = (squaredValue m (fold m q) : ℂ) ↔ _
    rw [Complex.ofReal_inj, squaredValue_injective m hm hr (fold_le m q), eq_comm]
  simp_rw [he]
  exact fold_fibre_card m hr

private theorem quadratic_zero_multiplicity (γ : ℂ) :
    (X ^ 2 - C γ : ℂ[X]).rootMultiplicity 0 = if γ = 0 then 2 else 0 := by
  classical
  by_cases h : γ = 0
  · subst γ
    simpa using (rootMultiplicity_X_sub_C_pow (0 : ℂ) 2)
  · rw [if_neg h]
    apply Polynomial.rootMultiplicity_eq_zero
    simpa [Polynomial.IsRoot] using h

/-- The zero root has algebraic multiplicity exactly two, including dipole and square. -/
theorem zero_algebraic_multiplicity (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) :
    (((jacobian (2 * m)).map Complex.ofRealHom).charpoly).rootMultiplicity 0 = 2 := by
  classical
  rw [complex_charpoly_mode_product m hm, rootMultiplicity_prod _ _
    (fun q _ => X_pow_sub_C_ne_zero (by omega : 0 < 2) (gamma m q : ℂ))]
  simp_rw [quadratic_zero_multiplicity, Complex.ofReal_eq_zero, gamma_zero_iff]
  have hc := fold_fibre_card m (le_refl m)
  simp only [or_true, ite_true] at hc
  have hs : (∑ q : ZMod (2 * m), if fold m q = m then 2 else 0) =
      2 * (Finset.univ.filter (fun q : ZMod (2 * m) => fold m q = m)).card := by
    rw [Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp
  rw [hs, hc]

/-- Root classification in the complete complex field, before choosing square roots. -/
theorem complex_root_iff_mode (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) (μ : ℂ) :
    (((jacobian (2 * m)).map Complex.ofRealHom).charpoly).IsRoot μ ↔
      ∃ q : ZMod (2 * m), μ ^ 2 = (gamma m q : ℂ) := by
  classical
  rw [complex_charpoly_mode_product m hm]
  simp only [Polynomial.IsRoot, eval_prod, eval_sub, eval_pow, eval_X, eval_C,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero]

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonMultiplicity
