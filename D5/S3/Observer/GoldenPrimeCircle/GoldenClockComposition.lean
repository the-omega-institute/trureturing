/- GID: D5/S3/Observer/GoldenPrimeCircle/GoldenClockComposition
   generality: G
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:exact-universal-algebra)
   anchors: []
   digest: Nested Beatty return maps have an exact orientation carry and a closed commutator at every pair of resolutions. -/

import D5.S3.Observer.GoldenPrimeCircle.GoldenClockLattice

namespace D5.S3.Observer.GoldenPrimeCircle.GoldenClockComposition

open GoldenClockLattice

noncomputable section

/-- Which side of the integer boundary the residual occupies. -/
def cutCarry (L : ℕ) : ℤ := if 0 < signedWidth L then 0 else 1

lemma signedWidth_abs_lt_one (L : ℕ) : |signedWidth L| < 1 := by
  rw [signedWidth_abs]
  unfold width
  exact pow_lt_one₀ (le_of_lt alpha_pos) alpha_lt_one (by omega)

/-- Irrationality makes the full two-integer residual faithful. -/
theorem residual_injective (e₁ h₁ e₂ h₂ : ℤ)
    (h : (e₁ : ℝ) * alpha - h₁ = (e₂ : ℝ) * alpha - h₂) :
    e₁ = e₂ ∧ h₁ = h₂ := by
  have he : e₁ = e₂ := by
    by_contra hne
    apply no_nonzero_clock_period (e₁ - e₂) (by omega)
    refine ⟨h₁ - h₂, ?_⟩
    push_cast
    linarith
  refine ⟨he, ?_⟩
  have hh : (h₁ : ℝ) = h₂ := by rw [he] at h; linarith
  exact_mod_cast hh

/-- The lift composition is proved from exact residuals and integral injectivity. -/
theorem lattice_composition (K L : ℕ) (m k : ℤ) :
    let e := leading L * m + boundary L * k
    let h := boundary L * m + previous L * k
    leading K * e + boundary K * h =
        leading (K + L + 2) * m + boundary (K + L + 2) * k ∧
      boundary K * e + previous K * h =
        boundary (K + L + 2) * m + previous (K + L + 2) * k := by
  dsimp only
  apply residual_injective
  rw [lattice_phase_identity, lattice_phase_identity, lattice_phase_identity]
  have hd : signedWidth K * signedWidth L = signedWidth (K + L + 2) := by
    unfold signedWidth
    rw [← pow_add]
    congr 1 <;> omega
  rw [← hd]
  ring

/-- Taking the integer part loses exactly one unit on a negative-oriented window. -/
theorem floor_entry (L : ℕ) (m : ℤ) (hm : m ≠ 0) :
    ⌊(entry L m : ℝ) * alpha⌋ =
      boundary L * m + previous L * ⌊(m : ℝ) * alpha⌋ - cutCarry L := by
  let r : ℝ := (m : ℝ) * alpha - (⌊(m : ℝ) * alpha⌋ : ℤ)
  have hr : 0 < r ∧ r < 1 := fractional_bounds m hm
  have hres := lattice_phase_identity L m ⌊(m : ℝ) * alpha⌋
  change (entry L m : ℝ) * alpha -
      ((boundary L * m + previous L * ⌊(m : ℝ) * alpha⌋ : ℤ) : ℝ) =
      signedWidth L * r at hres
  have hd := abs_lt.mp (signedWidth_abs_lt_one L)
  by_cases hp : 0 < signedWidth L
  · have hc : cutCarry L = 0 := by simp [cutCarry, hp]
    rw [hc, sub_zero]
    apply Int.floor_eq_iff.mpr
    have hprod0 : 0 < signedWidth L * r := mul_pos hp hr.1
    have hprod1 : signedWidth L * r < 1 := by
      have hh := mul_lt_mul_of_pos_left hr.2 hp
      nlinarith
    constructor <;> linarith
  · have hn : signedWidth L < 0 := by
      rcases lt_trichotomy (signedWidth L) 0 with h | h | h
      · exact h
      · exact (signedWidth_ne_zero L h).elim
      · exact (hp h).elim
    have hc : cutCarry L = 1 := by simp [cutCarry, hp]
    rw [hc]
    apply Int.floor_eq_iff.mpr
    have hprod0 : signedWidth L * r < 0 := mul_neg_of_neg_of_pos hn hr.1
    have hprod1 : -1 < signedWidth L * r := by
      have hh := mul_lt_mul_of_neg_left hr.2 hn
      nlinarith
    push_cast at hres ⊢
    constructor <;> linarith

theorem cutCarry_zero : cutCarry 0 = 0 := by
  have hp : 0 < signedWidth 0 := by
    change 0 < Real.goldenConj ^ 2
    exact sq_pos_of_ne_zero Real.goldenConj_ne_zero
  simp [cutCarry, hp]

/-- The carry flips when resolution increases; no special width is selected. -/
theorem cutCarry_succ (L : ℕ) : cutCarry (L + 1) = 1 - cutCarry L := by
  by_cases hp : 0 < signedWidth L
  · have hn : signedWidth (L + 1) < 0 := by
      rw [signedWidth_succ]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos alpha_pos) hp
    simp [cutCarry, hp, not_lt_of_ge (le_of_lt hn)]
  · have hn : signedWidth L < 0 := by
      rcases lt_trichotomy (signedWidth L) 0 with h | h | h
      · exact h
      · exact (signedWidth_ne_zero L h).elim
      · exact (hp h).elim
    have hnext : 0 < signedWidth (L + 1) := by
      rw [signedWidth_succ]
      exact mul_pos_of_neg_of_neg (neg_neg_of_pos alpha_pos) hn
    simp [cutCarry, hp, hnext]

/-- Nested return maps compose by a uniform carry correction. -/
theorem entry_compose (K L : ℕ) (m : ℤ) (hm : m ≠ 0) :
    entry K (entry L m) =
      entry (K + L + 2) m - boundary K * cutCarry L := by
  change leading K * entry L m + boundary K * ⌊(entry L m : ℝ) * alpha⌋ = _
  rw [floor_entry L m hm]
  have h := (lattice_composition K L m ⌊(m : ℝ) * alpha⌋).1
  dsimp only at h
  unfold entry
  linear_combination h

/-- Exact order defect, independent of the nonzero input m. -/
theorem entry_commutator (K L : ℕ) (m : ℤ) (hm : m ≠ 0) :
    entry K (entry L m) - entry L (entry K m) =
      boundary L * cutCarry K - boundary K * cutCarry L := by
  rw [entry_compose K L m hm, entry_compose L K m hm]
  rw [show L + K + 2 = K + L + 2 by omega]
  ring

/-- A finite arithmetic test determines commutation for every nonzero input at once. -/
theorem entry_commute_iff (K L : ℕ) (m : ℤ) (hm : m ≠ 0) :
    entry K (entry L m) = entry L (entry K m) ↔
      boundary L * cutCarry K = boundary K * cutCarry L := by
  have h := entry_commutator K L m hm
  constructor <;> intro he <;> linarith

end
end D5.S3.Observer.GoldenPrimeCircle.GoldenClockComposition
