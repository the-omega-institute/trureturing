/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exhaustive complex spectral values and their folded algebraic and geometric multiplicities. -/

import D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition

/-! All complex roots, with separate endpoint and internal multiplicities. -/
noncomputable section
open scoped BigOperators

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
open InverseChordCirculant AlternatingPolygonSpectrum AlternatingPolygonModes
open AlternatingPolygonMultiplicity AlternatingPolygonJordan AlternatingPolygonDecomposition

/-- One square root of each folded spectral value. The neutral label is handled first,
so the dipole does not identify its neutral mode with a nonzero internal mode. -/
def spectralRoot (m r : ℕ) : ℂ :=
  if r = m then 0 else if r = 0 then Complex.I * ((m : ℂ) / (Real.sqrt 2 : ℂ))
  else if r = 1 then Complex.I * (((m : ℂ) - 1) / 2)
  else (positiveRoot m r : ℂ)

theorem spectralRoot_sq (m : ℕ) {r : ℕ} (hr : r ≤ m) :
    spectralRoot m r ^ 2 = (squaredValue m r : ℂ) := by
  by_cases hrm : r = m
  · subst r
    simp [spectralRoot, squaredValue]
  · have hrm' : r < m := by omega
    by_cases hr0 : r = 0
    · subst r
      have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
        exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
      unfold spectralRoot
      rw [if_neg hrm, if_pos rfl, mul_pow, Complex.I_sq, div_pow, hs]
      push_cast
      simp [squaredValue]
      ring
    · by_cases hr1 : r = 1
      · subst r
        unfold spectralRoot
        rw [if_neg hrm, if_neg (by omega : (1 : ℕ) ≠ 0),
          if_pos rfl, mul_pow, Complex.I_sq, div_pow]
        push_cast
        simp [squaredValue]
        ring
      · rw [spectralRoot, if_neg hrm, if_neg hr0, if_neg hr1, ← Complex.ofReal_pow,
          positiveRoot_sq m r (by omega)]
        rfl

/-- Every complex characteristic root is one of these explicit signed values, and conversely. -/
theorem all_complex_roots (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) (μ : ℂ) :
    (((jacobian (2 * m)).map Complex.ofRealHom).charpoly).IsRoot μ ↔
      ∃ r : ℕ, r ≤ m ∧ (μ = spectralRoot m r ∨ μ = -spectralRoot m r) := by
  classical
  rw [complex_root_iff_mode m hm]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨fold m q, fold_le m q, ?_⟩
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [spectralRoot_sq m (fold_le m q), hq]
    rfl
  · rintro ⟨r, hr, hμ⟩
    have hc : 0 < (Finset.univ.filter (fun q : ZMod (2 * m) => fold m q = r)).card := by
      rw [fold_fibre_card m hr]
      split_ifs <;> omega
    obtain ⟨q, hq⟩ := Finset.card_pos.mp hc
    have hqr := (Finset.mem_filter.mp hq).2
    refine ⟨q, ?_⟩
    have hs : μ ^ 2 = spectralRoot m r ^ 2 :=
      sq_eq_sq_iff_eq_or_eq_neg.mpr hμ
    rw [hs, spectralRoot_sq m hr]
    change (squaredValue m r : ℂ) = (squaredValue m (fold m q) : ℂ)
    rw [hqr]

theorem spectralRoot_ne_zero (m : ℕ) (hm : 1 ≤ m) {r : ℕ} (hr : r < m) :
    spectralRoot m r ≠ 0 := by
  intro h
  have hs := spectralRoot_sq m (le_of_lt hr)
  rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
  have he : squaredValue m r = squaredValue m m := by
    simp only [squaredValue, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul, zero_div]
    exact Complex.ofReal_eq_zero.mp hs.symm
  have := (squaredValue_injective m hm (le_of_lt hr) le_rfl).mp he
  omega

/-- Signed roots at different folded labels never collide, including both imaginary families. -/
theorem no_cross_label_collision (m : ℕ) (hm : 1 ≤ m) {r s : ℕ}
    (hr : r ≤ m) (hs : s ≤ m) (μ : ℂ)
    (hμr : μ = spectralRoot m r ∨ μ = -spectralRoot m r)
    (hμs : μ = spectralRoot m s ∨ μ = -spectralRoot m s) : r = s := by
  have hsq : (squaredValue m r : ℂ) = (squaredValue m s : ℂ) := by
    rw [← spectralRoot_sq m hr, ← spectralRoot_sq m hs,
      ← sq_eq_sq_iff_eq_or_eq_neg.mpr hμr, ← sq_eq_sq_iff_eq_or_eq_neg.mpr hμs]
  exact (squaredValue_injective m hm hr hs).mp (Complex.ofReal_inj.mp hsq)

/-- Complete nonzero algebraic and geometric multiplicities of both signed roots. -/
theorem signed_root_multiplicities (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
    {r : ℕ} (hr : r < m) (μ : ℂ)
    (hμ : μ = spectralRoot m r ∨ μ = -spectralRoot m r) :
    (((jacobian (2 * m)).map Complex.ofRealHom).charpoly).rootMultiplicity μ =
        (if r = 0 then 1 else 2) ∧
      Module.finrank ℂ ((actualOperator m).eigenspace μ) = (if r = 0 then 1 else 2) := by
  have hn : μ ≠ 0 := by
    rcases hμ with rfl | rfl
    · exact spectralRoot_ne_zero m hm hr
    · exact neg_ne_zero.mpr (spectralRoot_ne_zero m hm hr)
  have hsq : μ ^ 2 = (squaredValue m r : ℂ) := by
    rw [sq_eq_sq_iff_eq_or_eq_neg.mpr hμ, spectralRoot_sq m (le_of_lt hr)]
  have hrm : r ≠ m := by omega
  constructor
  · simpa only [hrm, or_false] using
      algebraic_multiplicity_of_mode m hm (le_of_lt hr) μ hn hsq
  · simpa only [hrm, or_false] using
      geometric_multiplicity_of_mode m hm (le_of_lt hr) μ hn hsq

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
