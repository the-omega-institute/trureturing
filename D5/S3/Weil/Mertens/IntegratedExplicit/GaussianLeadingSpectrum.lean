import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import D5.S3.Weil.ZetaSeam.StatementSeamClosed

/-! The quadratic Gaussian exponent suppresses high ordinates and makes the
leading group finite even when the undamped real parts have no maximum. -/

noncomputable section

open Set

namespace GaussianLeadingSpectrum

def exponent (v : ℝ) (z : ℂ) : ℂ :=
  z + (v : ℂ) * z ^ 2 / 2

theorem exponent_re (v : ℝ) (z : ℂ) :
    (exponent v z).re = z.re + v * (z.re ^ 2 - z.im ^ 2) / 2 := by
  unfold exponent
  rw [div_eq_mul_inv, show ((2 : ℂ)⁻¹) = ((1 / 2 : ℝ) : ℂ) by norm_num, pow_two]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, zero_mul]
  ring

theorem exponent_injective_on_right {v : ℝ} (hv : 0 ≤ v) :
    Set.InjOn (exponent v) {z : ℂ | 0 < z.re} := by
  intro z hz w hw he
  have hz' : 0 < z.re := hz
  have hw' : 0 < w.re := hw
  have hne : 1 + (v : ℂ) * (z + w) / 2 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    rw [div_eq_mul_inv, show ((2 : ℂ)⁻¹) = ((1 / 2 : ℝ) : ℂ) by norm_num] at h'
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.zero_re, mul_zero, sub_zero, zero_mul] at h'
    nlinarith [mul_nonneg hv (add_nonneg hz'.le hw'.le)]
  have hfactor : (z - w) * (1 + (v : ℂ) * (z + w) / 2) = 0 := by
    unfold exponent at he
    linear_combination he
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hne)

theorem exponent_re_upper {v : ℝ} (hv : 0 ≤ v) {z : ℂ}
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    (exponent v z).re ≤ 1 + v / 2 - v * z.im ^ 2 / 2 := by
  have hs : z.re ^ 2 ≤ 1 := by nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz1)]
  rw [exponent_re]
  nlinarith [mul_nonneg hv (sub_nonneg.mpr hs)]

/-- Every fixed score superlevel lies in a bounded height range. -/
theorem finite_score_superlevel {ι : Type*} {z : ι → ℂ} {v : ℝ} (hv : 0 < v)
    (hstrip : ∀ i, 0 ≤ (z i).re ∧ (z i).re ≤ 1)
    (hfinite : ∀ R : ℝ, {i | |(z i).im| ≤ R}.Finite) (L : ℝ) :
    {i | L ≤ (exponent v (z i)).re}.Finite := by
  let C := (1 + v / 2 - L) / (v / 2)
  refine (hfinite (1 + max 0 C)).subset ?_
  intro i hi
  have hi' : L ≤ (exponent v (z i)).re := hi
  have hs := hi'.trans (exponent_re_upper hv.le (hstrip i).1 (hstrip i).2)
  have him : (z i).im ^ 2 ≤ C := by
    apply (le_div_iff₀ (show 0 < v / 2 by positivity)).mpr
    linarith only [hs]
  have habs : |(z i).im| ≤ 1 + |(z i).im| ^ 2 := by nlinarith [sq_nonneg (|(z i).im| - 1)]
  exact habs.trans (by rw [sq_abs]; linarith [him, le_max_right 0 C])

/-- Above any specified member there is an attained leading score with a
finite leading group and an actual gap to the other scores. -/
theorem leading_group {ι : Type*} {z : ι → ℂ} {v : ℝ} (hv : 0 < v)
    (hstrip : ∀ i, 0 ≤ (z i).re ∧ (z i).re ≤ 1)
    (hfinite : ∀ R : ℝ, {i | |(z i).im| ≤ R}.Finite) (i₀ : ι) :
    ∃ topScore η : ℝ, 0 < η ∧ (exponent v (z i₀)).re ≤ topScore ∧
      ({i | (exponent v (z i)).re = topScore} : Set ι).Nonempty ∧
      ({i | (exponent v (z i)).re = topScore} : Set ι).Finite ∧
      ∀ i, (exponent v (z i)).re = topScore ∨ (exponent v (z i)).re ≤ topScore - η := by
  classical
  let f (i : ι) := (exponent v (z i)).re
  let L := f i₀ - 1
  have hs : {i | L ≤ f i}.Finite := finite_score_superlevel hv hstrip hfinite L
  have h₀ : i₀ ∈ ({i | L ≤ f i} : Set ι) := by change f i₀ - 1 ≤ f i₀; linarith
  obtain ⟨i, _, himax⟩ := Finset.exists_max_image hs.toFinset f
    ⟨i₀, hs.mem_toFinset.mpr h₀⟩
  have hmax : ∀ j ∈ ({i | L ≤ f i} : Set ι), f j ≤ f i :=
    fun j hj => himax j (hs.mem_toFinset.mpr hj)
  let topScore := f i
  have htopScore : f i₀ ≤ topScore := hmax _ h₀
  have hL : L < topScore := lt_of_lt_of_le (by dsimp [L]; linarith) htopScore
  let low : Set ℝ := insert L (f '' {j | L ≤ f j ∧ f j < topScore})
  have hlowfin : low.Finite :=
    (hs.subset (fun _ hj => hj.1)).image f |>.insert L
  obtain ⟨M, hMfin, hMmax⟩ := Finset.exists_max_image hlowfin.toFinset id
    ⟨L, hlowfin.mem_toFinset.mpr (mem_insert _ _)⟩
  have hM : M ∈ low := hlowfin.mem_toFinset.mp hMfin
  have hMlt : M < topScore := by
    rcases mem_insert_iff.mp hM with h | ⟨j, hj, rfl⟩
    · simpa only [h] using hL
    · exact hj.2
  have hMle : ∀ a ∈ low, a ≤ M :=
    fun a ha => hMmax a (hlowfin.mem_toFinset.mpr ha)
  refine ⟨topScore, topScore - M, sub_pos.mpr hMlt, htopScore, ⟨i, rfl⟩,
    hs.subset ?_, ?_⟩
  · intro j hj
    change f j = topScore at hj
    change L ≤ f j
    rw [hj]
    exact hL.le
  intro j
  change f j = topScore ∨ f j ≤ topScore - (topScore - M)
  by_cases hj : L ≤ f j
  · rcases (hmax j hj).eq_or_lt with hEq | hlt
    · exact Or.inl hEq
    · exact Or.inr (by
        linarith only [hMle (f j) (mem_insert_of_mem _ ⟨j, ⟨hj, hlt⟩, rfl⟩)])
  · exact Or.inr (by linarith only [lt_of_not_ge hj, hMle L (mem_insert _ _)])

end GaussianLeadingSpectrum

#print axioms GaussianLeadingSpectrum.leading_group

namespace GaussianLeadingSpectrum

open Zeta23 (IsNontrivialZero zerosIn zerosIn_finite)

abbrev StripZero := {ρ : ℂ // IsNontrivialZero ρ}

/-- An off-line zero produces a finite leading group whose Gaussian score
strictly exceeds the score of the critical-line exponential envelope. -/
theorem actual_leading_group {ρ : StripZero} (hβ : 1 / 2 < ρ.val.re) {v : ℝ}
    (hv : 0 < v)
    (hvsmall : v ≤ (ρ.val.re - 1 / 2) / (1 + ρ.val.im ^ 2)) :
    ∃ topScore gap : ℝ, 0 < gap ∧ 1 / 2 + v / 8 < topScore ∧
      ({z : StripZero | (exponent v z.val).re = topScore} : Set StripZero).Nonempty ∧
      ({z : StripZero | (exponent v z.val).re = topScore} : Set StripZero).Finite ∧
      ∀ z : StripZero, (exponent v z.val).re = topScore ∨
        (exponent v z.val).re ≤ topScore - gap := by
  have hfinite (R : ℝ) : {z : StripZero | |z.val.im| ≤ R}.Finite := by
    have hpreimage := (zerosIn_finite (-R - 1) R).preimage
      (f := (Subtype.val : StripZero → ℂ)) Subtype.val_injective.injOn
    apply hpreimage.subset
    intro z hz
    have hz' : |z.val.im| ≤ R := hz
    exact ⟨z.property, by linarith [(abs_le.mp hz').1], (abs_le.mp hz').2⟩
  obtain ⟨m, d, hd, hscore, hnonempty, htopFinite, hrest⟩ :=
    leading_group (z := Subtype.val) hv
      (fun z : StripZero => ⟨z.property.2.1.le, z.property.2.2.le⟩) hfinite ρ
  refine ⟨m, d, hd, lt_of_lt_of_le ?_ hscore, hnonempty, htopFinite, hrest⟩
  rw [exponent_re]
  have hsmall := (le_div_iff₀ (show 0 < 1 + ρ.val.im ^ 2 by positivity)).mp hvsmall
  nlinarith [mul_nonneg hv.le (show 0 ≤ ρ.val.re ^ 2 - 1 / 4 by nlinarith)]

end GaussianLeadingSpectrum

#print axioms GaussianLeadingSpectrum.actual_leading_group
