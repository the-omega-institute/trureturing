/- GID: D5/S3/Geometry/Hyperideal/SupportRatioExit
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/SupportRatioExit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite support family admits a maximal ratio exit along an affine ray. -/

import Mathlib.Tactic

noncomputable section
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.SupportRatioExit

/- A maximal ratio among finitely many strictly negative anchor supports gives
   an exit point where one support is zero, all supports remain nonpositive,
   and the original point is recovered by the affine interpolation identity. -/
theorem support_ratio_exit {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (L : ι → (Fin 4 → ℝ) → ℝ)
    (a x : Fin 4 → ℝ)
    (hline : ∀ r u, L r (fun j => a j + u * (x j - a j)) =
      L r a + u * (L r x - L r a))
    (ha : ∀ r ∈ S, L r a < 0)
    (hzero : ∀ r, r ∉ S → L r a = 0)
    (hx : ∀ r, L r x ≤ 0)
    (hgrowth : ∃ r ∈ S, L r a < L r x) :
    ∃ r ∈ S, ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = (L r x - L r a) / (-L r a) ∧
      (∀ s ∈ S, (L s x - L s a) / (-L s a) ≤ t) ∧
      (∀ s, L s (fun j => a j + (x j - a j) / t) ≤ 0) ∧
      L r (fun j => a j + (x j - a j) / t) = 0 ∧
      x = (1 - t) • a + t • (fun j => a j + (x j - a j) / t) := by
  obtain ⟨s, hs, hsa⟩ := hgrowth
  obtain ⟨r, hr, hmax⟩ := S.exists_max_image
    (fun r => (L r x - L r a) / (-L r a)) ⟨s, hs⟩
  let t := (L r x - L r a) / (-L r a)
  have ht : 0 < t := lt_of_lt_of_le
    (div_pos (sub_pos.mpr hsa) (neg_pos.mpr (ha s hs))) (hmax s hs)
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ (neg_pos.mpr (ha r hr))).mpr
    linarith [hx r]
  have hformula (s : ι) :
      L s (fun j => a j + (x j - a j) / t) =
        L s a + (L s x - L s a) / t := by
    simpa only [div_eq_mul_inv, mul_comm] using hline s t⁻¹
  have hle (s : ι) : L s (fun j => a j + (x j - a j) / t) ≤ 0 := by
    rw [hformula]
    by_cases hs : s ∈ S
    · have hd : (L s x - L s a) / t ≤ -L s a := by
        apply (div_le_iff₀ ht).mpr
        have hnum := (div_le_iff₀ (neg_pos.mpr (ha s hs))).mp (hmax s hs)
        simpa [t, mul_comm] using hnum
      linarith
    · rw [hzero s hs, sub_zero, zero_add]
      exact div_nonpos_of_nonpos_of_nonneg (hx s) ht.le
  have heq : L r (fun j => a j + (x j - a j) / t) = 0 := by
    rw [hformula]
    have hta : t * (-L r a) = L r x - L r a := by
      exact div_mul_cancel₀ _ (neg_pos.mpr (ha r hr)).ne'
    have hquot : (L r x - L r a) / t = -L r a := by
      apply (div_eq_iff ht.ne').mpr
      nlinarith only [hta]
    rw [hquot]
    ring
  refine ⟨r, hr, t, ht, ht1, rfl, hmax, hle, heq, ?_⟩
  ext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [ht.ne']
  ring

#print axioms support_ratio_exit

end D5.S3.Geometry.Hyperideal.SupportRatioExit
