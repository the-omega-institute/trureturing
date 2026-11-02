/- GID: D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCompositionMoments
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/FiniteSlitCompositionMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual composition reciprocal banks, outer norm bounds and moment domination. -/

import D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitBankMoments

/-! Actual finite-bank data and outer-circle bounds for normalized reciprocal branches. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Filter MeasureTheory Set Topology

namespace D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitCompositionMoments

/-- The reciprocal of the origin-correct normalized source continuation. -/
def reciprocal (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) (z : ℂ) : ℂ :=
  ((CompositionZeroFreeCollar.normalizedContinuation head tail z)⁻¹) ^ (ell : ℕ)

private theorem outer_bound (A upper lower : ℂ → ℂ) (R0 ρ R : ℝ)
    (hR : 1 < R) (hRR0 : R < R0) (hRρ : R < 1 + ρ)
    (ha : ContinuousOn A {z | z ∈ CompositionContinuation.omega ∧ ‖z‖ < R0})
    (hu : ContinuousOn upper {z | ‖z - 1‖ ≤ ρ ∧ 0 ≤ z.im})
    (hl : ContinuousOn lower {z | ‖z - 1‖ ≤ ρ ∧ z.im ≤ 0})
    (hue : ∀ z, ‖z - 1‖ ≤ ρ → 0 ≤ z.im → z ∈ CompositionContinuation.omega → upper z = A z)
    (hle : ∀ z, ‖z - 1‖ ≤ ρ → z.im ≤ 0 → z ∈ CompositionContinuation.omega → lower z = A z) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ CompositionContinuation.omega, ‖z‖ = R → ‖A z‖ ≤ B := by
  let δ := (ρ + (R - 1)) / 2
  have hδ : R - 1 < δ := by dsimp [δ]; linarith
  have hδρ : δ < ρ := by dsimp [δ]; linarith
  let K : Set ℂ := {z | ‖z‖ = R ∧ δ ≤ ‖z - 1‖}
  have hK : IsCompact K := by
    have he : K = Metric.sphere (0 : ℂ) R ∩ {z | δ ≤ ‖z - 1‖} := by
      ext z
      simp [K, Metric.mem_sphere, dist_zero_right]
    rw [he]
    exact (isCompact_sphere (0 : ℂ) R).inter_right (isClosed_le continuous_const (by fun_prop))
  have hKOmega : K ⊆ CompositionContinuation.omega := by
    intro z hz
    by_contra hzo
    change ¬ (1 - z ∈ Complex.slitPlane) at hzo
    rw [Complex.mem_slitPlane_iff] at hzo
    push_neg at hzo
    have hzim : z.im = 0 := by simpa using hzo.2
    have hre0 : 1 - z.re ≤ 0 := by simpa only [sub_re, one_re] using hzo.1
    have hre : 1 ≤ z.re := by linarith
    have hzreal : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [hzim]
    have hnorm : ‖z‖ = z.re := by
      rw [hzreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] <;> simp
    have hnorm1 : ‖z - 1‖ = z.re - 1 := by
      rw [hzreal, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)] <;> simp
    have hzR : z.re = R := hnorm.symm.trans hz.1
    have hzδ := hz.2
    rw [hnorm1, hzR] at hzδ
    linarith
  obtain ⟨Mf, hMf⟩ := hK.exists_bound_of_continuousOn (ha.mono (fun z hz ↦
    ⟨hKOmega hz, by rw [hz.1]; exact hRR0⟩))
  have hKu : IsCompact {z : ℂ | ‖z - 1‖ ≤ ρ ∧ 0 ≤ z.im} := by
    have he : {z : ℂ | ‖z - 1‖ ≤ ρ ∧ 0 ≤ z.im} =
        Metric.closedBall (1 : ℂ) ρ ∩ {z | 0 ≤ z.im} := by
      ext z
      simp [Metric.mem_closedBall, dist_eq_norm]
    rw [he]
    exact (isCompact_closedBall (1 : ℂ) ρ).inter_right
      (isClosed_le continuous_const Complex.continuous_im)
  have hKl : IsCompact {z : ℂ | ‖z - 1‖ ≤ ρ ∧ z.im ≤ 0} := by
    have he : {z : ℂ | ‖z - 1‖ ≤ ρ ∧ z.im ≤ 0} =
        Metric.closedBall (1 : ℂ) ρ ∩ {z | z.im ≤ 0} := by
      ext z
      simp [Metric.mem_closedBall, dist_eq_norm]
    rw [he]
    exact (isCompact_closedBall (1 : ℂ) ρ).inter_right
      (isClosed_le Complex.continuous_im continuous_const)
  obtain ⟨Mu, hMu⟩ := hKu.exists_bound_of_continuousOn hu
  obtain ⟨Ml, hMl⟩ := hKl.exists_bound_of_continuousOn hl
  refine ⟨max 0 (max Mf (max Mu Ml)), le_max_left _ _, ?_⟩
  intro z hzo hzR
  apply le_trans _ (le_max_right _ _)
  by_cases hzδ : δ ≤ ‖z - 1‖
  · exact (hMf z ⟨hzR, hzδ⟩).trans (le_max_left _ _)
  · have hzρ : ‖z - 1‖ ≤ ρ := (lt_of_not_ge hzδ).le.trans hδρ.le
    apply le_trans _ (le_max_right _ _)
    by_cases hzi : 0 ≤ z.im
    · rw [← hue z hzρ hzi hzo]
      exact (hMu z ⟨hzρ, hzi⟩).trans (le_max_left _ _)
    · rw [← hle z hzρ (le_of_not_ge hzi) hzo]
      exact (hMl z ⟨hzρ, le_of_not_ge hzi⟩).trans (le_max_right _ _)

/-- The actual all-composition, same-power bank integral eventually dominates
any outer geometric error. This does not yet identify that expression with
an ordinary Taylor coefficient. -/
theorem result (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) :
    ∃ R0 ρ R : ℝ, ∃ upper : ℂ → ℂ,
      1 < R0 ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < R ∧ R < R0 ∧ R < 1 + ρ ∧
      AnalyticOnNhd ℂ (reciprocal head tail ell)
        {z | z ∈ CompositionContinuation.omega ∧ ‖z‖ < R0} ∧
      (∀ z : ℂ, ‖z‖ < 1 → reciprocal head tail ell z =
        ((CompositionDisk.normalized head tail z)⁻¹) ^ (ell : ℕ)) ∧
      reciprocal head tail ell 0 =
        ((CompositionDisk.normalized head tail 0)⁻¹) ^ (ell : ℕ) ∧
      ContinuousOn upper {z | ‖z - 1‖ ≤ ρ ∧ 0 ≤ z.im} ∧
      (∀ z : ℂ, ‖z - 1‖ ≤ ρ → 0 ≤ z.im → z ∈ CompositionContinuation.omega →
        upper z = reciprocal head tail ell z) ∧
      upper 1 = (if 1 < (head : ℕ) then
        ((CompositionBoundary.zeta head tail : ℂ)⁻¹) ^ (ell : ℕ) else 0) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ CompositionContinuation.omega,
        ‖z‖ = R → ‖reciprocal head tail ell z‖ ≤ B) ∧
      ∀ B : ℝ, ∀ᶠ n : ℕ in atTop,
        B / R ^ n + (1 / Real.pi) *
          (∫ x in (1 : ℝ)..R, (upper (x : ℂ)).im / x ^ (n + 1)) < 0 := by
  obtain ⟨hdisk, hanalytic, R0, hR0, hnonzero⟩ :=
    CompositionZeroFreeCollar.result head tail
  obtain ⟨ρ, hρ, hρ1, _hcontinued, _hlimit, upper, lower, hupper,
      hlower, hupperEq, hlowerEq, hupperOne, _hlowerOne, _hconj, hsign⟩ :=
    CompositionBanks.result head tail ell
  let R := 1 + min (R0 - 1) ρ / 2
  have hmin : 0 < min (R0 - 1) ρ := lt_min (by linarith) hρ
  have hmin0 := min_le_left (R0 - 1) ρ
  have hminρ := min_le_right (R0 - 1) ρ
  have hR : 1 < R := by dsimp [R]; linarith
  have hRR0 : R < R0 := by dsimp [R]; linarith
  have hRρ : R < 1 + ρ := by dsimp [R]; linarith
  have hagree : ∀ z : ℂ, ‖z - 1‖ ≤ ρ →
      upper z = (z ^ CompositionDisk.depth tail /
        CompositionContinuation.continued (head :: tail) z) ^ (ell : ℕ) →
      upper z = reciprocal head tail ell z := by
    intro z hz heq
    have hz0 : z ≠ 0 := by
      intro hz0
      subst z
      norm_num at hz
      linarith
    rw [reciprocal, CompositionZeroFreeCollar.normalizedContinuation, if_neg hz0]
    simpa only [inv_div] using heq
  have hc : ContinuousOn (fun x : ℝ ↦ -(upper (x : ℂ)).im) (Icc 1 R) := by
    apply (Complex.continuous_im.continuousOn.comp
      (hupper.comp Complex.continuous_ofReal.continuousOn ?_) (fun _ _ ↦ mem_univ _)).neg
    intro x hx
    refine ⟨?_, by simp⟩
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - 1)]
    linarith [hx.2]
  have hn : ∀ x ∈ Icc (1 : ℝ) R, 0 ≤ -(upper (x : ℂ)).im := by
    intro x hx
    by_cases hx1 : x = 1
    · subst x
      rw [Complex.ofReal_one, hupperOne]
      split
      · have hreal :
            ((CompositionBoundary.zeta head tail : ℂ)⁻¹) ^ (ell : ℕ) =
              (((CompositionBoundary.zeta head tail)⁻¹ ^ (ell : ℕ) : ℝ) : ℂ) := by
          rw [Complex.ofReal_pow, Complex.ofReal_inv]
        rw [hreal]
        simpa only [Complex.ofReal_im, neg_zero] using (le_rfl : (0 : ℝ) ≤ 0)
      · simp
    · have hpos : 0 < x - 1 := by
        have : 1 < x := lt_of_le_of_ne hx.1 (Ne.symm hx1)
        linarith
      have hs := hsign (x - 1) hpos (by linarith [hx.2])
      have heq : 1 + ((x - 1 : ℝ) : ℂ) = (x : ℂ) := by push_cast; ring
      rw [heq] at hs
      linarith
  have hp : ∀ x ∈ Ioo (1 : ℝ) R, 0 < -(upper (x : ℂ)).im := by
    intro x hx
    have hs := hsign (x - 1) (by linarith [hx.1]) (by linarith [hx.2])
    have heq : 1 + ((x - 1 : ℝ) : ℂ) = (x : ℂ) := by push_cast; ring
    rw [heq] at hs
    linarith
  have hanalyticA : AnalyticOnNhd ℂ (reciprocal head tail ell)
      {z | z ∈ CompositionContinuation.omega ∧ ‖z‖ < R0} := by
    intro z hz
    exact ((hanalytic z hz.1).inv (hnonzero z hz.1 hz.2)).pow _
  have hupperA : ∀ z, ‖z - 1‖ ≤ ρ → 0 ≤ z.im →
      z ∈ CompositionContinuation.omega → upper z = reciprocal head tail ell z := by
    intro z hz hi ho
    exact hagree z hz (hupperEq z hz hi ho)
  have hlowerA : ∀ z, ‖z - 1‖ ≤ ρ → z.im ≤ 0 →
      z ∈ CompositionContinuation.omega → lower z = reciprocal head tail ell z := by
    intro z hz hi ho
    have hz0 : z ≠ 0 := by
      intro he; subst z; norm_num at hz; linarith
    rw [hlowerEq z hz hi ho, reciprocal,
      CompositionZeroFreeCollar.normalizedContinuation, if_neg hz0, inv_div]
  refine ⟨R0, ρ, R, upper, hR0, hρ, hρ1, hR, hRR0, hRρ, ?_, ?_, ?_,
    hupper, hupperA, hupperOne, ?_, ?_⟩
  · exact hanalyticA
  · intro z hz
    simp only [reciprocal, hdisk z hz]
  · simp [reciprocal, CompositionZeroFreeCollar.normalizedContinuation]
  · exact outer_bound (reciprocal head tail ell) upper lower R0 ρ R hR hRR0 hRρ
      hanalyticA.continuousOn hupper hlower hupperA hlowerA
  · intro B
    have he := FiniteSlitBankMoments.bank_dominance
      (fun x : ℝ ↦ -(upper (x : ℂ)).im) R hR hc hn hp B
    filter_upwards [he] with n hn'
    simp only [neg_div, intervalIntegral.integral_neg] at hn'
    linarith

#print axioms result

end D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitCompositionMoments
