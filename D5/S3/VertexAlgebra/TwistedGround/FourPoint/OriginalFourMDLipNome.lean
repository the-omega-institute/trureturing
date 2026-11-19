import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource

noncomputable section

open Complex Set Filter
open scoped Topology

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipNome

open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
open OriginalFourMPeriodSource
open private lipSign real_d_aux analyticAt_tau dLip_im_ne_zero
  mem_doubleSlit_of_im complement_mem from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource

/-- The continuation of the D period ratio on its indicated lip. -/
def dTau (upperA : Bool) (t : ℂ) : ℂ := -(tau (1 - t⁻¹) + lipSign upperA)⁻¹

/-- The native lattice nome near the D boundary, with the sign fixed by the
complementary period jump. -/
def dNome (upperA : Bool) (t : ℂ) : ℂ := Complex.exp (I * (Real.pi : ℂ) * dTau upperA t)

theorem dTau_eq_tau {upperA : Bool} {t : ℂ} (ht : t ∈ dLip upperA) :
    dTau upperA t = tau t := by
  have htd : t ∈ doubleSlit := mem_doubleSlit_of_im (dLip_im_ne_zero ht)
  have hP : slitPeriod (1 - t) ≠ 0 := slitPeriod_ne_zero (complement_mem htd)
  have hQ : slitPeriod t ≠ 0 := slitPeriod_ne_zero htd.1
  have he := dPeriod_eq_slit ht
  unfold dPeriod at he
  have hS : tau (1 - t⁻¹) + lipSign upperA ≠ 0 := by
    intro hs
    rw [hs, zero_mul, zero_div] at he
    exact hQ he.symm
  change -(tau (1 - t⁻¹) + lipSign upperA)⁻¹ = I * slitPeriod (1 - t) / slitPeriod t
  rw [← dPeriod_eq_slit ht, dPeriod, div_div_eq_mul_div]
  rw [show I * slitPeriod (1 - t) * I = -slitPeriod (1 - t) by
    rw [mul_comm I (slitPeriod (1 - t)), mul_assoc, I_mul_I, mul_neg_one]]
  field_simp [hP, hS]

theorem dNome_eq_exp {upperA : Bool} {t : ℂ} (ht : t ∈ dLip upperA) :
    dNome upperA t = Complex.exp (I * (Real.pi : ℂ) * tau t) := by
  rw [dNome, dTau_eq_tau ht]

private theorem tau_plus_lip_im_pos (upperA : Bool) {r : ℂ} (hr : r ∈ doubleSlit) :
    0 < (tau r + lipSign upperA).im := by
  cases upperA <;> simpa [lipSign] using tau_im_pos hr

theorem dNome_analyticAt (upperA : Bool) {t : ℝ} (ht : 1 < t) :
    AnalyticAt ℂ (dNome upperA) (t : ℂ) := by
  have h₀ : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hArg : AnalyticAt ℂ (fun u : ℂ => 1 - u⁻¹) (t : ℂ) :=
    analyticAt_const.sub (analyticAt_id.inv h₀)
  have hr := (real_d_aux ht).2
  have hs : tau (1 - (t : ℂ)⁻¹) + lipSign upperA ≠ 0 := by
    intro hz
    have hp := tau_plus_lip_im_pos upperA hr
    rw [hz, zero_im] at hp
    exact (lt_irrefl _) hp
  have hplus := ((analyticAt_tau hr).comp (f := fun u : ℂ => 1 - u⁻¹) hArg).add
    (g := fun _ => lipSign upperA) analyticAt_const
  exact (analyticAt_const.mul ((hplus.inv hs).neg)).cexp'

theorem dNome_norm_lt_one (upperA : Bool) {t : ℝ} (ht : 1 < t) :
    ‖dNome upperA (t : ℂ)‖ < 1 := by
  let s := tau (1 - (t : ℂ)⁻¹) + lipSign upperA
  have hs : 0 < s.im := tau_plus_lip_im_pos upperA (real_d_aux ht).2
  have hn : s ≠ 0 := by
    intro he
    simp [he] at hs
  have hd : 0 < (dTau upperA (t : ℂ)).im := by
    change 0 < (-s⁻¹).im
    rw [neg_im, inv_im, neg_div, neg_neg]
    exact div_pos hs (normSq_pos.mpr hn)
  rw [dNome, Complex.norm_exp, Real.exp_lt_one_iff]
  simpa [Complex.mul_re, Complex.mul_im] using
    (neg_neg_of_pos (mul_pos Real.pi_pos hd))

theorem dNome_subunit_near (upperA : Bool) {t : ℝ} (ht : 1 < t) :
    ∀ᶠ u in 𝓝 (t : ℂ), ‖dNome upperA u‖ < 1 :=
  (dNome_analyticAt upperA ht).continuousAt.norm.eventually_lt
    continuousAt_const (dNome_norm_lt_one upperA ht)

#print axioms dNome_eq_exp
#print axioms dNome_analyticAt
#print axioms dNome_subunit_near

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipNome
