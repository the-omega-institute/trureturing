import D5.S3.Weil.ZetaGamma.FormCore.ThetaFullFourthNegativeCheck
import D5.S3.Weil.ZetaGamma.FormCore.ThetaLogCalculusCheck
import Mathlib.Tactic

noncomputable section
/- Uncompiled actual consumer. Append after ThetaFullJetGlobal and the
   GenericLogFourthJets / EvenLogFourthSquareConcavity suppliers.
   Every analytic premise below is paid by the literal full-theta kernel. -/

namespace RhTransient.ThetaLogFourthCertificate

open Real Set
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Zeros.Jensen.SourceThetaMomentBounds
open RhTransient.GenericLogFourthJets
open RhTransient.EvenLogFourthSquareConcavity
open private fullJet fullJet_deriv from
  D5.S3.Weil.ZetaGamma.FormCore.GaussianGammaDomainCheck

/-- The exact Csordas radial curvature target and square-variable strict
    concavity for the original theta kernel. No curvature hypothesis,
    finite-mode truncation, or RH hypothesis is introduced. -/
theorem actual_phi_radial_curvature_and_squareConcavity :
    (∀ x : ℝ, 0 < x →
      0 < x*((iteratedDeriv 1 romikPhi x)^2-
        romikPhi x*iteratedDeriv 2 romikPhi x)+
          romikPhi x*iteratedDeriv 1 romikPhi x) ∧
    StrictConcaveOn ℝ (Ioi (0:ℝ)) (fun r : ℝ => Real.log (romikPhi (Real.sqrt r))) := by
  have hpos (x : ℝ) : 0 < fullJet 0 x := by
    rw [actual_fullJet_zero_eq_phi_all,romikPhi_eq_source]
    exact (source_theta_gaussian_bound x).1
  let ell0 : ℝ → ℝ := fun x => Real.log (fullJet 0 x)
  let ell1 : ℝ → ℝ := logJet1 (fullJet 0) (fullJet 1)
  let ell2 : ℝ → ℝ := logJet2 (fullJet 0) (fullJet 1) (fullJet 2)
  let ell3 : ℝ → ℝ := logJet3 (fullJet 0) (fullJet 1) (fullJet 2) (fullJet 3)
  let ell4 : ℝ → ℝ :=
    logJet4 (fullJet 0) (fullJet 1) (fullJet 2) (fullJet 3) (fullJet 4)
  have hlog (x : ℝ) := hasDerivAt_log_four_jets
    (fullJet 0) (fullJet 1) (fullJet 2) (fullJet 3) (fullJet 4)
    (fullJet_deriv 0 x) (fullJet_deriv 1 x) (fullJet_deriv 2 x) (fullJet_deriv 3 x)
    (hpos x).ne'
  have h10 : ell1 0 = 0 := by
    dsimp [ell1,logJet1]
    rw [actual_fullJet_odd_origin.1]
    simp
  have h30 : ell3 0 = 0 := by
    dsimp [ell3,logJet3]
    rw [actual_fullJet_odd_origin.1,actual_fullJet_odd_origin.2]
    simp
  have h4neg (x : ℝ) (hx : 0 < x) : ell4 x < 0 := by
    change fourthNumerator (fullJet 0 x) (fullJet 1 x) (fullJet 2 x)
      (fullJet 3 x) (fullJet 4 x)/(fullJet 0 x)^4 < 0
    exact div_neg_of_neg_of_pos (actual_fullJet_fourthNumerator_negative hx.le)
      (pow_pos (hpos x) 4)
  have h := squareVariable_strictConcavity_of_fourthJet_neg ell0 ell1 ell2 ell3 ell4
    (fun x _ => (hlog x).1)
    (fun x _ => (hlog x).2.1)
    (fun x _ => (hlog x).2.2.1)
    (fun x _ => (hlog x).2.2.2)
    h10 h30 h4neg
  refine ⟨?_,?_⟩
  · intro x hx
    have hg := mul_pos (pow_pos (hpos x) 2) (h.1 x hx)
    have heq :
        (fullJet 0 x)^2*(ell1 x-x*ell2 x) =
          x*((fullJet 1 x)^2-fullJet 0 x*fullJet 2 x)+fullJet 0 x*fullJet 1 x := by
      dsimp [ell1,ell2,logJet1,logJet2]
      field_simp [(hpos x).ne']
      ring
    rw [heq] at hg
    rw [actual_fullJet_eq_phi_iterated_all 0,actual_fullJet_eq_phi_iterated_all 1,
      actual_fullJet_eq_phi_iterated_all 2] at hg
    simpa only [iteratedDeriv_zero] using hg
  · simpa only [ell0,actual_fullJet_zero_eq_phi_all] using h.2

end RhTransient.ThetaLogFourthCertificate

#print axioms RhTransient.ThetaLogFourthCertificate.actual_phi_radial_curvature_and_squareConcavity
