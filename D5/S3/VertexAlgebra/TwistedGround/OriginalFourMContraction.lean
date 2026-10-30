/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalFourMContraction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalFourMContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit original-source contraction of the native four twisted tensor coefficient. -/

import D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
import D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

/-! Algebraic four-M scalar contraction on the unchanged original carriers.
The source inverse is the existing fixed-grade pairing equivalence, transported
only across the order of its two subtypes. The actual homogeneous kernel gives
the ambient functional whose restriction is the normalized mixed coefficient.
No common rational channel, analytic crossing or three-M cancellation is assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open LatticeAllStateField LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockGradedTrace
open LatticeHalfFockCorrectedField ActualChargedAdjoint CorrectedInversion
open HalfFock.LatticeHalfFockParityField HalfFock.ActualEnergyCovariance
open SourceBPZ.OriginalSourcePairing SourceBPZ.SourcePairingLaws
open SourceBPZ.OriginalSourceCoevaluation
open private gradeOrderEquiv theta_projection from
  D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
open private kernel homogeneous_coefficient ambientCoefficient liftGrade from
  D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

private def sourceGradePairingEquiv (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ) :
    fixedGrade D h ≃ₗ[ℂ] Module.Dual ℂ (fixedGrade D h) :=
  let e := gradeOrderEquiv D h
  (e.symm.trans (FixedGradedDuality.fixedGradeDualEquiv D (sourcePairing D)
    (sourcePairing_nondegenerate D hu) (theta_projection D)
    (sourcePairing_theta D)
    (fun m n x y hx hy hmn => sourcePairing_grade D m n hmn x y hx hy) hD h)).trans
      e.symm.dualMap

private theorem sourceGradePairingEquiv_evaluation (D : LatticeData)
    (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ)
    (f : Module.Dual ℂ (fixedGrade D h)) (y : fixedGrade D h) :
    sourcePairing D ((sourceGradePairingEquiv D hu hD h).symm f).val y.val = f y := by
  let e := gradeOrderEquiv D h
  have he := FixedGradedDuality.fixedGradeDualEquiv_ambient_evaluation D
    (sourcePairing D) (sourcePairing_nondegenerate D hu) (theta_projection D)
    (sourcePairing_theta D)
    (fun m n x y hx hy hmn => sourcePairing_grade D m n hmn x y hx hy)
    hD h (f.comp e.toLinearMap) (e.symm y)
  exact he

private theorem native_kernel_restriction (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (k : ℤ)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (a : fixedGrade D ((H : ℤ)+(K : ℤ)-k-1)) :
    normalizedCoefficient D hu k u v ((H : ℤ)+(K : ℤ)-k-1) a =
      kernel D hu H K k u.val v.val a.val := by
  change ambientCoefficient D hu k u.val v.val _ a = _
  rw [homogeneous_coefficient D hu h24 H K k u.val v.val huH hvK]
  simp [liftGrade, DirectSum.lof_eq_of, DirectSum.of_apply,
    Submodule.dualRestrict_apply]

/-- The literal native four-M coefficient: the inverse of the normalized
coefficient is contracted with rho_t(a) = correctedField(a)[-2t-2].
The first identity exposes the single original half-average on the entire
charge/occupation fiber. The second retains the signed negative, genuine
vacuum and positive finite-frame branches. -/
theorem fourM_contraction (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (k t : ℤ) (u v : paritySpace D hu (-1))
    (w d : ActualTensor D hu)
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val) :
    let h : ℤ := (H : ℤ)+(K : ℤ)-k-1
    let f := normalizedCoefficient D hu k u v h
    let E := sourceGradePairingEquiv D hu hD h
    let x := E.symm f
    let F := kernel D hu H K k u.val v.val
    actualForm D hu d ((correctedField D hu x.val).coeff (-2*t-2) w) =
        (2 : ℂ)⁻¹ * ∑ᶠ a : EnergyFiber D h,
          (F (carrierBasis D a.val) + F (theta D (carrierBasis D a.val))) *
            actualForm D hu d
              ((correctedField D hu (dualCarrierBasis D a.val)).coeff (-2*t-2) w) ∧
    actualForm D hu d ((correctedField D hu x.val).coeff (-2*t-2) w) =
      if hh : h < 0 then 0 else if hz : h = 0 then
        f (hz.symm ▸ gradeVacuum D) *
          actualForm D hu d ((correctedField D hu (vacuum D)).coeff (-2*t-2) w)
      else ∑ᶠ a : EnergyFiber D h, f (fixedFrame D h a) *
        actualForm D hu d
          ((correctedField D hu (fixedDualFrame D h a).val).coeff (-2*t-2) w) := by
  dsimp only
  let h : ℤ := (H : ℤ)+(K : ℤ)-k-1
  let f := normalizedCoefficient D hu k u v h
  let x := (sourceGradePairingEquiv D hu hD h).symm f
  let F := kernel D hu H K k u.val v.val
  let g := K_R D hu (-2*t-2) d w
  have hx (y : fixedGrade D h) : sourcePairing D x.val y.val = f y :=
    sourceGradePairingEquiv_evaluation D hu hD h f y
  have hF (y : fixedGrade D h) : sourcePairing D x.val y.val = F y.val :=
    (hx y).trans (native_kernel_restriction D hu h24 H K k u v huH hvK y)
  exact ⟨inverse_contraction_half_average D hu hD h F g x hF,
    inverse_contraction_signed D hu hD h f g x hx⟩

end D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
