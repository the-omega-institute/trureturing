/- GID: D5/S3/VertexAlgebra/LatticeChargedAdjointSanityTransient
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeChargedAdjointSanityTransient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transient applications of native charged coefficient adjoints. -/

import D5.S3.VertexAlgebra.LatticeChargedFockForms

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeChargedAdjointSanityTransient

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeInvolution
open LatticeOscillatorFockForm LatticeChargedFockForms LatticeConvolutionFockAdjoint
open LatticeActualProductKernel MvPolynomial
open scoped VertexOperator

noncomputable section

private def gramTwo : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intro left right; rfl
  even_diagonal := by intro axis; exact ⟨1, by norm_num⟩

private def gramFour : LatticeData where
  rank := 1
  G := fun _ _ => 4
  symmetric := by intro left right; rfl
  even_diagonal := by intro axis; exact ⟨2, by norm_num⟩

private def rankZero : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro axis; exact Fin.elim0 axis
  even_diagonal := by intro axis; exact Fin.elim0 axis

example : paritySign (bilinear gramTwo (fun _ => 1) (fun _ => 1) / 2) = -1 := by
  have self_pairing : bilinear gramTwo (fun _ => 1) (fun _ => 1) = 2 := by decide
  rw [self_pairing]
  change (if Even (1 : ℤ) then (1 : ℂ) else -1) = -1
  rw [if_neg (by decide)]

example (left right : Carrier gramTwo) :
    hermitianForm gramTwo (((actualField gramTwo (fun _ => 1))[[-1]]) left) right =
      -hermitianForm gramTwo left (((actualField gramTwo (fun _ => -1))[[1]]) right) := by
  have self_pairing : bilinear gramTwo (fun _ => 1) (fun _ => 1) = 2 := by
    decide
  have phase : paritySign ((2 : ℤ) / 2) = -1 := by
    change (if Even (1 : ℤ) then (1 : ℂ) else -1) = -1
    exact if_neg (show ¬Even (1 : ℤ) by decide)
  have reflection : (2 : ℤ) - (-1) - 2 = 1 := by norm_num
  have native := hermitian_charged gramTwo (fun _ => 1) (-1) left right
  rw [self_pairing, phase, reflection, neg_one_mul] at native
  exact native

example (left right : Carrier gramFour) :
    hermitianForm gramFour (((actualField gramFour (fun _ => 1))[[-1]]) left) right =
      hermitianForm gramFour left (((actualField gramFour (fun _ => -1))[[3]]) right) := by
  have self_pairing : bilinear gramFour (fun _ => 1) (fun _ => 1) = 4 := by
    decide
  have phase : paritySign ((4 : ℤ) / 2) = 1 := by
    change (if Even (2 : ℤ) then (1 : ℂ) else -1) = 1
    exact if_pos (show Even (2 : ℤ) by decide)
  have reflection : (4 : ℤ) - (-1) - 2 = 3 := by norm_num
  have native := hermitian_charged gramFour (fun _ => 1) (-1) left right
  rw [self_pairing, phase, reflection, one_mul] at native
  exact native

private theorem vacuum_fixed (D : LatticeData) : pct D (vacuum D) = vacuum D := by
  change thetaLinear D (coefficientConjugation D (Finsupp.single 0 1)) = Finsupp.single 0 1
  have conjugated : coefficientConjugation D (Finsupp.single 0 1) =
      Finsupp.single 0 (conjugatePolynomial D 1) := by
    run_tac
      let supplier := (Lean.Name.num
        `_private.D5.S3.VertexAlgebra.LatticeChargedFockForms 0).append
        `D5.S3.VertexAlgebra.LatticeChargedFockForms.conjugation_single
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($(Lean.mkIdent supplier))))
  rw [conjugated]
  simp [conjugatePolynomial, theta_single]

example (D : LatticeData) : pct D (Complex.I • vacuum D) = -Complex.I • vacuum D := by
  rw [LinearMap.map_smulₛₗ, vacuum_fixed]
  change star Complex.I • vacuum D = -Complex.I • vacuum D
  rw [Complex.star_def, Complex.conj_I]

example (left right : ℂ) :
    fockForm rankZero (C left) (C right) = star left * right := by
  rw [C_eq_smul_one (a := left), LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    fockForm_vacuum_left] <;>
      simp only [constantCoeff_C, starRingEnd_apply, smul_eq_mul]

example (index : ℤ) (left right : Oscillator rankZero) :
    fockForm rankZero (convolution rankZero 0 index (translatedPolynomial rankZero 0 left)) right =
      fockForm rankZero left
        (convolution rankZero 0 (-index) (translatedPolynomial rankZero 0 right)) := by
  simpa only [neg_zero] using convolution_transpose rankZero 0 index left right

end
end D5.S3.VertexAlgebra.LatticeChargedAdjointSanityTransient
