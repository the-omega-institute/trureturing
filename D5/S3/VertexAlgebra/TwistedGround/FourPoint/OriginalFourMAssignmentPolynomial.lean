/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignmentPolynomial
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignmentPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial realization of the native mode assignment sums. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAssignedOccupation

/-! Multiplication of the surviving linear creators implements the independent
mode assignments inside the factorial-weighted affine readout. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAssignmentPolynomial

open LatticeGeneratingFieldLocality LatticeHalfFock
open FourPoint.OriginalFourMActualChart
open OriginalFourMFixedChargeWick (Mode nativeModeCovariance nativeModeMean modeMatrix)
open OriginalFourMAssignedOccupation
open OriginalGaussianSourceRestriction (CompactExternal)
open AffineWickAssignments (assign)
open AffineOccurrenceWick (wick affineMoment_eq_wick)
open OriginalChargedRowSource (affineMoment_coefficient)
open NativeAffineExternalCoefficient (jetOccupation)
open FactorialFockMetric (weight)
open MvPolynomial

variable {X J I : Type*} [Fintype J]

/-- Expand the surviving linear creators in one common oscillator algebra. -/
def assignmentPolynomial (U : Matrix X J ℂ) (f : J → I) (l : List X) : MvPolynomial I ℂ :=
  (l.map fun a => ∑ j, U a j • MvPolynomial.X (f j)).prod

omit [Fintype J] in
private theorem word_product (f : J → I) (l : List J) :
    (l.map fun j => (MvPolynomial.X (f j) : MvPolynomial I ℂ)).prod =
      monomial (jetOccupation (l.map f)) 1 := by
  induction l with
  | nil => simp [jetOccupation]
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, jetOccupation]
    rw [ih, MvPolynomial.X, monomial_mul_monomial, one_mul, add_comm]

/-- The assignment sum is the linear readout of the product of the
surviving creators. Repetition is carried by polynomial multiplication. -/
theorem assign_polynomial (U : Matrix X J ℂ) (f : J → I) (l : List X)
    (R : MvPolynomial I ℂ →ₗ[ℂ] ℂ) :
    assign U l (fun w => R (monomial (jetOccupation (w.map f)) 1)) =
      R (assignmentPolynomial U f l) := by
  simp_rw [← word_product]
  induction l generalizing R with
  | nil => rfl
  | cons a l ih =>
    simp only [assign, List.map_cons, List.prod_cons]
    have he (j : J) := ih (R.comp (LinearMap.mulLeft ℂ (MvPolynomial.X (f j) : MvPolynomial I ℂ)))
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at he
    simp only [he, assignmentPolynomial, List.map_cons, List.prod_cons,
      Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, smul_eq_mul]

/-- Evaluation against the actual affine coefficient array with the ordinary
Fock weight at every occupation. -/
def affineReadout [Fintype I] (K : Matrix I I ℂ) (μ : I → ℂ) : MvPolynomial I ℂ →ₗ[ℂ] ℂ :=
  (Finsupp.lsum ℂ fun d => ((weight d : ℂ) *
    OriginalChargedRowSource.affineCoefficient K μ d) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

omit [Fintype J] in
private theorem affineReadout_monomial [Fintype I] (K : Matrix I I ℂ) (μ : I → ℂ)
    (d : I →₀ ℕ) :
    affineReadout K μ (monomial d 1) = OriginalChargedRowSource.affineMoment K μ d := by
  classical
  rw [affineMoment_coefficient]
  simp [affineReadout, monomial, AddMonoidAlgebra.lsingle]

omit [Fintype J] in
/-- The native factor is the readout of the product of the surviving
oscillator creators in their actual compact leg and orientation coordinates. -/
theorem native_part_polynomial [Fintype X] [DecidableEq X] (D : LatticeData)
    (q : Charge D) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hc : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) (l : List X) :
    assign (modeMatrix c x slot n) l
      (wick (nativeModeCovariance D c x slot colour n) (nativeModeMean D q c x slot colour n)) =
    affineReadout (compactCovariance D c x F) (compactMean D q c x F)
      (assignmentPolynomial (modeMatrix c x slot n) (compactMode D c slot colour F hF) l) := by
  let K := compactCovariance D c x F
  let μ := compactMean D q c x F
  let f := compactMode D c slot colour F hF
  have hs (a b) : K a b = K b a := by
    rcases hc with ⟨hc, hr⟩ | rfl
    · exact compactCovariance_ab_symm D c x F hc hr a b
    · exact compactCovariance_d_symm D hx hx₁ F a b
  have ⟨hK, hμ⟩ := mode_array_pullback D q c x slot colour F hF
  rw [hK, hμ, ← assign_polynomial]
  congr 1
  funext w
  rw [affineReadout_monomial, affineMoment_eq_wick _ _ hs f]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAssignmentPolynomial
