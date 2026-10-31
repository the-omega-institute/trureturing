import D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Full original-telescope symmetry observation, with a genuine nonsymmetric
bilinear form witnessing dependence. The original actualForm is not replaced. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped TensorProduct

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry

attribute [local instance] Classical.propDecidable

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.VertexAlgebra.LatticeHalfFock
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open _root_.D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry

abbrev Parameters := {D : LatticeData // IsUnit D.G.det}
abbrev Form (p : Parameters) := LinearMap.BilinForm ℂ (ActualTensor p.1 p.2)
abbrev signature := Reg.Support.SingleDependentReadout.signature
  Parameters Form (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ B => decide B.IsSymm) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det),
    R.readout () ⟨D, hu⟩ (actualForm D hu) = true

theorem sourceBridge : (type_of% (@actualForm_symmetric)) ↔ arena.Law actual := by
  constructor
  · intro h D hu
    exact decide_eq_true (h D hu)
  · intro h D hu
    exact of_decide_eq_true (h D hu)

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact Fin.elim0 i

private theorem emptyUnit : IsUnit emptyLattice.G.det := by
  change IsUnit (0 : Matrix (Fin 0) (Fin 0) ℤ).det
  simp

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact Bool.false_ne_true (h emptyLattice emptyUnit)

private def hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  even_diagonal := by intro i; fin_cases i <;> exact ⟨0, rfl⟩

private theorem hyperbolicUnit : IsUnit hyperbolic.G.det := by
  change IsUnit (!![(0 : ℤ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det
  norm_num [Matrix.det_fin_two]

private def asymmetric (D : LatticeData) (hu : IsUnit D.G.det) :
    LinearMap.BilinForm ℂ (ActualTensor D hu) :=
  LinearMap.BilinForm.tmul
    ((LinearMap.mul ℂ ℂ).compl₁₂
      (MvPolynomial.lcoeff ℂ (0 : Index D →₀ ℕ))
      (MvPolynomial.lcoeff ℂ (0 : Index D →₀ ℕ)))
    ((LinearMap.mul ℂ ℂ).compl₁₂
      (LinearMap.proj (0 : Half (groundRank D hu)))
      (LinearMap.proj (1 : Half (groundRank D hu))))

private theorem asymmetric_not_symmetric :
    ¬ (asymmetric hyperbolic hyperbolicUnit).IsSymm := by
  classical
  have rank_eq : 2 = groundRank hyperbolic hyperbolicUnit +
      groundRank hyperbolic hyperbolicUnit :=
    (Classical.choose_spec (Classical.choose_spec
      (actual_twisted_ground_representation hyperbolic hyperbolicUnit))).1
  have positive : 0 < groundRank hyperbolic hyperbolicUnit := by omega
  have distinct : (0 : Half (groundRank hyperbolic hyperbolicUnit)) ≠ 1 := by
    intro h
    have point := congrFun h ⟨0, positive⟩
    exact zero_ne_one point
  intro h
  have value := h.eq
    ((1 : Oscillator hyperbolic) ⊗ₜ[ℂ]
      (Pi.single 0 1 : ActualGround hyperbolic hyperbolicUnit))
    ((1 : Oscillator hyperbolic) ⊗ₜ[ℂ]
      (Pi.single 1 1 : ActualGround hyperbolic hyperbolicUnit))
  norm_num [asymmetric, LinearMap.BilinForm.tensorDistrib_tmul,
    LinearMap.compl₁₂_apply, LinearMap.proj_apply,
    distinct, Ne.symm distinct] at value

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨hyperbolic, hyperbolicUnit⟩, 0, asymmetric hyperbolic hyperbolicUnit, ?_⟩
  change decide (0 : Form ⟨hyperbolic, hyperbolicUnit⟩).IsSymm ≠
    decide (asymmetric hyperbolic hyperbolicUnit).IsSymm
  simp [LinearMap.BilinForm.isSymm_zero, asymmetric_not_symmetric]

def family : Registration arena (type_of% (@actualForm_symmetric)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp actualForm_symmetric, rejected, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actualForm_symmetric)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry.actualForm_symmetric
    "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms sourceBridge
#print axioms family
#print axioms audit

end Reg.D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry
