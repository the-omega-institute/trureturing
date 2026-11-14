import D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact source-type mirrors preserve the original theorem telescopes. A mirror
is compiled audit evidence, not a four-slot registration or a binding verdict. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource

abbrev sourceScope_recompositionAmplitude_eq := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource.recompositionAmplitude_eq.{u})
theorem source_actual_recompositionAmplitude_eq : sourceScope_recompositionAmplitude_eq.{u} :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource.recompositionAmplitude_eq.{u}

abbrev sourceScope_original_corrected_gaussian_row := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource.original_corrected_gaussian_row)
theorem source_actual_original_corrected_gaussian_row : sourceScope_original_corrected_gaussian_row :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource.original_corrected_gaussian_row

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open TwistedGround OriginalFourMChargeCoset SignedOscillatorWick
open OriginalChargedRowSource OriginalNormalRowSource OriginalCorrectedRowRecompositionSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace CorrectedRow

structure Parameters where
  lattice : LatticeData
  unit : IsUnit lattice.G.det
  charge : Charge lattice
  source : Index lattice →₀ ℕ
  input : Index lattice →₀ ℕ
  detector : Index lattice →₀ ℕ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameters (fun _ => ℤ) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p e => wick p.lattice (MvPolynomial.monomial p.detector 1)
    (oscillatorCorrected p.lattice p.unit p.charge e
      (MvPolynomial.monomial p.source 1) (MvPolynomial.monomial p.input 1)))
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (alpha beta gamma : Index D →₀ ℕ) (e : ℤ),
    R.readout () ⟨D, hu, a, alpha, beta, gamma⟩ e =
      let K := rowSupport D alpha beta gamma
      let label := supportLabel D K
      (FactorialFockMetric.weight alpha : ℂ) * (FactorialFockMetric.weight beta : ℂ) *
        (FactorialFockMetric.weight gamma : ℂ) *
        affineLaurent (correctedMatrix D label) (correctedMean D a label)
          (normalWeight D label)
          (threeOccupation (restricted D K alpha) (restricted D K beta)
            (restricted D K gamma)) (e+chargeNorm D a)

theorem source_bridge : sourceScope_original_corrected_gaussian_row ↔ arena.Law actual :=
  Iff.rfl

theorem positive : arena.Law actual :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource.original_corrected_gaussian_row

def emptyLattice : LatticeData where
  rank := 0
  G := fun i => Fin.elim0 i
  symmetric := by intro i; exact Fin.elim0 i
  even_diagonal := by intro i; exact Fin.elim0 i

theorem empty_unit : IsUnit emptyLattice.G.det := by
  simp [emptyLattice]

def rejected : Realization signature := realize signature
  (fun role p e => actual.readout role p e + 1) (fun empty => nomatch empty)

theorem negative : ¬ arena.Law rejected := by
  intro h
  have bad := h emptyLattice empty_unit 0 0 0 0 0
  have good := positive emptyLattice empty_unit 0 0 0 0 0
  change actual.readout () ⟨emptyLattice, empty_unit, 0, 0, 0, 0⟩ 0 + 1 = _ at bad
  have eqn := bad.trans good.symm
  have shifted : actual.readout () ⟨emptyLattice, empty_unit, 0, 0, 0, 0⟩ 0 + 1 =
      actual.readout () ⟨emptyLattice, empty_unit, 0, 0, 0, 0⟩ 0 + 0 := by
    simpa only [add_zero] using eqn
  exact one_ne_zero (add_left_cancel shifted)

theorem vacuum (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ) :
    actual.readout () ⟨D, hu, 0, 0, 0, 0⟩ e = if e = 0 then 1 else 0 := by
  have h := positive D hu 0 0 0 0 e
  simp [rowSupport, restricted, threeOccupation, affineLaurent, affineCoefficient,
    FactorialFockMetric.weight, chargeNorm, bilinear] at h
  simp only [Finsupp.single_apply, eq_comm (a := (0 : ℤ)) (b := e)] at h
  simpa [FactorialFockQuadraticEstimate.gaussianCoefficient,
    FactorialFockQuadraticEstimate.gaussianPiece] using h

theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨⟨emptyLattice, empty_unit, 0, 0, 0, 0⟩, 0, 1, ?_⟩
  rw [vacuum, vacuum]
  norm_num

def family : Registration arena sourceScope_original_corrected_gaussian_row where
  actual := actual
  bridge := source_bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource.original_corrected_gaussian_row)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource.CorrectedRow.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource.CorrectedRow.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end CorrectedRow
end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource
