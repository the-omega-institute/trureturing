import D5.S3.VertexAlgebra.TransverseMetric.RealAdaptedFrame
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.TransverseMetric.RealAdaptedFrame

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
  _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
  _root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric
  _root_.D5.S3.VertexAlgebra.OriginalQQuartetSource
  _root_.D5.S3.VertexAlgebra.TransverseMetric.RealAdaptedFrame
  _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators Matrix

noncomputable section

abbrev Params : Type := Σ data : LatticeData, Matrix (Fin data.rank) (Fin data.rank) ℂ

abbrev signature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Params
    (fun parameter => Charge parameter.1) (fun parameter => Charge parameter.1)

def actual : Realization signature :=
  realize signature (fun _ _ beta => beta) (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := ∀ (data : LatticeData)
    (inverse : Matrix (Fin data.rank) (Fin data.rank) ℂ)
    (leftGramInverse : inverse * gramComplex data = 1)
    (rightGramInverse : gramComplex data * inverse = 1)
    (rank : 2 ≤ data.rank) (beta : Charge data) (chargeNonzero : beta ≠ 0)
    (lorentzian : _root_.D5.S3.QuadraticForms.ActualSignature.signature
      (gramReal data).toQuadraticForm' = (data.rank : ℤ) - 2),
    Nonempty (NativeFrame data inverse (observation.readout () ⟨data, inverse⟩ beta))

theorem exact_source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.TransverseMetric.RealAdaptedFrame.exists_native_frame)) ↔
      arena.Law actual := Iff.rfl

private abbrev witnessData : LatticeData where
  rank := 2
  G := fun first second => if first = second then 0 else 1
  symmetric := by intro first second; fin_cases first <;> fin_cases second <;> decide
  even_diagonal := by intro axis; simp

private def witnessInverse : Matrix (Fin witnessData.rank) (Fin witnessData.rank) ℂ :=
  gramComplex witnessData

private theorem witnessLeft : witnessInverse * gramComplex witnessData = 1 := by
  ext first second
  change (∑ index : Fin 2, witnessInverse first index * gramComplex witnessData index second) = _
  rw [Fin.sum_univ_two]
  fin_cases first <;> fin_cases second <;> apply Complex.ext <;>
    norm_num only [witnessInverse, Matrix.mul_apply, gramComplex, Matrix.map_apply,
      witnessData, Fin.sum_univ_two, Matrix.one_apply, Fin.ext_iff,
      Fin.val_zero, Fin.val_one, Fin.val_natCast, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, ite_true, ite_false]

private theorem witnessRight : gramComplex witnessData * witnessInverse = 1 := witnessLeft

private theorem witnessSignature :
    _root_.D5.S3.QuadraticForms.ActualSignature.signature
      (gramReal witnessData).toQuadraticForm' = (witnessData.rank : ℤ) - 2 := by
  apply (_root_.D5.S3.QuadraticForms.ActualSignature.realizes_iff_signature
    2 (gramReal witnessData) (by
      intro first second
      exact congrArg (fun value : ℤ => (value : ℝ)) (witnessData.symmetric first second)) 0).mp
  refine Or.inr (Or.inr ⟨?_, 0, 0, ?_, ?_⟩)
  · intro axis
    simp [gramReal]
  · norm_num [gramReal, witnessData, Fin.succAbove, Fin.ext_iff]
  · rfl

private def witnessParams : Params :=
  ⟨witnessData, witnessInverse⟩

private def witnessCharge : Charge witnessData := fun _ => 1

private theorem witnessNonzero : witnessCharge ≠ 0 := by
  intro vanished
  have equality := congrFun vanished 0
  norm_num [witnessCharge] at equality

private theorem zeroExcluded (parameter : Params) :
    ¬ Nonempty (NativeFrame parameter.1 parameter.2 0) := by
  rintro ⟨frame⟩
  apply frame.chosenNonzero
  simp [chosenP, complexCharge, gramPair]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := law witnessData witnessInverse witnessLeft witnessRight (by decide)
    witnessCharge witnessNonzero witnessSignature
  exact zeroExcluded witnessParams impossible

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨witnessParams, 0, witnessCharge, ?_⟩
  change (0 : Charge witnessData) ≠ witnessCharge
  exact Ne.symm witnessNonzero

def familyRegistration : Registration arena
    (type_of%
      (@_root_.D5.S3.VertexAlgebra.TransverseMetric.RealAdaptedFrame.exists_native_frame)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp exists_native_frame, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.TransverseMetric.RealAdaptedFrame.exists_native_frame)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName :=
    `D5.S3.VertexAlgebra.TransverseMetric.RealAdaptedFrame.exists_native_frame.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TransverseMetric.RealAdaptedFrame.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TransverseMetric.RealAdaptedFrame
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms familyRegistration

end
end Reg.D5.S3.VertexAlgebra.TransverseMetric.RealAdaptedFrame
