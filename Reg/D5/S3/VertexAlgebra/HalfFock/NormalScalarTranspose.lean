import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose

/-! Faithful dependent readout audit attempts for original scalar transpose.
The flat proof mentions a private mode-reflection helper; its unresolved audit
binding is recorded in issue #21197 without expanding the mathematical API. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFock
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open _root_.D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection (wordWeight sourceWeight Corr)
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)
open scoped BigOperators TensorProduct

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact Fin.elim0 i
private theorem emptyUnit : IsUnit emptyLattice.G.det := by
  change IsUnit (0 : Matrix (Fin 0) (Fin 0) ℤ).det
  simp
private def hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  even_diagonal := by intro i; fin_cases i <;> exact ⟨0, rfl⟩
private theorem hyperbolicUnit : IsUnit hyperbolic.G.det := by
  change IsUnit (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det
  simpa [Matrix.det_fin_two] using (isUnit_neg_one : IsUnit (-1 : ℤ))

namespace actual_current_transpose
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (k : ℤ) (x y : ActualTensor D hu),
    R.readout () () (actualForm D hu (tensorCurrent D (ActualGround D hu) i k x) y)
      (-actualForm D hu x (tensorCurrent D (ActualGround D hu) i (-k-1) y))
theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_current_transpose)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h hyperbolic hyperbolicUnit ⟨0, by decide⟩ 0 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_current_transpose)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_current_transpose, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_current_transpose) (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_current_transpose "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_current_transpose.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end actual_current_transpose

namespace actual_word_scalar_rectangle
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (F : NativeField D hu) (w : List (Index D)) (e : ℤ) (x y : ActualTensor D hu),
    R.readout () () (actualForm D hu ((wordField D hu F w).coeff e x) y)
      (∑ m ∈ scalarModeRectangle D hu w x y,
        actualForm D hu (flatCoefficient D hu F w m e x) y)
theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_word_scalar_rectangle)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h emptyLattice emptyUnit 0 [] 0 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_word_scalar_rectangle)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_word_scalar_rectangle, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_word_scalar_rectangle) (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_word_scalar_rectangle "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_word_scalar_rectangle.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end actual_word_scalar_rectangle

namespace jetScalar_reflection
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (r : ℕ) (k : ℤ),
    R.readout () () (jetScalar r (-k-1))
      ((-1 : ℂ)^r *
      ∑ s ∈ Finset.range (r+1), ((r+1).choose (s+1) : ℂ) * jetScalar s k)
theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.jetScalar_reflection)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.jetScalar_reflection)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.jetScalar_reflection, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.jetScalar_reflection) (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.jetScalar_reflection "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.jetScalar_reflection.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end jetScalar_reflection

/- The actual_flat_transpose audit was attempted with the exact original
   telescope. Its private reflectModes term cannot be named here. Issue #21197
   records that missing binding; no new public reflection API is introduced. -/

namespace actual_word_transpose
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) (e : ℤ) (x y : ActualTensor D hu),
    R.readout () () (actualForm D hu ((chargedWordField D hu a w).coeff e x) y)
      (∑ s : JetTuple D w,
        paritySign (bilinear D a a / 2) * triangleCoefficient D w s *
          actualForm D hu x ((chargedWordField D hu a (lowerWord D w s)).coeff
            (transposeExponent D a w s e) y))
theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_word_transpose)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h emptyLattice emptyUnit 0 [] 0 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_word_transpose)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_word_transpose, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_word_transpose) (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_word_transpose "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_word_transpose.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end actual_word_transpose

namespace actual_polynomial_monomial_transpose
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (m : Index D →₀ ℕ) (e : ℤ) (x y : ActualTensor D hu),
    R.readout () () (actualForm D hu ((polynomialField D hu a (MvPolynomial.monomial m 1)).coeff e x) y)
      (∑ s : JetTuple D (occurrences D m),
        paritySign (bilinear D a a / 2) * triangleCoefficient D (occurrences D m) s *
          actualForm D hu x ((polynomialField D hu a
            (wordPolynomial D (lowerWord D (occurrences D m) s))).coeff
              (transposeExponent D a (occurrences D m) s e) y))
theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_polynomial_monomial_transpose)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h emptyLattice emptyUnit 0 0 0 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_polynomial_monomial_transpose)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_polynomial_monomial_transpose, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_polynomial_monomial_transpose) (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_polynomial_monomial_transpose "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_polynomial_monomial_transpose.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end actual_polynomial_monomial_transpose

namespace actual_source_scalar_transpose
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (v : Carrier D) (e : ℤ) (x y : ActualTensor D hu),
    R.readout () () (actualForm D hu ((sourceField D hu v).coeff e x) y)
      (∑ a ∈ v.support,
        ∑ m ∈ ((MvPolynomial.basisMonomials (Index D) ℂ).repr (v a)).support,
          ((MvPolynomial.basisMonomials (Index D) ℂ).repr (v a) m) *
            (paritySign (bilinear D a a / 2) *
              (-1 : ℂ)^(Finsupp.weight (sourceWeight D) m) *
                ∑ s : JetTuple D (occurrences D m),
                  binomialProduct D (occurrences D m) s *
                    actualForm D hu x ((sourceField D hu
                      (Finsupp.single a (wordPolynomial D (lowerWord D (occurrences D m) s)))).coeff
                        (-e-2*chargeNorm D a-4*(Finsupp.weight (sourceWeight D) m : ℤ)+
                          2*(weightLoss D (occurrences D m) s : ℤ)) y)))
theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_source_scalar_transpose)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h emptyLattice emptyUnit 0 0 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_source_scalar_transpose)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_source_scalar_transpose, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_source_scalar_transpose) (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_source_scalar_transpose "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_source_scalar_transpose.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end actual_source_scalar_transpose

namespace actual_corrected_scalar_normal_readout
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (v : Carrier D) (e : ℤ) (x y : ActualTensor D hu),
    R.readout () () (actualForm D hu ((correctedField D hu v).coeff e x) y)
      (∑ a ∈ v.support, ∑ c ∈ (Corr D a (v a)).support,
        ∑ m ∈ ((MvPolynomial.basisMonomials (Index D) ℂ).repr ((Corr D a (v a)) c)).support,
          ((MvPolynomial.basisMonomials (Index D) ℂ).repr ((Corr D a (v a)) c) m) *
            (paritySign (bilinear D a a / 2) * (-1 : ℂ)^(Finsupp.weight (sourceWeight D) m) *
              ∑ s : JetTuple D (occurrences D m),
                binomialProduct D (occurrences D m) s *
                  actualForm D hu x ((sourceField D hu
                    (Finsupp.single a (wordPolynomial D (lowerWord D (occurrences D m) s)))).coeff
                      (-(e+2*(c : ℤ))-2*chargeNorm D a-
                        4*(Finsupp.weight (sourceWeight D) m : ℤ)+
                        2*(weightLoss D (occurrences D m) s : ℤ)) y)))
theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_corrected_scalar_normal_readout)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h emptyLattice emptyUnit 0 0 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_corrected_scalar_normal_readout)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_corrected_scalar_normal_readout, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_corrected_scalar_normal_readout) (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_corrected_scalar_normal_readout "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose.actual_corrected_scalar_normal_readout.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end actual_corrected_scalar_normal_readout

end Reg.D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose
