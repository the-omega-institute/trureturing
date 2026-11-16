import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm

noncomputable section
open scoped BigOperators Topology
open Filter Metric
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open TwistedGround
open OriginalGaussianExternalBlocks OriginalGaussianSourceMeans OriginalGaussianDeterminant
open OriginalGaussianMatrix OriginalGaussianSourceGerm NativeAffineTransport OriginalChargedRowSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm

private abbrev hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  even_diagonal := by intro i; fin_cases i <;> exact ⟨0, rfl⟩
private theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
  have h : hyperbolic.G.det = -1 := by decide
  rw [h]
  exact isUnit_neg_one
private def labels : Unit → External hyperbolic := fun _ => (false, (0, 0))

abbrev ltSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def ltActual : Realization ltSignature := realize _ (fun _ _ x y => x < y) (fun e => nomatch e)
def ltBad : Realization ltSignature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem ltDependence : ObservationalDependence ltSignature ltActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 1
  have hh : (1 : ℝ) < 1 := Eq.mp he zero_lt_one
  exact (lt_irrefl _) hh

abbrev eqSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)
def eqActual : Realization eqSignature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def eqBad : Realization eqSignature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem eqDependence : ObservationalDependence eqSignature eqActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero he

abbrev diffSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ → ℂ)
    (fun _ => Prop)
def diffActual : Realization diffSignature :=
  realize _ (fun _ _ f => Differentiable ℂ f) (fun e => nomatch e)
def diffBad : Realization diffSignature :=
  realize _ (fun _ _ _ => False) (fun e => nomatch e)
private theorem diffDependence : ObservationalDependence diffSignature diffActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun z => z⁻¹), ?_⟩
  intro h
  have hd : Differentiable ℂ (fun z : ℂ => z⁻¹) := Eq.mp h (differentiable_const _)
  exact (differentiableAt_inv_iff.mp (hd 0)) rfl

namespace left_entry_differentiable
def arena : Arena where
  signature := diffSignature
  Law A := ∀ (X : Type) [Fintype X] [DecidableEq X] (D : LatticeData) (N : ℕ) (e : X → External D) (i j : Internal D N ⊕ X),
    A.readout () () (fun z => leftRow D N e z i j) 
private theorem bad_fails : ¬ arena.Law diffBad := by
  intro h
  exact h Unit hyperbolic 0 labels (.inr ()) (.inr ())
def evidence : Registration arena (type_of% (@left_entry_differentiable)) where
  actual := diffActual
  bridge := Iff.rfl
  variation := ⟨fun X _ _ D N e i j => left_entry_differentiable D N e i j, diffBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law diffActual diffBad bad_fails
  dependence := diffDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@left_entry_differentiable) (Realization diffSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.left_entry_differentiable.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.left_entry_differentiable.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize diffSignature diffActual.readout diffActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end left_entry_differentiable

namespace right_entry_differentiable
def arena : Arena where
  signature := diffSignature
  Law A := ∀ (X : Type) [Fintype X] [DecidableEq X] (D : LatticeData) (N : ℕ) (e : X → External D) (i j : Internal D N ⊕ X),
    A.readout () () (fun z => rightRow D N e z i j) 
private theorem bad_fails : ¬ arena.Law diffBad := by
  intro h
  exact h Unit hyperbolic 0 labels (.inr ()) (.inr ())
def evidence : Registration arena (type_of% (@right_entry_differentiable)) where
  actual := diffActual
  bridge := Iff.rfl
  variation := ⟨fun X _ _ D N e i j => right_entry_differentiable D N e i j, diffBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law diffActual diffBad bad_fails
  dependence := diffDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@right_entry_differentiable) (Realization diffSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.right_entry_differentiable.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.right_entry_differentiable.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize diffSignature diffActual.readout diffActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end right_entry_differentiable

namespace original_rows_contract_on_germ
def arena : Arena where
  signature := ltSignature
  Law A := ∀ (X : Type) [Fintype X] [DecidableEq X] (D : LatticeData) (N : ℕ) (e : X → External D),
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ z : ℂ, ‖z‖ ≤ r →
      A.readout () () ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        ((leftRow D N e z).submatrix Sum.inl Sum.inl)‖ 1 ∧
      A.readout () () ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        ((rightRow D N e z).submatrix Sum.inl Sum.inl)‖ 1 ∧
      A.readout () () ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (positiveInternal D N
        ((originalRow D N e).submatrix Sum.inl Sum.inl) ‖z‖)‖ 1 ∧
      A.readout () () ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (positiveInternal D N
        ((transportCovariance (sourceBlock (J := X) (inverseSubstitution D N))
          (originalRow D N e)).submatrix Sum.inl Sum.inl) ‖z‖)‖ 1
private theorem bad_fails : ¬ arena.Law ltBad := by
  intro h
  obtain ⟨r, hr, _, he⟩ := h Unit hyperbolic 0 labels
  exact (he 0 (by simpa using hr.le)).1
def evidence : Registration arena (type_of% (@original_rows_contract_on_germ)) where
  actual := ltActual
  bridge := Iff.rfl
  variation := ⟨fun X _ _ D N e => original_rows_contract_on_germ D N e, ltBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law ltActual ltBad bad_fails
  dependence := ltDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_rows_contract_on_germ) (Realization ltSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_rows_contract_on_germ.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_rows_contract_on_germ.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ltSignature ltActual.readout ltActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "body", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "body", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_rows_contract_on_germ

namespace original_rows_trace_power
def arena : Arena where
  signature := eqSignature
  Law A := ∀ (X : Type) [Fintype X] [DecidableEq X] (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ) (e : X → External D) (z : ℂ) (p : ℕ),
    A.readout () () (Matrix.trace (((leftRow D N e z).submatrix Sum.inl Sum.inl *
      (rightRow D N e z).submatrix Sum.inl Sum.inl) ^ p))
      ((D.rank : ℂ) * Matrix.trace (finiteSection N z ^ (2 * p)))
private theorem bad_fails : ¬ arena.Law eqBad := by
  intro h
  exact h Unit hyperbolic hyperbolic_unit 0 labels 0 0
def evidence : Registration arena (type_of% (@original_rows_trace_power)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun X _ _ D hu N e z p => original_rows_trace_power D hu N e z p, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_rows_trace_power) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_rows_trace_power.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_rows_trace_power.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_rows_trace_power

namespace original_rows_trace_prefactor
def arena : Arena where
  signature := eqSignature
  Law A := ∀ (X : Type) [Fintype X] [DecidableEq X] (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ) (e : X → External D) (z : ℂ),
    A.readout () () (Complex.exp ((1 / 2 : ℂ) * ∑' k : ℕ,
      Matrix.trace (((leftRow D N e z).submatrix Sum.inl Sum.inl *
        (rightRow D N e z).submatrix Sum.inl Sum.inl) ^ (k + 1)) / (k + 1 : ℂ)))
      (Complex.exp (-(D.rank : ℂ) / 2 * finiteLog N z))
private theorem bad_fails : ¬ arena.Law eqBad := by
  intro h
  exact h Unit hyperbolic hyperbolic_unit 0 labels 0
def evidence : Registration arena (type_of% (@original_rows_trace_prefactor)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun X _ _ D hu N e z => original_rows_trace_prefactor D hu N e z, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_rows_trace_prefactor) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_rows_trace_prefactor.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_rows_trace_prefactor.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_rows_trace_prefactor


namespace original_row_coefficients_scale
def arena : Arena where
  signature := eqSignature
  Law A := ∀ (X : Type) [Fintype X] [DecidableEq X] (D : LatticeData) (a : Charge D) (N : ℕ)
    (e : X → External D) (z : ℂ) (d : Internal D N →₀ ℕ) (h k : X →₀ ℕ),
    A.readout () () (affineCoefficient (leftRow D N e z) (leftMean D a N e z) (d.sumElim h))
      (z ^ internalEnergy D N d *
        affineCoefficient (originalRow D N e) (originalMean D a N e) (d.sumElim h)) ∧
    A.readout () () (affineCoefficient (rightRow D N e z) (rightMean D a N e z) (d.sumElim k))
      (z ^ internalEnergy D N d *
        affineCoefficient
          (transportCovariance (sourceBlock (J := X) (inverseSubstitution D N))
            (originalRow D N e)) (originalInverseMean D a N e) (d.sumElim k))
private theorem bad_fails : ¬ arena.Law eqBad := by
  intro h
  exact (h Unit hyperbolic 0 0 labels 0 0 0 0).1
def evidence : Registration arena (type_of% (@original_row_coefficients_scale)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun X _ _ D a N e z d h k => original_row_coefficients_scale D a N e z d h k, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_row_coefficients_scale) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_row_coefficients_scale.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_row_coefficients_scale.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_row_coefficients_scale

namespace original_row_product_scales
def arena : Arena where
  signature := eqSignature
  Law A := ∀ (X : Type) [Fintype X] [DecidableEq X] (D : LatticeData) (a : Charge D) (N : ℕ)
    (e : X → External D) (z : ℂ) (d : Internal D N →₀ ℕ) (h k : X →₀ ℕ),
    A.readout () () ((FactorialFockMetric.weight d : ℂ) *
      affineCoefficient (leftRow D N e z) (leftMean D a N e z) (d.sumElim h) *
      affineCoefficient (rightRow D N e z) (rightMean D a N e z) (d.sumElim k))
      (z ^ (2 * internalEnergy D N d) * ((FactorialFockMetric.weight d : ℂ) *
      affineCoefficient (originalRow D N e) (originalMean D a N e) (d.sumElim h) *
      affineCoefficient
        (transportCovariance (sourceBlock (J := X) (inverseSubstitution D N))
          (originalRow D N e)) (originalInverseMean D a N e) (d.sumElim k)))
private theorem bad_fails : ¬ arena.Law eqBad := by
  intro h
  exact h Unit hyperbolic 0 0 labels 0 0 0 0
def evidence : Registration arena (type_of% (@original_row_product_scales)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun X _ _ D a N e z d h k => original_row_product_scales D a N e z d h k, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_row_product_scales) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_row_product_scales.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_row_product_scales.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_row_product_scales

namespace original_occupation_scales
def arena : Arena where
  signature := eqSignature
  Law A := ∀ (X : Type) [Fintype X] [DecidableEq X] (D : LatticeData) (a : Charge D) (N : ℕ)
    (e : X → External D) (d : Internal D N →₀ ℕ) (z : ℂ) (x y : X → ℂ),
    A.readout () () (occupationTerm D a N e d (z, x, y))
      (z ^ (2 * internalEnergy D N d) * rawOccupationTerm D a N e d x y)
private theorem bad_fails : ¬ arena.Law eqBad := by
  intro h
  exact h Unit hyperbolic 0 0 labels 0 0 0 0
def evidence : Registration arena (type_of% (@original_occupation_scales)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun X _ _ D a N e d z x y => original_occupation_scales D a N e d z x y, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_occupation_scales) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_occupation_scales.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_occupation_scales.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_occupation_scales


abbrev leSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def leActual : Realization leSignature := realize _ (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def leBad : Realization leSignature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem leDependence : ObservationalDependence leSignature leActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) he

abbrev SourceParameter := Σ D : LatticeData, ℕ × Type
private abbrev ParameterSpace (p : SourceParameter) := ℂ × (p.2.2 → ℂ) × (p.2.2 → ℂ)
private abbrev ParameterPartial (p : SourceParameter) :=
  Finset (Internal p.1 p.2.1 →₀ ℕ) → ParameterSpace p → ℂ
abbrev sewingSignature : Signature where
  Params := SourceParameter ⊕ Unit
  State p := match p with
    | .inl p => ParameterPartial p
    | .inr _ => ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := match p with
    | .inl p => (ParameterSpace p → ℂ) → Set (ParameterSpace p) → Prop
    | .inr _ => ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def sewingActual : Realization sewingSignature := realize _
  (fun _ p => match p with
    | .inl _ => fun F f s => TendstoUniformlyOn F f Filter.atTop s
    | .inr _ => fun x y => x = y) (fun e => nomatch e)
def sewingBad : Realization sewingSignature := realize _
  (fun _ p => match p with
    | .inl _ => fun _ _ _ => False
    | .inr _ => fun _ _ => False) (fun e => nomatch e)
private theorem sewingDependence : ObservationalDependence sewingSignature sewingActual := by
  intro i
  refine ⟨.inr (), 0, 1, ?_⟩
  intro h
  have he : (1 : ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero he
private theorem sewingSensitivity (law : Realization sewingSignature → Prop)
    (hbad : ¬ law sewingBad) : Sensitivity ⟨sewingSignature, law⟩ sewingActual := by
  constructor
  · intro i
    refine ⟨sewingBad, ?_, ?_, hbad⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

abbrev meanSignature : Signature where
  Params := SourceParameter
  State p := Internal p.1 p.2.1 ⊕ p.2.2 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Internal p.1 p.2.1 ⊕ p.2.2 → ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def meanActual : Realization meanSignature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def meanBad : Realization meanSignature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem meanDependence : ObservationalDependence meanSignature meanActual := by
  intro i
  refine ⟨⟨hyperbolic, 0, Unit⟩, 0, 1, ?_⟩
  intro h
  have he : (1 : Internal hyperbolic 0 ⊕ Unit → ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  have hc : (1 : ℂ) = 0 := congrFun he (.inr ())
  exact one_ne_zero hc
private theorem meanSensitivity (law : Realization meanSignature → Prop)
    (hbad : ¬ law meanBad) : Sensitivity ⟨meanSignature, law⟩ meanActual := by
  constructor
  · intro i
    refine ⟨meanBad, ?_, ?_, hbad⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

namespace rightMean_raw
def arena : Arena where
  signature := meanSignature
  Law A := ∀ (X : Type) [Fintype X] [DecidableEq X]
    (D : LatticeData) (a : Charge D) (N : ℕ) (e : X → External D) (z : ℂ),
    A.readout () ⟨D, N, X⟩ (rightMean D a N e z)
      (fun i => damp D N z i * originalInverseMean D a N e i)
private theorem bad_fails : ¬ arena.Law meanBad := by
  intro h
  exact h Unit hyperbolic 0 0 labels 0
def evidence : Registration arena (type_of% (@rightMean_raw)) where
  actual := meanActual
  bridge := Iff.rfl
  variation := ⟨fun X _ _ D a N e z => rightMean_raw D a N e z, meanBad, bad_fails⟩
  sensitivity := meanSensitivity arena.Law bad_fails
  dependence := meanDependence
def audit : Contract.Registration
    (@rightMean_raw) (Realization meanSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.rightMean_raw.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.rightMean_raw.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize meanSignature meanActual.readout meanActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end rightMean_raw

namespace original_occupation_majorant_on_germ
def arena : Arena where
  signature := leSignature
  Law A := ∀ (X : Type) [Fintype X] [DecidableEq X]
    (D : LatticeData) (a : Charge D) (N : ℕ) (e : X → External D),
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ M : (Internal D N →₀ ℕ) → ℝ,
      Summable M ∧ ∀ p ∈ sourcePolydisk (X := X) r, ∀ d,
        A.readout () () ‖occupationTerm D a N e d p‖ (M d)
private theorem bad_fails : ¬ arena.Law leBad := by
  intro h
  obtain ⟨r, hr, hr1, M, hM, hb⟩ := h Unit hyperbolic 0 0 labels
  exact hb (0, 0, 0) ⟨by simpa using hr.le, by simp, by simp⟩ 0
def evidence : Registration arena (type_of% (@original_occupation_majorant_on_germ)) where
  actual := leActual
  bridge := Iff.rfl
  variation := ⟨fun X _ _ D a N e => original_occupation_majorant_on_germ D a N e, leBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law leActual leBad bad_fails
  dependence := leDependence
def audit : Contract.Registration
    (@original_occupation_majorant_on_germ) (Realization leSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_occupation_majorant_on_germ.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_occupation_majorant_on_germ.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize leSignature leActual.readout leActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_occupation_majorant_on_germ

namespace original_occupation_normal_on_germ
def arena : Arena where
  signature := sewingSignature
  Law A := ∀ (X : Type) [Fintype X] [DecidableEq X]
    (D : LatticeData) (a : Charge D) (N : ℕ) (e : X → External D),
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      A.readout () (.inl ⟨D, N, X⟩)
        (fun s : Finset (Internal D N →₀ ℕ) => fun p => ∑ d ∈ s, occupationTerm D a N e d p)
        (fun p => ∑' d, occupationTerm D a N e d p) (sourcePolydisk (X := X) r)
private theorem bad_fails : ¬ arena.Law sewingBad := by
  intro h
  obtain ⟨r, hr, hr1, hb⟩ := h Unit hyperbolic 0 0 labels
  exact hb
def evidence : Registration arena (type_of% (@original_occupation_normal_on_germ)) where
  actual := sewingActual
  bridge := Iff.rfl
  variation := ⟨fun X _ _ D a N e => original_occupation_normal_on_germ D a N e, sewingBad, bad_fails⟩
  sensitivity := sewingSensitivity arena.Law bad_fails
  dependence := sewingDependence
def audit : Contract.Registration
    (@original_occupation_normal_on_germ) (Realization sewingSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_occupation_normal_on_germ.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_occupation_normal_on_germ.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sewingSignature sewingActual.readout sewingActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_occupation_normal_on_germ

namespace original_occupation_sewing_on_germ
def arena : Arena where
  signature := sewingSignature
  Law A := ∀ (X : Type) [Fintype X] [DecidableEq X]
    (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) (N : ℕ) (e : X → External D),
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      A.readout () (.inl ⟨D, N, X⟩)
        (fun s : Finset (Internal D N →₀ ℕ) => fun p => ∑ d ∈ s, occupationTerm D a N e d p)
        (fun p => ∑' d, occupationTerm D a N e d p) (sourcePolydisk (X := X) r) ∧
      ∀ p ∈ sourcePolydisk (X := X) r,
        A.readout () (.inr ()) (∑' d, occupationTerm D a N e d p)
          (Complex.exp (-(D.rank : ℂ) / 2 * finiteLog N p.1) *
            Complex.exp (finiteMixedExponent D a N e p))
private theorem bad_fails : ¬ arena.Law sewingBad := by
  intro h
  obtain ⟨r, hr, hr1, hb, he⟩ := h Unit hyperbolic hyperbolic_unit 0 0 labels
  exact hb
def evidence : Registration arena (type_of% (@original_occupation_sewing_on_germ)) where
  actual := sewingActual
  bridge := Iff.rfl
  variation := ⟨fun X _ _ D hu a N e => original_occupation_sewing_on_germ D hu a N e, sewingBad, bad_fails⟩
  sensitivity := sewingSensitivity arena.Law bad_fails
  dependence := sewingDependence
def audit : Contract.Registration
    (@original_occupation_sewing_on_germ) (Realization sewingSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_occupation_sewing_on_germ.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_occupation_sewing_on_germ.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sewingSignature sewingActual.readout sewingActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_occupation_sewing_on_germ


namespace original_rows_symm
def arena : Arena where
  signature := eqSignature
  Law A := ∀ (X : Type) [Fintype X] [DecidableEq X] (D : LatticeData) (N : ℕ) (e : X → External D) (z : ℂ),
    (∀ i j, A.readout () () (leftRow D N e z i j) (leftRow D N e z j i)) ∧
    ∀ i j, A.readout () () (rightRow D N e z i j) (rightRow D N e z j i)
private theorem bad_fails : ¬ arena.Law eqBad := by
  intro h
  exact (h Unit hyperbolic 0 labels 0).1 (.inr ()) (.inr ())
def evidence : Registration arena (type_of% (@original_rows_symm)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun X _ _ D N e z => original_rows_symm D N e z, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_rows_symm) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_rows_symm.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm.original_rows_symm.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_rows_symm

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm
