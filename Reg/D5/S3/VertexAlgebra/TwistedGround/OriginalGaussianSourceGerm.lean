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
open OriginalGaussianMatrix OriginalGaussianSourceGerm NativeAffineTransport
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

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm
