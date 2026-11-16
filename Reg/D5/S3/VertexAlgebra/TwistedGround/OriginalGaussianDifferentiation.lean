import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
noncomputable section
open scoped BigOperators Topology ENNReal Matrix Matrix.Norms.L2Operator Kronecker
open Filter
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.TwistedGround
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianWeightedResolvent
open OriginalGaussianDifferentiation

open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod
open LatticeHalfFockFiniteCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
abbrev eqSignature : Signature where
  Params := Type
  State T := T
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ T := T → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def eqActual : Realization eqSignature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def eqRejected : Realization eqSignature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem eqDependence : ObservationalDependence eqSignature eqActual := by
  intro i
  refine ⟨ℂ, 0, 1, ?_⟩
  intro h
  have he : (1 : ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero he
abbrev summableSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℝ) (fun _ => Prop)
def summableActual : Realization summableSignature :=
  realize _ (fun _ _ f => Summable f) (fun e => nomatch e)
def summableRejected : Realization summableSignature :=
  realize _ (fun _ _ _ => False) (fun e => nomatch e)
private theorem summableDependence : ObservationalDependence summableSignature summableActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hs : Summable (fun _ : ℕ => (0 : ℝ)) := summable_zero
  have ht : Summable (fun _ : ℕ => (1 : ℝ)) := Eq.mp h hs
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht.tendsto_atTop_zero)

namespace derivative_shifted_geometric
abbrev arena : Arena where
  signature := summableSignature
  Law A := ∀ {R : ℝ} (hR : 0 < R) (hR1 : R < 1) (j : ℕ),
    A.readout () () (fun n : ℕ => (n + 1 : ℝ) ^ j * R ^ n)
private theorem rejected_fails : ¬ arena.Law summableRejected := by
  intro h
  exact h (R := 1 / 2) (by norm_num) (by norm_num) 0
def family : Registration arena (type_of% (@derivative_shifted_geometric)) where
  actual := summableActual
  bridge := Iff.rfl
  variation := ⟨@derivative_shifted_geometric, summableRejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_fails
  dependence := summableDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@derivative_shifted_geometric) (Realization summableSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.derivative_shifted_geometric.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.derivative_shifted_geometric.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize summableSignature summableActual.readout summableActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end derivative_shifted_geometric

namespace sourceFamily_summable
abbrev arena : Arena where
  signature := summableSignature
  Law R := ∀ (j : ℕ) {z : ℂ} (hz : ‖z‖ < 1),
    R.readout () () (fun n : ℕ => ‖sourceFamilyTerm j z n‖)
private theorem rejected_fails : ¬ arena.Law summableRejected := by
  intro h
  exact h 0 (z := 0) (by simp)
def family : Registration arena (type_of% (@sourceFamily_summable)) where
  actual := summableActual
  bridge := Iff.rfl
  variation := ⟨@sourceFamily_summable, summableRejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_fails
  dependence := summableDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceFamily_summable) (Realization summableSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.sourceFamily_summable.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.sourceFamily_summable.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize summableSignature summableActual.readout summableActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sourceFamily_summable

namespace sourceFamily_apply
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (j : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ),
    R.readout () _ (sourceFamily j z n) ((n + 1 : ℂ) ^ j * halfBinomial (n + 1) * z ^ (n + 1) /
      (Real.sqrt (n + 1 : ℝ) : ℂ))
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h 0 (z := 0) (by simp) 0
def family : Registration arena (type_of% (@sourceFamily_apply)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@sourceFamily_apply, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceFamily_apply) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.sourceFamily_apply.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.sourceFamily_apply.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sourceFamily_apply

namespace sourceFamily_zero_eq_source
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1),
    R.readout () _ (sourceFamily 0 (Real.sqrt r : ℂ)) (source r hr hr1)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (r := 0) le_rfl (by norm_num)
def family : Registration arena (type_of% (@sourceFamily_zero_eq_source)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@sourceFamily_zero_eq_source, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceFamily_zero_eq_source) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.sourceFamily_zero_eq_source.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.sourceFamily_zero_eq_source.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sourceFamily_zero_eq_source

namespace radial_column_derivative_scaled
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    R.readout () _ ((r : ℂ) • radialColumnDerivative r)
      (((radialNormalization r : ℂ) / 2) •
        resolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1))
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (r := 1 / 2) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@radial_column_derivative_scaled)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@radial_column_derivative_scaled, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@radial_column_derivative_scaled) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.radial_column_derivative_scaled.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.radial_column_derivative_scaled.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end radial_column_derivative_scaled

namespace sourceFamily_one_eq_weightedSource
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1), R.readout () _ (sourceFamily 1 (Real.sqrt r : ℂ)) (weightedSource r hr hr1)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (r := 0) le_rfl (by norm_num)
def family : Registration arena (type_of% (@sourceFamily_one_eq_weightedSource)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@sourceFamily_one_eq_weightedSource, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceFamily_one_eq_weightedSource) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.sourceFamily_one_eq_weightedSource.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.sourceFamily_one_eq_weightedSource.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sourceFamily_one_eq_weightedSource

namespace sourceBilinearFunctional_apply
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (w x : H), R.readout () _ (sourceBilinearFunctional w x) (∑' n : ℕ, w n * x n)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (0 : H) (0 : H)
def family : Registration arena (type_of% (@sourceBilinearFunctional_apply)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@sourceBilinearFunctional_apply, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceBilinearFunctional_apply) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.sourceBilinearFunctional_apply.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.sourceBilinearFunctional_apply.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
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
end sourceBilinearFunctional_apply

namespace sourceBilinearFunctional_smul_left
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (a : ℂ) (w x : H), R.readout () _ (sourceBilinearFunctional (a • w) x) (a * sourceBilinearFunctional w x)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (0 : ℂ) (0 : H) (0 : H)
def family : Registration arena (type_of% (@sourceBilinearFunctional_smul_left)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@sourceBilinearFunctional_smul_left, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceBilinearFunctional_smul_left) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.sourceBilinearFunctional_smul_left.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.sourceBilinearFunctional_smul_left.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sourceBilinearFunctional_smul_left

namespace radial_pair_normalization
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {r : ℝ} (hr : 0 < r) (hr1 : r < 1), R.readout () _ (1 + sourceBilinearFunctional (radialSourceFamily 1 r) (radialColumn r)) (radialNormalization r : ℂ)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (r := 1 / 2) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@radial_pair_normalization)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@radial_pair_normalization, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@radial_pair_normalization) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.radial_pair_normalization.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.radial_pair_normalization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end radial_pair_normalization

abbrev vectorFunctionSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → H) (fun _ => ℝ → H)
def vectorFunctionActual : Realization vectorFunctionSignature :=
  realize _ (fun _ _ f => f) (fun e => nomatch e)
def vectorFunctionShifted : Realization vectorFunctionSignature :=
  realize _ (fun _ _ f u => f u + (u : ℂ) • basis 0) (fun e => nomatch e)
private theorem vectorFunctionDependence :
    ObservationalDependence vectorFunctionSignature vectorFunctionActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => basis 0), ?_⟩
  intro h
  have he : (0 : ℂ) = 1 := by
    simpa [vectorFunctionActual, realize, basis] using
      congrArg (fun f : ℝ → H => f 0 0) h
  exact zero_ne_one he

namespace hasDerivAt_radial_sourceFamily
abbrev arena : Arena where
  signature := vectorFunctionSignature
  Law R := ∀ (j : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    HasDerivAt (R.readout () () (radialSourceFamily j)) ((1 / (2 * (r : ℂ))) • radialSourceFamily (j + 1) r) r
private theorem rejected_fails : ¬ arena.Law vectorFunctionShifted := by
  intro h
  have hb := h 0 (r := 1 / 2) (by norm_num) (by norm_num)
  have ha := (hasDerivAt_radial_sourceFamily 0 (r := 1 / 2) (by norm_num) (by norm_num)).add
    ((hasDerivAt_id (1 / 2 : ℝ)).ofReal_comp.smul_const (basis 0))
  have he := hb.unique ha
  have he0 := congrArg (fun x : H => x 0) he
  simp only [Complex.ofReal_one, one_smul] at he0
  have he1 : (0 : ℂ) = 1 := by
    simp only [lp.coeFn_add, Pi.add_apply, basis, lp.single_apply, Pi.single_eq_same] at he0
    linear_combination he0
  exact zero_ne_one he1
def family : Registration arena (type_of% (@hasDerivAt_radial_sourceFamily)) where
  actual := vectorFunctionActual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_radial_sourceFamily, vectorFunctionShifted, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_fails
  dependence := vectorFunctionDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_radial_sourceFamily) (Realization vectorFunctionSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.hasDerivAt_radial_sourceFamily.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.hasDerivAt_radial_sourceFamily.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize vectorFunctionSignature vectorFunctionActual.readout vectorFunctionActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end hasDerivAt_radial_sourceFamily

namespace hasDerivAt_radial_column
abbrev arena : Arena where
  signature := vectorFunctionSignature
  Law R := ∀ {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    HasDerivAt (R.readout () () (radialColumn)) (radialColumnDerivative r) r
private theorem rejected_fails : ¬ arena.Law vectorFunctionShifted := by
  intro h
  have hb := h (r := 1 / 2) (by norm_num) (by norm_num)
  have ha := (hasDerivAt_radial_column (r := 1 / 2) (by norm_num) (by norm_num)).add
    ((hasDerivAt_id (1 / 2 : ℝ)).ofReal_comp.smul_const (basis 0))
  have he := hb.unique ha
  have he0 := congrArg (fun x : H => x 0) he
  simp only [Complex.ofReal_one, one_smul] at he0
  have he1 : (0 : ℂ) = 1 := by
    simp only [lp.coeFn_add, Pi.add_apply, basis, lp.single_apply, Pi.single_eq_same] at he0
    linear_combination he0
  exact zero_ne_one he1
def family : Registration arena (type_of% (@hasDerivAt_radial_column)) where
  actual := vectorFunctionActual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_radial_column, vectorFunctionShifted, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_fails
  dependence := vectorFunctionDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_radial_column) (Realization vectorFunctionSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.hasDerivAt_radial_column.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation.hasDerivAt_radial_column.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize vectorFunctionSignature vectorFunctionActual.readout vectorFunctionActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end hasDerivAt_radial_column

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
