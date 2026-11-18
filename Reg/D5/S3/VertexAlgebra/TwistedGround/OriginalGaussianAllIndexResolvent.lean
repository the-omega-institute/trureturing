import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent
noncomputable section
open scoped BigOperators Topology ENNReal Matrix Matrix.Norms.L2Operator Kronecker
open Filter
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.TwistedGround
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianWeightedResolvent
open OriginalGaussianUniformCutoff
open OriginalGaussianDifferentiation OriginalGaussianAllIndexResolvent
open OriginalGaussianDisplacement

open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod
open LatticeHalfFockFiniteCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent
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
abbrev leSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def leActual : Realization leSignature := realize _ (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def leRejected : Realization leSignature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem leDependence : ObservationalDependence leSignature leActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
  norm_num at he
abbrev limitSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℂ → ℂ)
    (fun _ => (ℂ → ℂ) → Set ℂ → Prop)
def limitActual : Realization limitSignature :=
  realize _ (fun _ _ F f s => TendstoUniformlyOn F f atTop s) (fun e => nomatch e)
def limitRejected : Realization limitSignature :=
  realize _ (fun _ _ _ _ _ => False) (fun e => nomatch e)
private theorem limitDependence : ObservationalDependence limitSignature limitActual := by
  intro i
  refine ⟨(), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro h
  have he := congrFun (congrFun h (fun _ => 0)) (Set.univ : Set ℂ)
  have hz : limitActual.readout () () (fun _ _ => 0) (fun _ => 0) Set.univ :=
    tendsto_const_nhds.tendstoUniformlyOn_const Set.univ
  have ho := Eq.mp he hz
  have hp := ho.tendsto_at (Set.mem_univ (0 : ℂ))
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hp)
private abbrev hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  even_diagonal := by intro i; fin_cases i <;> exact ⟨0, rfl⟩
private theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
  have h : hyperbolic.G.det = -1 := by
    change (Matrix.det (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ)) = -1
    norm_num [Matrix.det_fin_two]
  rw [h]
  exact isUnit_neg_one
private def labels : PUnit → Bool × Index hyperbolic := fun _ => (false, (0, 0))

namespace columnSeries_entry_explicit_complex
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ),
    R.readout () _ (columnSeries z n) ((-1 : ℂ) ^ (n + 1) * z ^ (n + 1) *
      shiftedCentralSeries (z ^ 2) (n + 1) /
        ((Real.sqrt (n + 1 : ℝ) : ℂ) * period (z ^ 2))) 
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (z := 0) (by simp) 0
def family : Registration arena (type_of% (@columnSeries_entry_explicit_complex)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@columnSeries_entry_explicit_complex, eqRejected, rejected_fails⟩
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
    (@columnSeries_entry_explicit_complex) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent.columnSeries_entry_explicit_complex.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent.columnSeries_entry_explicit_complex.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent
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
end columnSeries_entry_explicit_complex

namespace square_eq_one_add
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {z : ℂ} (hz : ‖z‖ < 1),
    R.readout () _ (squareResolvent z) (1 + operator z * oddResolvent z) 
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (z := 0) (by simp)
def family : Registration arena (type_of% (@square_eq_one_add)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@square_eq_one_add, eqRejected, rejected_fails⟩
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
    (@square_eq_one_add) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent.square_eq_one_add.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent.square_eq_one_add.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent
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
end square_eq_one_add

namespace oddResolvent_entry_explicit
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {z : ℂ} (hz : ‖z‖ < 1) (n m : ℕ),
    R.readout () _ (oddResolvent z (basis m) n) (explicitOddEntry z (n + 1) (m + 1)) 
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (z := 0) (by simp) 0 0
def family : Registration arena (type_of% (@oddResolvent_entry_explicit)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@oddResolvent_entry_explicit, eqRejected, rejected_fails⟩
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
    (@oddResolvent_entry_explicit) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent.oddResolvent_entry_explicit.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent.oddResolvent_entry_explicit.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent
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
end oddResolvent_entry_explicit

namespace squareResolvent_entry_explicit
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {z : ℂ} (hz : ‖z‖ < 1) (n m : ℕ),
    Summable (fun k : ℕ => ‖matrixEntry z (n + 1) (k + 1) *
      explicitOddEntry z (k + 1) (m + 1)‖) ∧R.readout () _ (squareResolvent z (basis m) n) ((if n = m then 1 else 0) +
      ∑' k : ℕ, matrixEntry z (n + 1) (k + 1) * explicitOddEntry z (k + 1) (m + 1)) 
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact (h (z := 0) (by simp) 0 0).2
def family : Registration arena (type_of% (@squareResolvent_entry_explicit)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@squareResolvent_entry_explicit, eqRejected, rejected_fails⟩
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
    (@squareResolvent_entry_explicit) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent.squareResolvent_entry_explicit.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent.squareResolvent_entry_explicit.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end squareResolvent_entry_explicit

namespace period_ofReal
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (r : ℝ), R.readout () _ (period (r : ℂ)) (F r : ℂ)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (0 : ℝ)
def family : Registration arena (type_of% (@period_ofReal)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@period_ofReal, eqRejected, rejected_fails⟩
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
    (@period_ofReal) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent.period_ofReal.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent.period_ofReal.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end period_ofReal

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent
