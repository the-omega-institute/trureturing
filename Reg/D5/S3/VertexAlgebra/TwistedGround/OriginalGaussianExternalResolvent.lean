import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent
noncomputable section
open scoped BigOperators Topology ENNReal Matrix Matrix.Norms.L2Operator Kronecker
open Filter
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.TwistedGround
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open LatticeHalfFock
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianWeightedResolvent
open OriginalGaussianUniformCutoff
open OriginalGaussianDifferentiation OriginalGaussianAllIndexResolvent
open OriginalGaussianDisplacement
open OriginalGaussianExternalResolvent
open OriginalCorrectedRowRecompositionSource OriginalNormalRowSource

open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod
open LatticeHalfFockFiniteCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent
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

namespace externalColumn_l1
abbrev arena : Arena where
  signature := leSignature
  Law R := ∀ (out : Bool) (p : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {z : ℂ} (hz : ‖z‖ ≤ ρ),
    (∀ n, R.readout () () ‖externalColumn out p z n‖
      ((p + 1 : ℝ) ^ p * (n + 1 : ℝ) ^ (p + 1) * ρ ^ (n + 1))) ∧
      Summable (fun n : ℕ => ‖externalColumn out p z n‖)
private theorem rejected_fails : ¬ arena.Law leRejected := by
  intro h
  exact (h false 0 (ρ := 0) le_rfl (by norm_num) (z := 0) (by simp)).1 0
def family : Registration arena (type_of% (@externalColumn_l1)) where
  actual := leActual
  bridge := Iff.rfl
  variation := ⟨@externalColumn_l1, leRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨leRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := leDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@externalColumn_l1) (Realization leSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent.externalColumn_l1.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent.externalColumn_l1.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize leSignature leActual.readout leActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end externalColumn_l1

namespace externalVector_apply
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out : Bool) (p : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ),
    R.readout () _ (externalVector out p z n) (externalColumn out p z n) 
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h false 0 (z := 0) (by simp) 0
def family : Registration arena (type_of% (@externalVector_apply)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@externalVector_apply, eqRejected, rejected_fails⟩
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
    (@externalVector_apply) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent.externalVector_apply.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent.externalVector_apply.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end externalVector_apply

namespace external_contractions_explicit
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1),
    Summable (fun st : ℕ × ℕ => ‖externalColumn out p z st.1 *
      explicitOddEntry z (st.1 + 1) (st.2 + 1) * externalColumn out' q z st.2‖) ∧
    Summable (fun skt : (ℕ × ℕ) × ℕ => ‖externalColumn out p z skt.1.1 *
      matrixEntry z (skt.1.1 + 1) (skt.1.2 + 1) *
        explicitOddEntry z (skt.1.2 + 1) (skt.2 + 1) * externalColumn out' q z skt.2‖) ∧R.readout () _ (innerSL ℂ (star (externalVector out p z))
      (oddResolvent z (externalVector out' q z))) (externalJ out p out' q z) ∧
    innerSL ℂ (star (externalVector out p z))
      (squareResolvent z (externalVector out' q z)) = externalT out p out' q z ∧
    Summable (fun s : ℕ => ‖externalColumn out p z s * externalColumn out' q z s‖)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact (h false 0 false 0 (z := 0) (by simp)).2.2.1
def family : Registration arena (type_of% (@external_contractions_explicit)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@external_contractions_explicit, eqRejected, rejected_fails⟩
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
    (@external_contractions_explicit) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent.external_contractions_explicit.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent.external_contractions_explicit.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end external_contractions_explicit

namespace externalCutoff_control
abbrev arena : Arena where
  signature := leSignature
  Law R := ∀ {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (out : Bool) (p : ℕ),
    (∀ (z : ℂ), ‖z‖ ≤ ρ → R.readout () () ‖externalVector out p z‖ (externalMass p ρ) ∧
      ∀ N, ‖externalCutoff N out p z‖ ≤ externalMass p ρ) ∧
    TendstoUniformly
      (fun N => fun z : {z : ℂ | ‖z‖ ≤ ρ} => externalCutoff N out p z)
      (fun z : {z : ℂ | ‖z‖ ≤ ρ} => externalVector out p z) atTop
private theorem rejected_fails : ¬ arena.Law leRejected := by
  intro h
  exact ((h (ρ := 0) le_rfl (by norm_num) false 0).1 0 (by simp)).1
def family : Registration arena (type_of% (@externalCutoff_control)) where
  actual := leActual
  bridge := Iff.rfl
  variation := ⟨@externalCutoff_control, leRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨leRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := leDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@externalCutoff_control) (Realization leSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent.externalCutoff_control.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent.externalCutoff_control.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize leSignature leActual.readout leActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end externalCutoff_control

namespace actual_left_mixed
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (D : LatticeData) (z : ℂ)
    (i : Index D) (out : Bool) (j : Index D),
    R.readout () _ (z ^ (i.2 + 1) * correctedMatrix D (Function.Embedding.refl (Index D))
      (.inl i) (originalExternalIndex D (out, j))) ((Real.sqrt (i.2 + 1 : ℝ) : ℂ) * externalColumn out j.2 z i.2 *
        (D.G i.1 j.1 : ℂ)) 
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h hyperbolic 0 (0, 0) false (0, 0)
def family : Registration arena (type_of% (@actual_left_mixed)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@actual_left_mixed, eqRejected, rejected_fails⟩
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
    (@actual_left_mixed) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent.actual_left_mixed.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent.actual_left_mixed.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end actual_left_mixed

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent
