import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks
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
open OriginalGaussianExternalBlocks
open _root_.D5.S3.VertexAlgebra.OriginalCurrentMetric

open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod
open LatticeHalfFockFiniteCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks
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

namespace original_source
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (D : LatticeData) (N : ℕ) {X : Type*}
    (e : X → External D) (z : ℂ),
    R.readout () _ ((leftRow D N e z).submatrix Sum.inl Sum.inl) ((gramComplex D) ⊗ₖ (frequencyRoot N * finiteSection N z * frequencyRoot N)) 
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h hyperbolic 0 (X := PUnit) labels 0
def family : Registration arena (type_of% (@original_source)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@original_source, eqRejected, rejected_fails⟩
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
    (@original_source) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.original_source.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.original_source.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks
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
end original_source

namespace original_inverse_source
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D) (z : ℂ),
    R.readout () _ ((rightRow D N e z).submatrix Sum.inl Sum.inl) ((gramComplex D)⁻¹ ⊗ₖ
        (inverseFrequencyRoot N * finiteSection N z * inverseFrequencyRoot N)) 
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h hyperbolic hyperbolic_unit 0 (X := PUnit) labels 0
def family : Registration arena (type_of% (@original_inverse_source)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@original_inverse_source, eqRejected, rejected_fails⟩
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
    (@original_inverse_source) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.original_inverse_source.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.original_inverse_source.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks
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
end original_inverse_source

namespace original_internal_inverse_similarities
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D)
    {z : ℂ} (hz : ‖z‖ < 1),
    let A := (leftRow D N e z).submatrix Sum.inl Sum.inl
    let B := (rightRow D N e z).submatrix Sum.inl Sum.inl
R.readout () _ (Ring.inverse (1 - B * A)) ((1 : Matrix (Fin D.rank) (Fin D.rank) ℂ) ⊗ₖ
        (inverseFrequencyRoot N * finiteSquare N z * frequencyRoot N)) ∧
    Ring.inverse (1 - A * B) =
      (1 : Matrix (Fin D.rank) (Fin D.rank) ℂ) ⊗ₖ
        (frequencyRoot N * finiteSquare N z * inverseFrequencyRoot N)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact (h hyperbolic hyperbolic_unit 0 (X := PUnit) labels (z := 0) (by simp)).1
def family : Registration arena (type_of% (@original_internal_inverse_similarities)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@original_internal_inverse_similarities, eqRejected, rejected_fails⟩
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
    (@original_internal_inverse_similarities) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.original_internal_inverse_similarities.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.original_internal_inverse_similarities.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks
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
end original_internal_inverse_similarities

namespace original_mixed
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (D : LatticeData) (N : ℕ) {X : Type*}
    (e : X → External D) (z : ℂ) (i : Internal D N) (x : X),
    R.readout () _ (leftRow D N e z (.inl i) (.inr x)) ((Real.sqrt (i.2.val + 1 : ℝ) : ℂ) *
        externalColumn (e x).1 (e x).2.2 z i.2.val * (gramComplex D) i.1 (e x).2.1) 
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h hyperbolic 1 (X := PUnit) labels 0 (0, 0) PUnit.unit
def family : Registration arena (type_of% (@original_mixed)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@original_mixed, eqRejected, rejected_fails⟩
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
    (@original_mixed) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.original_mixed.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.original_mixed.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks
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
end original_mixed

namespace original_inverse_mixed
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D) (z : ℂ)
    (i : Internal D N) (x : X),
    R.readout () _ (rightRow D N e z (.inl i) (.inr x)) (-(Real.sqrt (i.2.val + 1 : ℝ) : ℂ)⁻¹ *
        externalColumn (e x).1 (e x).2.2 z i.2.val *
          (if i.1 = (e x).2.1 then 1 else 0)) 
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h hyperbolic hyperbolic_unit 1 (X := PUnit) labels 0 (0, 0) PUnit.unit
def family : Registration arena (type_of% (@original_inverse_mixed)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@original_inverse_mixed, eqRejected, rejected_fails⟩
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
    (@original_inverse_mixed) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.original_inverse_mixed.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.original_inverse_mixed.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_inverse_mixed

namespace original_mixed_transpose
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (D : LatticeData) (N : ℕ) {X : Type*}
    (e : X → External D) (z : ℂ) (i : Internal D N) (x : X),
    R.readout () _ (leftRow D N e z (.inr x) (.inl i)) (leftRow D N e z (.inl i) (.inr x)) 
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h hyperbolic 1 (X := PUnit) labels 0 (0, 0) PUnit.unit
def family : Registration arena (type_of% (@original_mixed_transpose)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@original_mixed_transpose, eqRejected, rejected_fails⟩
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
    (@original_mixed_transpose) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.original_mixed_transpose.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.original_mixed_transpose.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks
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
end original_mixed_transpose

namespace cutoff_zeroExtend
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (N : ℕ) (out : Bool) (p : ℕ) (z : ℂ),
    R.readout () _ (zeroExtend N (WithLp.toLp 2 (fun s : Fin N => externalColumn out p z s.val))) (externalCutoff N out p z) 
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h 0 false 0 0
def family : Registration arena (type_of% (@cutoff_zeroExtend)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@cutoff_zeroExtend, eqRejected, rejected_fails⟩
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
    (@cutoff_zeroExtend) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.cutoff_zeroExtend.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.cutoff_zeroExtend.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks
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
end cutoff_zeroExtend

namespace external_pair_error
abbrev arena : Arena where
  signature := leSignature
  Law R := ∀ (u v x y : H) (A B : H →L[ℂ] H)
    {C : ℝ} (hC : 0 ≤ C) (hu : ‖u‖ ≤ C) (hy : ‖y‖ ≤ C)
    (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C),
    R.readout () () (‖innerSL ℂ (star v) (B y) - innerSL ℂ (star u) (A x)‖) (C ^ 2 * (‖v - u‖ + ‖B - A‖ + ‖y - x‖)) 
private theorem rejected_fails : ¬ arena.Law leRejected := by
  intro h
  exact h 0 0 0 0 0 0 (C := 0) le_rfl (by simp) (by simp) (by simp) (by simp)
def family : Registration arena (type_of% (@external_pair_error)) where
  actual := leActual
  bridge := Iff.rfl
  variation := ⟨@external_pair_error, leRejected, rejected_fails⟩
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
    (@external_pair_error) (Realization leSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.external_pair_error.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.external_pair_error.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end external_pair_error

namespace original_effectiveKernel_blocks_tendsto_explicit
abbrev arena : Arena where
  signature := limitSignature
  Law R := ∀ (D : LatticeData)
    (hu : IsUnit D.G.det) {X : Type*} [Fintype X] [DecidableEq X]
    (e : X → External D) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (a b : X ⊕ X),
    R.readout () () (fun N z => originalEffectiveKernel D N e z a b)
      (fun z => explicitEffectiveKernel D e z a b) {z : ℂ | ‖z‖ ≤ ρ}
private theorem rejected_fails : ¬ arena.Law limitRejected := by
  intro h
  exact h hyperbolic hyperbolic_unit (X := PUnit) labels (ρ := 0) le_rfl (by norm_num) (.inl PUnit.unit) (.inl PUnit.unit)
def family : Registration arena (type_of% (@original_effectiveKernel_blocks_tendsto_explicit)) where
  actual := limitActual
  bridge := Iff.rfl
  variation := ⟨@original_effectiveKernel_blocks_tendsto_explicit, limitRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨limitRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := limitDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_effectiveKernel_blocks_tendsto_explicit) (Realization limitSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.original_effectiveKernel_blocks_tendsto_explicit.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.original_effectiveKernel_blocks_tendsto_explicit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize limitSignature limitActual.readout limitActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_effectiveKernel_blocks_tendsto_explicit

namespace root_units
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ N : ℕ,
    R.readout () (Matrix (Fin N) (Fin N) ℂ)
      (frequencyRoot N * inverseFrequencyRoot N) (1 : Matrix (Fin N) (Fin N) ℂ) ∧
      R.readout () (Matrix (Fin N) (Fin N) ℂ)
        (inverseFrequencyRoot N * frequencyRoot N) (1 : Matrix (Fin N) (Fin N) ℂ)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact (h 0).1
def family : Registration arena (type_of% (@root_units)) where
  actual := eqActual
  bridge := by
    constructor
    · intro h N
      exact ⟨(h N).1, (h N).2⟩
    · intro h N
      exact ⟨(h N).1, (h N).2⟩
  variation := ⟨(by intro N; exact ⟨(root_units N).1, (root_units N).2⟩),
    eqRejected, rejected_fails⟩
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
    (@root_units) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.root_units.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks.root_units.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end root_units

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks
