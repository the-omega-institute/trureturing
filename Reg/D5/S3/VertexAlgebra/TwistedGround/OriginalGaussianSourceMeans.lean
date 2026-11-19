import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans
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
open OriginalGaussianSourceMeans

open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod
open LatticeHalfFockFiniteCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans
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

namespace source_pairings_explicit
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {z : ℂ} (hz : ‖z‖ < 1) (out : Bool) (p : ℕ),
    Summable (fun n : ℕ => ‖(-1 : ℂ) ^ (n + 1) * externalBinomial out p (n + 1) *
      z ^ (2 * (n + 1)) * shiftedCentralSeries (z ^ 2) (n + 1) / period (z ^ 2)‖) ∧
    Summable (fun n : ℕ => ‖(centralWeight (n + 1) : ℂ) * z ^ (2 * (n + 1)) *
      shiftedCentralSeries (z ^ 2) (n + 1) / ((n + 1 : ℂ) * period (z ^ 2))‖) ∧R.readout () _ (innerSL ℂ (star (externalVector out p z)) (columnSeries z)) (sourceExternal out p z) ∧
    innerSL ℂ (star (sourceFamily 0 z)) (columnSeries z) = sourceConstant z
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact (h (z := 0) (by simp) false 0).2.2.1
def family : Registration arena (type_of% (@source_pairings_explicit)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@source_pairings_explicit, eqRejected, rejected_fails⟩
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
    (@source_pairings_explicit) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans.source_pairings_explicit.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans.source_pairings_explicit.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end source_pairings_explicit

namespace original_opposite_charge_means_explicit
abbrev arena : Arena where
  signature := limitSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1),
    (∀ x : X,
      R.readout () () (fun N z => effectiveMean D a N e z (.inl x))
        (fun z => (bilinear D (unitCharge D (e x).2.1) a : ℂ) *
          (-1 + sourceExternal (e x).1 (e x).2.2 z)) {z : ℂ | ‖z‖ ≤ ρ} ∧
      R.readout () () (fun N z => effectiveMean D a N e z (.inr x))
        (fun z => (bilinear D (unitCharge D (e x).2.1) a : ℂ) *
          (1 - sourceExternal (e x).1 (e x).2.2 z)) {z : ℂ | ‖z‖ ≤ ρ}) ∧
    R.readout () () (fun N z => effectiveConstant D a N e z)
      (fun z => (LatticeHalfFockChargedTensorCoefficients.chargeNorm D a : ℂ) * sourceConstant z)
      {z : ℂ | ‖z‖ ≤ ρ}
private theorem rejected_fails : ¬ arena.Law limitRejected := by
  intro h
  exact (h hyperbolic hyperbolic_unit 0 (X := PUnit) labels (ρ := 0) le_rfl (by norm_num)).2
def family : Registration arena (type_of% (@original_opposite_charge_means_explicit)) where
  actual := limitActual
  bridge := Iff.rfl
  variation := ⟨@original_opposite_charge_means_explicit, limitRejected, rejected_fails⟩
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
    (@original_opposite_charge_means_explicit) (Realization limitSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans.original_opposite_charge_means_explicit.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans.original_opposite_charge_means_explicit.family
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
end original_opposite_charge_means_explicit

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans
