import Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators
noncomputable section
open scoped BigOperators Topology ENNReal
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianDifferentiation
open OriginalGaussianWeightedResolvent
open OriginalGaussianAllIndexResolvent OriginalGaussianExternalResolvent
open OriginalGaussianSourceMeans OriginalGaussianSourceEvaluation
open OriginalGaussianExternalFrequency OriginalGaussianExternalDisplacement
open OriginalGaussianExternalMoments OriginalGaussianExternalRadial
open OriginalGaussianExternalEvolution OriginalGaussianExternalSourceJet
open OriginalGaussianExternalNormal OriginalGaussianExternalGenerators
open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
open OriginalGaussianExternalNormal
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal
local notation:50 a:51 " ≋[" R "] " b:51 => Realization.readout R () _ a b
local notation:50 a:51 " ≼[" R "] " b:51 => Realization.readout R () () a b

abbrev summableSignature : Signature where
  Params := Type
  State T := T → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def summableActual : Realization summableSignature :=
  realize _ (fun _ _ f => Summable f) (fun e => nomatch e)
def summableRejected : Realization summableSignature :=
  realize _ (fun _ _ _ => False) (fun e => nomatch e)
def summableObserve {T : Type} (R : Realization summableSignature) (f : T → ℝ) : Prop :=
  R.readout () T f
private theorem summableDependence : ObservationalDependence summableSignature summableActual := by
  intro i
  refine ⟨ℕ, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hf : Summable (fun _ : ℕ => (1 : ℝ)) := Eq.mp h (summable_zero)
  have he : (1 : ℝ) = 0 := by simpa only [summable_const_iff] using hf
  exact one_ne_zero he

namespace external_binomial_joint_summable
abbrev arena : Arena where
  signature := summableSignature
  Law R := ∀ (out : Bool) (d : ℕ) {δ ρ : ℝ}
    (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hsmall : δ + ρ < 1),
    summableObserve R (fun ps : ℕ × ℕ => (ps.1 + ps.2 + 1 : ℝ) ^ d *
      δ ^ ps.1 * ρ ^ ps.2 * ‖externalBinomial out ps.1 ps.2‖)
private theorem rejected_fails : ¬ arena.Law summableRejected := by
  intro h
  exact h false 0 (δ := 0) (ρ := 0) (by norm_num) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@external_binomial_joint_summable)) where
  actual := summableActual
  bridge := Iff.rfl
  variation := ⟨@external_binomial_joint_summable, summableRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨summableRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := summableDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@external_binomial_joint_summable) (Realization summableSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal.external_binomial_joint_summable.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal.external_binomial_joint_summable.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end external_binomial_joint_summable


namespace externalColumn_joint_summable
abbrev arena : Arena where
  signature := summableSignature
  Law R := ∀ (out : Bool) {u z : ℂ}
    (hsmall : ‖u‖ + ‖z‖ < 1),
    summableObserve R (fun pn : ℕ × ℕ => ‖u‖ ^ pn.1 * ‖externalColumn out pn.1 z pn.2‖)
private theorem rejected_fails : ¬ arena.Law summableRejected := by
  intro h
  exact h false (u := 0) (z := 0) (by norm_num)
def family : Registration arena (type_of% (@externalColumn_joint_summable)) where
  actual := summableActual
  bridge := Iff.rfl
  variation := ⟨@externalColumn_joint_summable, summableRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨summableRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := summableDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@externalColumn_joint_summable) (Realization summableSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal.externalColumn_joint_summable.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal.externalColumn_joint_summable.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end externalColumn_joint_summable


namespace externalVector_mode_summable
abbrev arena : Arena where
  signature := summableSignature
  Law R := ∀ (out : Bool) {u z : ℂ}
    (hsmall : ‖u‖ + ‖z‖ < 1),
    summableObserve R (fun p : ℕ => ‖u ^ p • externalVector out p z‖)
private theorem rejected_fails : ¬ arena.Law summableRejected := by
  intro h
  exact h false (u := 0) (z := 0) (by norm_num)
def family : Registration arena (type_of% (@externalVector_mode_summable)) where
  actual := summableActual
  bridge := Iff.rfl
  variation := ⟨@externalVector_mode_summable, summableRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨summableRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := summableDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@externalVector_mode_summable) (Realization summableSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal.externalVector_mode_summable.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal.externalVector_mode_summable.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end externalVector_mode_summable


namespace external_kernel_mode_summable
abbrev arena : Arena where
  signature := summableSignature
  Law R := ∀ (out out' : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1),
    summableObserve R (fun pq : ℕ × ℕ => ‖u ^ pq.1 * v ^ pq.2 *
      externalJ out pq.1 out' pq.2 z‖) ∧
    Summable (fun pq : ℕ × ℕ => ‖u ^ pq.1 * v ^ pq.2 *
      externalT out pq.1 out' pq.2 z‖)
private theorem rejected_fails : ¬ arena.Law summableRejected := by
  intro h
  exact (h false false (u := 0) (v := 0) (z := 0) (by norm_num) (by norm_num)).1
def family : Registration arena (type_of% (@external_kernel_mode_summable)) where
  actual := summableActual
  bridge := Iff.rfl
  variation := ⟨@external_kernel_mode_summable, summableRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨summableRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := summableDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@external_kernel_mode_summable) (Realization summableSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal.external_kernel_mode_summable.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal.external_kernel_mode_summable.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end external_kernel_mode_summable


namespace sourceAmplitude_joint_summable
abbrev arena : Arena where
  signature := summableSignature
  Law R := ∀ (out : Bool) {u x : ℂ} (hsmall : ‖u‖ + ‖x‖ < 1),
    summableObserve R (fun pn : ℕ × ℕ => ‖(OriginalGaussianMatrix.centralWeight pn.2 : ℂ) *
      (-1 : ℂ) ^ pn.2 *
      Ring.choose ((if out then (pn.1 : ℂ) + 1 / 2 else -(pn.1 : ℂ) - 1 / 2) -
        1 / 2) pn.2 * x ^ pn.2 * u ^ pn.1‖)
private theorem rejected_fails : ¬ arena.Law summableRejected := by
  intro h
  exact h false (u := 0) (x := 0) (by norm_num)
def family : Registration arena (type_of% (@sourceAmplitude_joint_summable)) where
  actual := summableActual
  bridge := Iff.rfl
  variation := ⟨@sourceAmplitude_joint_summable, summableRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨summableRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := summableDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceAmplitude_joint_summable) (Realization summableSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal.sourceAmplitude_joint_summable.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal.sourceAmplitude_joint_summable.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sourceAmplitude_joint_summable

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal
