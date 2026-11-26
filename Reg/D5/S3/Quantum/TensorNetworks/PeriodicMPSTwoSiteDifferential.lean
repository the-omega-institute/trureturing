import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteDifferential

/-! Source-bound registration of the determinant nonzero predicate. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteDifferential

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteDifferential
open LeanInformationAudit

noncomputable section

private abbrev Entries := (Fin 2 × Fin 2) × (Fin 2 × Fin 2)

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ determinant target => determinant ≠ target) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : ℕ, ∃ (a : ℂ) (x : Fin 4 → ℂ) (rows : Fin 9 → Entries),
    R.readout () () ((augmented r a x).submatrix rows id).det 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, _, hdet⟩ := h 0
  exact hdet

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hz : (0 : ℂ) ≠ 0 := (congrFun h 0).mpr one_ne_zero
  exact hz rfl

def rankFamily : Registration arena (type_of% @projective_rank_eight) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@projective_rank_eight, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def rankAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@projective_rank_eight) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteDifferential.unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteDifferential.rankFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨rankFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ determinant target => determinant ≠ target)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteDifferential
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "body", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms rankAudit

end

end Reg.D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteDifferential
