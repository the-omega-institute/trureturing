import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.GridSeedFreeness
import Reg.Support.SingleDependentReadout

/-! The freeness criterion observes the range of prime cycles. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.GridSeedFreeness

open _root_.D5.S3.ConceptDynamics.Attribution.GridSeedFreeness
open _root_.D5.S3.ConceptDynamics.Attribution.PermutationGridSupport (CalibratingLaw)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ k => k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k m : ℕ}, 0 < m →
    ((∀ (S : Type) [Fintype S] [MulAction (Equiv.Perm (Fin k)) S] (w : S → ℝ)
      (f : {a : Fin k → ℕ // ∑ i, a i = m} → S → Fin k), CalibratingLaw S w f →
      ∀ s : S, MulAction.stabilizer (Equiv.Perm (Fin k)) s = ⊥) ↔
      (∀ p : ℕ, p.Prime → p ≤ R.readout () () k → p ∣ m))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have free := (h (k := 2) (m := 1) (by decide)).mpr
    (fun p prime bound => False.elim (by have := prime.two_le; change p ≤ 0 at bound; omega))
  exact (by decide : ¬ 2 ∣ 1)
    ((every_calibrating_law_free_iff (k := 2) (m := 1) (by decide)).mp free 2
      (by decide) (by decide))

def family : Registration arena (type_of% (@every_calibrating_law_free_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨every_calibrating_law_free_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    exact ⟨(), 1, 2, (by decide : (1 : ℕ) ≠ 2)⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@every_calibrating_law_free_iff) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.GridSeedFreeness.prime_cycle_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.GridSeedFreeness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.GridSeedFreeness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "body", "domain", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.GridSeedFreeness
