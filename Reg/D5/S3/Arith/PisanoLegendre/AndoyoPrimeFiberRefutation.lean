import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.PisanoLegendre.AndoyoPrimeFiberRefutation
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the exact universal prime-fiber refutation. -/

namespace Reg.D5.S3.Arith.PisanoLegendre.AndoyoPrimeFiberRefutation

open _root_.D5.S3.Arith.PisanoLegendre.AndoyoPrimeFiberRefutation
open _root_.D5.S3.Arith.AndoyoPisanoSetCollision
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature := Reg.Support.SingleDependentReadout.signature
  (ℤ × ℤ) (fun _ => ℤ) (fun _ => Set ℕ)

def actual : Realization signature :=
  realize signature (fun _ ab k => fiber ab.1 ab.2 k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ¬ ∀ a b : ℤ, (a, b) ≠ (0, 0) →
    ∀ k : ℤ, k ∈ chi a b → (R.readout () (a, b) k).Infinite

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by intro a b hab k hk; exact Set.infinite_univ)

theorem dependence : ObservationalDependence signature actual := by
  intro role
  let k := K 3 Nat.prime_three 0 0
  refine ⟨(0, 0), k, k + 1, ?_⟩
  change fiber 0 0 k ≠ fiber 0 0 (k + 1)
  intro h
  have hm : 3 ∈ fiber 0 0 k := ⟨Nat.prime_three, by decide, rfl⟩
  rw [h] at hm
  obtain ⟨hp, hp2, he⟩ := hm
  have he' : k = k + 1 := he
  omega

def registration : Registration arena (Not claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.PisanoLegendre.AndoyoPrimeFiberRefutation.result) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PisanoLegendre.AndoyoPrimeFiberRefutation.result.audit
  realizationName := `Reg.D5.S3.Arith.PisanoLegendre.AndoyoPrimeFiberRefutation.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ab k => fiber ab.1 ab.2 k)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.Arith.PisanoLegendre.AndoyoPrimeFiberRefutation
    definition := some {
      owner := `D5.S3.Arith.PisanoLegendre.AndoyoPrimeFiberRefutation
      name := `D5.S3.Arith.PisanoLegendre.AndoyoPrimeFiberRefutation.claim
      path := #["arg"] }
    coordinates := #[]
    readouts := #[
      { path := #["arg", "body", "body", "body", "body", "body", "arg"]
        stateBinder := 3
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end
end Reg.D5.S3.Arith.PisanoLegendre.AndoyoPrimeFiberRefutation
