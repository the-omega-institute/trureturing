import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.FreeGroup.PrimeQuotientSeparation
import Reg.Support.UniverseSingleReadout

/-! Source-bound separation observations for arbitrary alphabets and primes. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open FreeGroupPrimeQuotientSeparation

noncomputable section
universe u

namespace Reg.D5.S3.FiniteGroups.FreeGroup.PrimeQuotientSeparation

/-- Data coordinates; prime and nonidentity proofs remain in the full source law. -/
abbrev SourceParams : Type (u + 1) := Σ X : Type u, Σ _p : ℕ, FreeGroup X

abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature
  SourceParams.{u} (fun P => Subgroup (FreeGroup P.1)) (fun _ => Bool)

def actual : Realization signature.{u} := realize signature
  (fun _ P N => by classical exact decide (P.2.2 ∉ N)) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {X : Type u} {p : ℕ} [hp : Fact p.Prime] {w : FreeGroup X} (hw : w ≠ 1),
    ∃ (N : Subgroup (FreeGroup X)) (_ : N.Normal),
      N.FiniteIndex ∧ IsPGroup p (FreeGroup X ⧸ N) ∧ r.readout () ⟨X, p, w⟩ N = true

private theorem bridge :
    (type_of% (@exists_normal_is_p_group_quotient_not_mem.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h X p hp w hw
    obtain ⟨N, hN, hfinite, hgroup, hout⟩ := h hw
    exact ⟨N, hN, hfinite, hgroup, by simpa [actual, realize] using hout⟩
  · intro h X p hp w hw
    obtain ⟨N, hN, hfinite, hgroup, hout⟩ := h hw
    exact ⟨N, hN, hfinite, hgroup, by simpa [actual, realize] using hout⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨N, hN, hfinite, hgroup, hf⟩ :=
    h (X := ULift.{u} PUnit) (p := 2)
      (w := FreeGroup.of (ULift.up PUnit.unit)) (FreeGroup.of_ne_one _)
  simpa [rejected, realize] using hf

private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  let x : ULift.{u} PUnit := ⟨PUnit.unit⟩
  let P : SourceParams.{u} := ⟨ULift.{u} PUnit, 2, FreeGroup.of x⟩
  refine ⟨P, ⊥, ⊤, ?_⟩
  change decide ((FreeGroup.of x : FreeGroup (ULift.{u} PUnit)) ∉
      (⊥ : Subgroup (FreeGroup (ULift.{u} PUnit)))) ≠
    decide ((FreeGroup.of x : FreeGroup (ULift.{u} PUnit)) ∉
      (⊤ : Subgroup (FreeGroup (ULift.{u} PUnit))))
  simp [FreeGroup.of_ne_one]

def family : Registration arena.{u}
    (type_of% (@exists_normal_is_p_group_quotient_not_mem.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @exists_normal_is_p_group_quotient_not_mem.{u},
    rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_normal_is_p_group_quotient_not_mem.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `FreeGroupPrimeQuotientSeparation.exists_normal_is_p_group_quotient_not_mem.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.FreeGroup.PrimeQuotientSeparation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.FreeGroup.PrimeQuotientSeparation
    definition := none
    coordinates := #[0,1,3]
    readouts := #[{
      path := #["body","body","body","body","body","arg","body","arg","body","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg","fn","arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.FiniteGroups.FreeGroup.PrimeQuotientSeparation
