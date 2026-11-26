import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Lattices.KisielewiczFleetWinners
import Reg.Support.DependentFamily

/-! The period comparison observes the window side shifted by the proposed period. -/

open _root_.KisielewiczFleetWinners
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Lattices.KisielewiczFleetWinners

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ P c => c + P) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ c => c) (fun e => nomatch e)

/-- The readout is the shifted window side in the period-breaking comparison. -/
def arena : Arena where
  signature := signature
  Law R := ∃ F G : Set Origin,
    UniqueCover F ∧ UniqueCover G ∧ TrivialStabilizer F ∧ TrivialStabilizer G ∧
    (∀ B : ℕ, ∃ a b : ℕ, max 1 B ≤ a ∧ max 1 B ≤ b ∧
      outcome F G a = 1 ∧ outcome F G b = -1) ∧
    (∀ P : ℕ, 0 < P → ∀ B : ℕ, ∃ c : ℕ, max 1 B ≤ c ∧
      outcome F G (R.readout () P c) ≠ outcome F G c)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨F, G, _, _, _, _, _, h⟩
  obtain ⟨c, _, hc⟩ := h 1 (by decide) 0
  exact hc rfl

def evidence : Registration arena (type_of% exists_nonperiodic_fleets) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_nonperiodic_fleets, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      exact ⟨rejected, fun j hj => (hj (by cases j; rfl)).elim, rfl, rejected_law⟩
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), ?_⟩
    change (1 : ℕ) ≠ 2
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exists_nonperiodic_fleets (Realization signature) Unit Unit where
  unitName := Lean.Name.str (Lean.Name.str
    (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "KisielewiczFleetWinners")
      "exists_nonperiodic_fleets")
    "Reg.D5.S3.Arith.Lattices.KisielewiczFleetWinners/\
      Reg.D5.S3.Arith.Lattices.KisielewiczFleetWinners.arena/[anonymous]")
    "__information_unit"
  realizationName := `Reg.D5.S3.Arith.Lattices.KisielewiczFleetWinners.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ P c => c + P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.KisielewiczFleetWinners
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg",
        "body", "body", "body", "arg", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }]

end Reg.D5.S3.Arith.Lattices.KisielewiczFleetWinners
