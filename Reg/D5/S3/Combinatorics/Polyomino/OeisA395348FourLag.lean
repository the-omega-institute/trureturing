import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Polyomino.OeisA395348FourLag
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.Polyomino.OeisA395348FourLag

open SpiralQueens
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ → ℕ) (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ moves n => moves n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∃! moves : ℕ → ℕ, SpiralGreedy moves) ∧
      ∀ moves : ℕ → ℕ, SpiralGreedy moves → ∀ n : ℕ, 2 ≤ n →
        R.readout () moves (2*(n+4)) = moves (2*n) + 8*n + 34

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨moves, hmoves, _⟩ := law.1
  have h := law.2 moves hmoves 2 (by decide)
  change (0 : ℕ) = moves (2*2) + 8*2 + 34 at h
  omega

def sourceRegistration : Registration arena (type_of% a395348_four_lag) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨a395348_four_lag, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    exact ⟨id, 0, 1, by decide⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      a395348_four_lag (Realization signature) Unit Unit where
  unitName := `SpiralQueens.a395348_four_lag.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Polyomino.OeisA395348FourLag.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ moves n => moves n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Polyomino.OeisA395348FourLag
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Polyomino.OeisA395348FourLag
