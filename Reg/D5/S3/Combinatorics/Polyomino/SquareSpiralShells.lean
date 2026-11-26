import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Polyomino.SquareSpiralShells
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.Polyomino.SquareSpiralShells

open SpiralQueens
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ × ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ n => spiral n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0, 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 0 < n →
    ∃ k d : ℕ, n = (2*k+1)*(2*k+1)+d ∧ d < 8*(k+1) ∧
      R.readout () () n = shellPoint ((k : ℤ)+1) (d : ℤ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨k, d, hsum, _, hpoint⟩ := law (n := 1) (by decide)
  have hk : k = 0 := by
    by_contra hn
    have hb : 2*k+1 ≤ (2*k+1)*(2*k+1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  subst k
  have hd : d = 0 := by omega
  subst d
  exact (by decide : ((0, 0) : ℤ × ℤ) ≠ shellPoint 1 0) hpoint

def sourceRegistration : Registration arena (type_of% (@spiral_shells)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨spiral_shells, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    exact ⟨(), 0, 1, by decide⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@spiral_shells) (Realization signature) Unit Unit where
  unitName := `SpiralQueens.spiral_shells.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Polyomino.SquareSpiralShells.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => spiral n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Polyomino.SquareSpiralShells
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end

end Reg.D5.S3.Combinatorics.Polyomino.SquareSpiralShells
