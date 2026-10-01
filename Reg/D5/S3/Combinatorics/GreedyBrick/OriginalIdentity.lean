import D5.S3.Combinatorics.GreedyBrick.OriginalIdentity
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity
open _root_.D5.S3.ArithSums.GreedyBrickCapacityTotality

namespace Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ m : ℕ, 1 ≤ m →
    r.readout () () (a m) = a m * (a m + 3) / 2 - m

theorem first_birth : a 1 = 1 := by
  have spec := Nat.find_spec (birth_totality 1 (by omega))
  have ha : 0 < a 1 ∧ a 1 ≤ 1 := by
    simpa only [a, dif_pos (by omega : 1 ≤ 1), birth, ↓reduceIte] using
      (show 0 < birth 1 (by omega) ∧ birth 1 (by omega) ≤ 1 from ⟨spec.1, spec.2.2.2⟩)
  omega

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx := h 1 (by omega)
  change 0 = a 1 * (a 1 + 3) / 2 - 1 at hx
  rw [first_birth] at hx
  norm_num at hx

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), 1, 2, ?_⟩
  change a 1 ≠ a 2
  intro h
  have spec := Nat.find_spec (birth_totality 2 (by omega))
  have hx : (trajectory (a 2)).length = 2 := by
    simpa only [a, dif_pos (by omega : 1 ≤ 2), birth] using spec.2.1
  rw [← h, first_birth] at hx
  norm_num [trajectory, step, transfer] at hx

noncomputable def registration : Registration arena
    (∀ m : ℕ, 1 ≤ m → a (a m) = a m * (a m + 3) / 2 - m) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.result in arena
  readout via (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Combinatorics.GreedyBrick.OriginalIdentity
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn"]
      functionOperand := true }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity
