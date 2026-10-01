import D5.S1.Recurrence.Invariants.CloitreActualRightProfile
import Reg.Support.DependentFamily

open _root_.D5.S1.Recurrence.Invariants.CloitreActualRightProfile
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ n => C n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => C n + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ N i : ℕ, 3 ≤ N → X N i ∈ D N) ∧
    (∀ N : ℕ, 3 ≤ N → R.readout () () N = C (g N) + C (N - g N))

theorem rejected_law : ¬ arena.Law rejected := by
  intro hr
  have he := hr.2 3 (by omega)
  have ha := actual_foundations.2 3 (by omega)
  change C 3 + 1 = C (g 3) + C (3 - g 3) at he
  omega

def registration : Registration arena
    ((∀ N i : ℕ, 3 ≤ N → X N i ∈ D N) ∧
      (∀ N : ℕ, 3 ≤ N → C N = C (g N) + C (N - g N))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_foundations, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact False.elim (hj (@Subsingleton.elim Unit _ j i))
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (1 : ℕ), (4 : ℕ), ?_⟩
    change C 1 ≠ C 4
    decide

register_information_theorem actual_foundations
  in arena
  readout via (realize signature (fun _ _ n => C n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Recurrence.Invariants.CloitreActualRightProfile
    coordinates := #[]
    readouts := #[{ path := #["arg", "body", "body", "fn", "arg"], stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile
