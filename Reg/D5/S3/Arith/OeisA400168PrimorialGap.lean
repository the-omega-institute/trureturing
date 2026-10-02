import D5.S3.Arith.OeisA400168PrimorialGap
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.OeisA400168PrimorialGap
open _root_.D5.S3.Arith.OeisA400168PrimorialGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
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

def actual : Realization signature :=
  realize signature (fun _ _ n => L (D n)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete original negation and domain, varying only the derivative-length reading. -/
abbrev arena : Arena where
  signature := signature
  Law R := ¬ ∀ n : ℕ, 1 ≤ n → R.readout () () n ≤ M n + 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro n _
  exact Nat.zero_le _

theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 2, ?_⟩
  have hD0 : D 0 = 0 := by simp [D]
  have hD2 : D 2 = 1 := by simp [D, Nat.prime_two.factorization]
  have hL0 : L 0 = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact Nat.find_min' _ (by change 0 < P 0; decide)
  have hL1 : L 1 = 1 := by
    apply le_antisymm
    · exact Nat.find_min' _ (by change 1 < P 1; simp [P])
    · apply Nat.le_of_not_gt
      intro h
      have hz : L 1 = 0 := by omega
      have hspec : 1 < P (L 1) := by unfold L; exact Nat.find_spec (p := fun k => 1 < P k) _
      rw [hz] at hspec
      exact (by decide : ¬ (1 < P 0)) hspec
  change L (D 0) ≠ L (D 2)
  rw [hD0, hD2, hL0, hL1]
  decide

def registration : Registration arena (Not claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence

register_information_theorem
  _root_.D5.S3.Arith.OeisA400168PrimorialGap.result in arena
  readout via (realize signature (fun _ _ n => L (D n)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.OeisA400168PrimorialGap
    «definition» := some {
      owner := `D5.S3.Arith.OeisA400168PrimorialGap
      name := `D5.S3.Arith.OeisA400168PrimorialGap.claim
      path := #["arg"] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Arith.OeisA400168PrimorialGap
