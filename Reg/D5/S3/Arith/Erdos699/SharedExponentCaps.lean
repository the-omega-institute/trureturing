import D5.S3.Arith.Erdos699.SharedExponentCaps
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Erdos699.SharedExponentCaps

open _root_.D5.S3.Arith.Erdos699.SharedExponentCaps
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ × Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law := fun r => ∀ N : ℕ, (r.readout () () N).2 = true

def actual : Realization signature :=
  realize signature
    (fun _ _ (N : ℕ) =>
      (N, decide (
        (N % 110 ≠ 0 ∨ N % 11 ≠ 1) ∧
        (N % 110 ≠ 22 ∨ N % 11 ≠ 4) ∧
        (N % 110 ≠ 1 ∨ N % 11 ≠ 0) ∧
        (N % 110 ≠ 23 ∨ N % 11 ≠ 3))))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ (N : ℕ) => (N, false)) (fun e => nomatch e)

theorem actual_law : arena.Law actual := by
  intro N
  simp [actual, realize, shared_lift_caps]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfalse := h 0
  simp [rejected, realize] at hfalse

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    intro h
    have hfirst := congrArg Prod.fst h
    norm_num [actual, realize] at hfirst

register_information_theorem shared_lift_caps in arena
  readout via (realize signature
    (fun _ _ (N : ℕ) =>
      (N, decide (
        (N % 110 ≠ 0 ∨ N % 11 ≠ 1) ∧
        (N % 110 ≠ 22 ∨ N % 11 ≠ 4) ∧
        (N % 110 ≠ 1 ∨ N % 11 ≠ 0) ∧
        (N % 110 ≠ 23 ∨ N % 11 ≠ 3))))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Erdos699.SharedExponentCaps
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "body", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms actual_law
#print axioms registration

end Reg.D5.S3.Arith.Erdos699.SharedExponentCaps
