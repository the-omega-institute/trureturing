import D5.S0.Tower.GoldenGapZeckendorf
import Reg.Support.DependentFamily

open _root_.D5.S0.Conventions
open _root_.D5.S0.Tower.GoldenGapZeckendorf
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S0.Tower.GoldenGapZeckendorf

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State Q := Fin (Nat.fib (Q + 2))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ (Q : ℕ) (j : Fin (Nat.fib (Q + 2))) => wdigits (Nat.fib (Q + 3) + j.val))
    (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ Q : ℕ, ∀ j : Fin (Nat.fib (Q + 2)),
    R.readout () Q j = (Q + 3) :: wdigits j.val

theorem rejected_law : ¬ arena.Law rejected := by
  intro hr
  have hh := hr 0 ⟨0, by norm_num [Nat.fib]⟩
  change [] = 3 :: wdigits 0 at hh
  simp at hh

def registration : Registration arena
    (∀ Q : ℕ, ∀ j : Fin (Nat.fib (Q + 2)),
      wdigits (Nat.fib (Q + 3) + j.val) = (Q + 3) :: wdigits j.val) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨wdigits_fib_add, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(1 : ℕ), ⟨0, by norm_num [Nat.fib]⟩, ⟨1, by norm_num [Nat.fib]⟩, ?_⟩
    change wdigits 3 ≠ wdigits 4
    intro he
    have hd := congrArg (fun l : List ℕ => (l.map Nat.fib).sum) he
    rw [decode_wdigits, decode_wdigits] at hd
    omega

register_information_theorem wdigits_fib_add
  in arena
  readout via (realize signature
    (fun _ (Q : ℕ) (j : Fin (Nat.fib (Q + 2))) => wdigits (Nat.fib (Q + 3) + j.val))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S0.Tower.GoldenGapZeckendorf
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 1 }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S0.Tower.GoldenGapZeckendorf
