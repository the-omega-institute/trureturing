-- Native generated-identity carrier; reuses the existing GoldenGap source audit.
import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Tower.GoldenGapZeckendorf
import Reg.Support.DependentFamily

open _root_.D5.S0.Conventions
open _root_.D5.S0.Tower.GoldenGapZeckendorf
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace LeanInformationAuditRegTests.NativeCapacity.Source

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

end
end LeanInformationAuditRegTests.NativeCapacity.Source
