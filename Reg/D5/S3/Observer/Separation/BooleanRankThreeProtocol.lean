import D5.S3.Observer.Separation.BooleanRankThreeProtocol
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol

open _root_.D5.S3.Observer.Separation.BooleanRankThreeProtocol
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a => delta a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => false) (fun e => nomatch e)

/-- The complete negated necessity statement, with the decoder row as readout. -/
abbrev arena : Arena where
  signature := signature
  Law R := ¬ (TaskData →
    Protocol Ftheta 3 3 alpha beta (R.readout () ()) →
    ∃ c d, Balanced Ftheta c d)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro _ hp
  have bad := hp.2.2 1 0 true (by decide)
  change false = true at bad
  exact Bool.noConfusion bad

def registration : Registration arena (¬ claim) where
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
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have bad := congrFun h 0
    change false = true at bad
    exact Bool.noConfusion bad

register_information_theorem result in arena
  readout via (realize signature (fun _ _ a => delta a) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.Separation.BooleanRankThreeProtocol
    «definition» := some {
      owner := `D5.S3.Observer.Separation.BooleanRankThreeProtocol
      name := `D5.S3.Observer.Separation.BooleanRankThreeProtocol.claim
      path := #["arg"] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "domain", "arg"]
      stateBinder := 0
      functionOperand := true }] })
  escape continues (open)

#print axioms result
#print axioms registration

end Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol
