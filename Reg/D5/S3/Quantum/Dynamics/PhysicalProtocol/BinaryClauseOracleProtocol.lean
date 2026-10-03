import D5.S3.Quantum.Dynamics.PhysicalProtocol.BinaryClauseOracleProtocol
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S3.Quantum.Dynamics.PhysicalProtocol.BinaryClauseOracleProtocol
open _root_.PredictiveThermodynamic _root_.PredictiveThermodynamic.BinaryNames
open _root_.PredictiveThermodynamic.Physical _root_.Lax51Proofs.RamToTM
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Turing StateTransition LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ w => Conventional.rawCount w) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 3) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ w : List Bool,
    let B := w.length^2+8*w.length+7
    ∃ r : List ResponseSymbol,
      queryReply (preparedQuery (denseOutput w)) r ∧
      r.length ≤ 2*(B+1)^2+B+5 ∧
      msbValue (totalPostOutput r) = R.readout () () w ∧
      (∃ t ≤ 80*(w.length+1)^2+20*B^2+72*B+87,
        BinaryProtocolRun (.prefix (initList queryCompiler w))
          (.physical (.halt (haltList postMachine (binaryWord (totalPostOutput r))))) t 1) ∧
      (∀ output t asks, BinaryProtocolRun (.prefix (initList queryCompiler w))
        (.physical (.halt output)) t asks → asks = 1)

def rejected_law : ¬ arena.Law rejected := by
  intro h
  let w := Conventional.comparisonSource
  obtain ⟨a,replyA,_,countA,_,_⟩ := conventional_one_query_run w
  obtain ⟨b,replyB,_,countB,_,_⟩ := h w
  obtain ⟨valueA,decodedA,physicalA⟩ := replyA
  obtain ⟨valueB,decodedB,physicalB⟩ := replyB
  have decoder := (dense_query_run w).2.1
  have sameA : valueA = densePrepared w := Option.some.inj (decodedA.symm.trans decoder)
  have sameB : valueB = densePrepared w := Option.some.inj (decodedB.symm.trans decoder)
  subst valueA
  subst valueB
  obtain ⟨_,_,unique,_,_,_,_⟩ := physical_reply_run (densePrepared w).2
  have same : a = b := (unique a physicalA).trans (unique b physicalB).symm
  have sourceCount : Conventional.rawCount w = 2 := by decide
  rw [sourceCount,same] at countA
  change msbValue (totalPostOutput b) = 3 at countB
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨conventional_one_query_run,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j different
      exact (different (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),Conventional.comparisonSource,[],?_⟩
    have decoded : Conventional.rawCount Conventional.comparisonSource = 2 := by decide
    change Conventional.rawCount Conventional.comparisonSource ≠ Conventional.rawCount []
    rw [decoded]
    decide

def selection : SourceSelection := {
  owner := `D5.S3.Quantum.Dynamics.PhysicalProtocol.BinaryClauseOracleProtocol
  coordinates := #[0]
  readouts := #[
    { path := #["body","body","arg","body","arg","arg","fn","arg","arg"]
      stateOperand := some #["arg"] }
  ] }

register_information_theorem _root_.PredictiveThermodynamic.BinaryNames.conventional_one_query_run in arena
  readout via (realize signature (fun _ _ w => Conventional.rawCount w) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end Reg.D5.S3.Quantum.Dynamics.PhysicalProtocol.BinaryClauseOracleProtocol
