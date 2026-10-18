/-
UNCOMPILED transient audit draft. Not a mathematical deliverable or acceptance.

After the current original flight is terminal and strictly collected, first
compile this small check through canonical make lean with an explicit target.
The main 4.35 cache window is complete; do not restore retired fixed11.
Only then wrap the entire unchanged anonymous root proof with the tactic.
Do not import a fictitious named theorem for that anonymous example.

The proof capture follows Lean.Elab.Tactic.ShowTerm.evalShowTerm's public
getMainGoal / evalTactic / instantiateMVars route. The audit collects axioms
from the actual closed proof and its original type, not just named helpers.
No declaration retaining the root proof is introduced.
-/
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

namespace OriginalRootAxiomAuditDraft

syntax (name := auditOriginalRoot) "audit_original_root " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| audit_original_root $body:tacticSeq) => withMainContext do
    let goal ← getMainGoal
    unless (← getUnsolvedGoals).length == 1 do
      throwError "Root audit must start with exactly one complete goal"
    let originalType ← goal.getType
    evalTactic body
    Term.synthesizeSyntheticMVarsNoPostponing
    unless (← getUnsolvedGoals).isEmpty do
      throwError "Root audit requires the complete proof to close every goal"
    let proof ← instantiateMVars (mkMVar goal)
    let type ← instantiateMVars originalType
    if proof.hasMVar || proof.hasFVar || type.hasMVar || type.hasFVar then
      throwError "Root audit requires a closed proof and type without metavariables"
    let mut axioms : Array Name := #[]
    for constant in proof.getUsedConstants ++ type.getUsedConstants do
      for axiomName in (← Lean.collectAxioms constant) do
        unless axioms.contains axiomName do
          axioms := axioms.push axiomName
    let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
    let unexpected := axioms.filter fun name => !allowed.contains name
    unless unexpected.isEmpty do
      throwError "Root proof uses nonstandard axioms: {unexpected}"
    logInfo m!"ORIGINAL_ROOT_AXIOMS {axioms.qsort Name.quickLt}"

-- Transient elaborator checks only; they do not establish the original root.
example : True := by
  audit_original_root
    exact True.intro

example : ∀ p q : Prop, (p ↔ q) → p = q := by
  audit_original_root
    intro p q hpq
    exact propext hpq

end OriginalRootAxiomAuditDraft
