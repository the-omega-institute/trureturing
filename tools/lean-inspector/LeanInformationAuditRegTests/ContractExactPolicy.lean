import LeanInformationAuditRegTests.ContractAssertions
import LeanInformationAudit.Contract.Decoder
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace LeanInformationAuditRegTests.ContractExactPolicy
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

universe u

theorem universeTarget (A : Type u) : A = A := rfl

def storedSignature : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature where
  Params := Seal.{0,0}
  State := fun _ => Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Unit
  Anchor := Unit
  finiteAnchor := inferInstance

def storedResult : storedSignature.Params := { rootId := `Stored, catalogs := #[], options := #[] }
def signatureAlias := storedSignature
def wrappedResult : Option storedSignature.Params := some storedResult

run_meta do
  let env := (← getEnv).setExporting false
  for (label, levels, accepted) in #[
      ("ValidTargetLevels", [Level.zero], true),
      ("MissingTargetLevels", [], false),
      ("ExtraTargetLevels", [Level.zero, Level.zero], false)] do
    let mut error := "accepted"
    try discard <| Decoder.liftLiteral <| Decoder.checkTarget (env.find? ·) ``universeTarget (.const ``universeTarget levels)
    catch ex => error := ← ex.toMessageData.toString
    assertTest s!"policy.target.{label}"
      (if accepted then error == "accepted"
       else error.startsWith "unclassified_form:contract.target_statement:")



run_elab do
  for (label, typeSyntax, valueSyntax, expected) in #[
      ("literal_identity", ← `(term| ExactMatch True True),
        ← `(term| ExactMatch.evidence), true),
      ("proved_proposition_is_not_identity", ← `(term| ExactMatch True (1 + 1 = 2)),
        ← `(term| ExactMatch.evidence), false),
      ("unknown_nonidentity", ← `(term| ExactMatch True (1 + 1 = 2)),
        ← `(term| ExactMatch.unknown), true),
      ("absent_nonidentity", ← `(term| ExactMatch True (1 + 1 = 2)),
        ← `(term| ExactMatch.absent), true),
      ("unsupported_nonidentity", ← `(term| ExactMatch True (1 + 1 = 2)),
        ← `(term| ExactMatch.unsupported `Nat.add_comm), true)] do
    let type ← Lean.Elab.Term.elabTerm typeSyntax none
    let accepted ← try
      let value ← Lean.Elab.Term.elabTerm valueSyntax (some type)
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      checkWithKernel value
      pure true
    catch _ => pure false
    assertTest s!"policy.exact_correspondence.{label}" (accepted == expected)

end LeanInformationAuditRegTests.ContractExactPolicy
