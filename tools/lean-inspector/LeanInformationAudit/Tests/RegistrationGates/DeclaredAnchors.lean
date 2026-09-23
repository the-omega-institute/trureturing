import LeanInformationAudit.Tests.RegistrationGates.DeclaredBindings

namespace LeanInformationAudit.Tests.DeclaredAnchors
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape

def signature : PrimitiveSignature Bool where
  Index := Unit
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Bool
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def template (f anchor : Bool → Bool) : PrimitiveRealization signature :=
  ⟨fun _ => f, anchor⟩

register_information_template template

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := signature
  Law r := ∀ x : Bool, r.readout () x = x

instance : DecidableEq arena.State := instDecidableEqBool

information_theorem faithful in arena primitives (template (fun x => x) (fun b => b))
  : ∀ x : Bool, x = x := by intro x; rfl

def projectedAnchorDomain : PrimitiveRealization signature := ⟨fun _ x => x, fun b => b⟩
def identical : PrimitiveRealization signature := ⟨fun _ x => x, fun b : Bool => b⟩
def oneChanged : PrimitiveRealization signature := ⟨fun _ x => x, fun _ : Bool => false⟩
def bothChanged : PrimitiveRealization signature := ⟨fun _ x => x, Bool.not⟩

run_meta do
  let some event := (TemplateBinding.inventory (← getEnv)).find? (·.key.theoremName == ``faithful)
    | throwError "setup: missing native registration"
  let identity := Expr.lam .anonymous (mkConst ``Bool) (.bvar 0) .default
  let descriptor ← mkAppM ``template #[identity, identity]
  for (actual, label, shouldValidate) in #[
      (``identical, "matching_readout_and_anchors_accepted", true),
      (``oneChanged, "anchor_mismatch_rejected", false),
      (``bothChanged, "anchor_vector_mismatch_rejected", false),
      (``projectedAnchorDomain, "supplied_anchor_domain_rewrite_rejected", false)] do
    let record ← TemplateBinding.assess { event with realizationName := actual } (some {
      key := event.key, arena := event.arena, descriptor := some descriptor,
      owner := (← getEnv).header.mainModule })
    let (ok, result) := match record.result with
      | .declaredValidated _ => (shouldValidate, "validated")
      | .declaredUnresolved diagnostic =>
        (!shouldValidate && (diagnostic.splitOn
          "reason=unclassified_form rule=dtr.realization_mismatch site=").length == 2, diagnostic)
      | .undeclared => (false, "undeclared")
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"
    unless ok do logInfo m!"actual={result}"

end LeanInformationAudit.Tests.DeclaredAnchors
