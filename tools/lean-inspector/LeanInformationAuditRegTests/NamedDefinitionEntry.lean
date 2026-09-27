import LeanInformationAudit.Syntax

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.NamedDefinitionEntry

-- Same body, distinct identity: entry must not choose an interchangeable definition.
def claim : Prop := ∀ n : Nat, n = n
def otherClaim : Prop := ∀ n : Nat, n = n
unsafe def unsafeClaim : Prop := ∀ n : Nat, n = n
opaque opaqueClaim : Prop := ∀ n : Nat, n = n
@[extern "named_claim_test"] def externalClaim : Prop := ∀ n : Nat, n = n
@[implemented_by unsafeClaim] def implementedClaim : Prop := ∀ n : Nat, n = n
theorem target : claim := by intro n; rfl
theorem siblingTarget : claim ∧ claim := ⟨target, target⟩

def numberClaim : Nat := 1
def polyClaim.{u} : Prop := ∀ (_ : Type u) (n : Nat), n = n
def universeClaim.{u,v} : Prop := ∀ (_ : Type u) (_ : Type v) (n : Nat), n = n
theorem universeTarget.{u,v} : universeClaim.{u,v} := by intro α β n; rfl
theorem permutedTarget.{u,v} : universeClaim.{v,u} := by intro α β n; rfl

def aliasClaim : Prop := claim
theorem aliasTarget : aliasClaim := by intro n; rfl

def letClaim : Prop := ∀ n : Nat, let k := n + 1; ∀ x : Fin k, x.val < k
theorem letTarget : letClaim := by intro n k x; exact x.isLt

def dictionaryClaim : Prop := ∀ (α : Type) [Inhabited α] (n : Nat),
  (default : α) = default ∧ n = n
theorem dictionaryTarget : dictionaryClaim := by intro α i n; exact ⟨rfl, rfl⟩

private partial def changedLet : Expr → Expr
  | .forallE n d b bi => .forallE n d (changedLet b) bi
  | .letE n d v b nd => .letE n d (mkApp (mkConst ``Nat.succ) v) b nd
  | e => e


def selection : SourceSelection where
  owner := `LeanInformationAuditRegTests.NamedDefinitionEntry
  definition := some {
    owner := `LeanInformationAuditRegTests.NamedDefinitionEntry
    name := `LeanInformationAuditRegTests.NamedDefinitionEntry.claim }
  coordinates := #[]
  readouts := #[{ path := #["body", "arg"], stateBinder := 0 }]

private def mustReject (rule : String) (action : MetaM Unit) : MetaM Unit := do
  let result ← try action; pure "accepted" catch e => e.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"
  logInfo m!"[PASS] named definition rejects {rule}"

run_meta do
  let info ← getConstInfo ``target
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  unless scope.source.equal info.type && scope.telescope.isEmpty &&
      scope.definition.any (·.name == ``claim) && (scope.readouts[0]?.map (·.context.size)).getD 0 == 1 do
    throwError "named definition lost raw theorem identity or lexical context"
  mustReject "source.absent_occurrence" do
    discard <| (SourceScope.resolve info { selection with definition := none }).run 524288
  for (name, rule) in #[( ``otherClaim, "source.definition_reference"),
      (``target, "source.definition_kind"), (``opaqueClaim, "source.definition_kind"),
      (``externalClaim, "source.definition_safety"), (``implementedClaim, "source.definition_safety"),
      (``unsafeClaim, "source.definition_safety"),
      (``Nat.add, "source.definition_owner"),
      (``numberClaim, "source.definition_type"), (``polyClaim, "source.definition_universes")] do
    mustReject rule do
      discard <| (SourceScope.resolve info { selection with definition := some {
        owner := selection.owner, name := name } }).run 524288
  mustReject "source.definition_owner" do
    discard <| (SourceScope.resolve info { selection with definition := some {
      owner := `Wrong, name := ``claim } }).run 524288
  let siblingInfo ← getConstInfo ``siblingTarget
  for path in #[#["arg"], #["fn", "arg"]] do
    mustReject "source.definition_path" do
      discard <| (SourceScope.resolve siblingInfo { selection with definition := some {
        owner := selection.owner, name := ``claim, path } }).run 524288
  let some definition := scope.definition | throwError "entry missing"
  let body := definition.value
  mustReject "source.telescope_reconstruction" do
    let .forallE n d b _ := body | throwError "fixture binder missing"
    discard <| (SourceScope.reconstruct body (.forallE n d b .implicit)).run 524288
  mustReject "source.missing_binder" do
    discard <| (SourceScope.reconstruct body (mkConst ``False)).run 524288
  mustReject "source.absent_occurrence" do
    discard <| (SourceScope.resolve info { selection with
      readouts := #[{ path := #["normalize"], stateBinder := 0 }] }).run 524288
  let universeSelection : SourceSelection := {
    owner := selection.owner
    definition := some { owner := selection.owner, name := ``universeClaim }
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "arg"], stateBinder := 2 }] }
  discard <| (SourceScope.resolve (← getConstInfo ``universeTarget) universeSelection).run 524288
  mustReject "source.definition_reference" do
    discard <| (SourceScope.resolve (← getConstInfo ``permutedTarget) universeSelection).run 524288
  let aliasInfo ← getConstInfo ``aliasTarget
  mustReject "source.definition_reference" do
    discard <| (SourceScope.resolve aliasInfo selection).run 524288
  mustReject "source.absent_occurrence" do
    discard <| (SourceScope.resolve aliasInfo { selection with definition := some {
      owner := selection.owner, name := ``aliasClaim } }).run 524288
  let letInfo ← getConstInfo ``letTarget
  let letSelection : SourceSelection := {
    owner := selection.owner
    definition := some { owner := selection.owner, name := ``letClaim }
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg"], stateBinder := 2 }] }
  let (letScope, _) ← (SourceScope.resolve letInfo letSelection).run 524288
  let some letDefinition := letScope.definition | throwError "let entry absent"
  mustReject "source.let_coordinate" do
    discard <| (SourceScope.resolve letInfo { letSelection with coordinates := #[0,1] }).run 524288
  mustReject "source.let_reconstruction" do
    discard <| (SourceScope.reconstruct letDefinition.value
      (changedLet letDefinition.value)).run 524288
  let dictionaryInfo ← getConstInfo ``dictionaryTarget
  let dictionarySelection : SourceSelection := {
    owner := selection.owner
    definition := some { owner := selection.owner, name := ``dictionaryClaim }
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "arg", "arg"], stateBinder := 2 }] }
  let (dictionaryScope, _) ← (SourceScope.resolve dictionaryInfo dictionarySelection).run 524288
  mustReject "source.dictionary_or_proof_coordinate" do
    discard <| (SourceScope.resolve dictionaryInfo {
      dictionarySelection with coordinates := #[0,1] }).run 524288
  let some dictionaryDefinition := dictionaryScope.definition | throwError "dictionary entry absent"
  let .forallE n d (.forallE i id ib _) bi := dictionaryDefinition.value
    | throwError "dictionary binder absent"
  mustReject "source.telescope_reconstruction" do
    discard <| (SourceScope.reconstruct dictionaryDefinition.value
      (.forallE n d (.forallE i id ib .default) bi)).run 524288
  logInfo "[PASS] exact raw named claim entry retains lets and dictionaries"

end LeanInformationAuditRegTests.NamedDefinitionEntry
