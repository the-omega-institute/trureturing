import LeanInformationAudit.Syntax
import D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open Lean Meta LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace LeanInformationAuditRegTests.LexicalSourceContract

private def mustReject (rule : String) (action : MetaM Unit) : MetaM Unit := do
  let result ← try action; pure "accepted" catch e => e.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"
  logInfo m!"[PASS] lexical rejects {rule}"

def gaussianSignature : Signature where
  Params := Σ Ω : Type, Σ _ : ℕ → ℕ → Ω → ℝ, Σ _ : ℕ → ℕ → ℝ, Σ _ : ℕ, ℕ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def gaussianActual : Realization gaussianSignature :=
  realize gaussianSignature (fun _ p ω =>
    p.2.2.1 p.2.2.2.1 p.2.2.2.2 * ((p.2.1 p.2.2.2.1 p.2.2.2.2 ω)^2 - 1))
    (fun e => nomatch e)

theorem siblingScope : (∀ n x : ℕ, n + x = n + x) ∧ (∀ n x : ℕ, n + x = n + x) := by
  constructor <;> intros <;> rfl

theorem lexicalLet (n : ℕ) : let k := n + 1; ∀ x : Fin k, x.val < k := by
  intro k x
  exact x.isLt

private partial def changedLet : Expr → Expr
  | .forallE n d b bi => .forallE n d (changedLet b) bi
  | .letE n d v b nd => .letE n d (mkApp (mkConst ``Nat.succ) v) b nd
  | e => e

private partial def changedMode : Expr → Expr
  | .forallE n d b bi => .forallE n d (changedMode b) bi
  | .letE n d v (.forallE n' d' b' _) nd =>
    .letE n d v (.forallE n' d' b' .implicit) nd
  | e => e

run_meta do
  let info ← getConstInfo ``D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.result
  let source ← IO.FS.readBinFile ((← Repository.root) /
    "D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticLimit.lean")
  unless Sha256.hex source == "82443192d04cd30c222f5f914436c735e92f59c190461f508ceeec999d545e70" do
    throwError "Gaussian original source changed"
  let path := (Array.replicate 12 "body") ++ #["fn", "arg", "body", "body", "fn", "fn", "arg", "body"]
  let selection : SourceSelection := {
    owner := `D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit
    coordinates := #[0,4,5,12,13], readouts := #[{ path, stateBinder := 14 }] }
  mustReject "source.coordinate_dependency" do
    discard <| (SourceScope.resolve info { selection with coordinates := #[0,4,5] }).run 524288
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  unless scope.telescope.size == 12 && (scope.readouts[0]?.map (·.context.size)).getD 0 == 15 &&
      scope.coordinates.size == 5 do throwError "Gaussian lexical/outer scope conflated"
  discard <| (SourceScope.validateFields scope (mkConst ``gaussianSignature)
    (mkConst ``gaussianActual)).run 524288
  logInfo "[PASS] Gaussian original nested n,j extraction and actual fields; full registration remains open"
  for coords in #[#[0,1,4,5,12,13], #[0,4,5,7,12,13]] do
    mustReject "source.dictionary_or_proof_coordinate" do
      discard <| (SourceScope.resolve info { selection with coordinates := coords }).run 524288
  let sibling ← getConstInfo ``siblingScope
  mustReject "source.captured_coordinate" do
    discard <| (SourceScope.resolve sibling {
      owner := `LeanInformationAuditRegTests.LexicalSourceContract, coordinates := #[0]
      readouts := #[
        { path := #["fn", "arg", "body", "body", "fn", "arg"], stateBinder := 1 },
        { path := #["arg", "body", "body", "fn", "arg"], stateBinder := 1 }] }).run 524288
  let localLet ← getConstInfo ``lexicalLet
  let letSelection : SourceSelection := {
    owner := `LeanInformationAuditRegTests.LexicalSourceContract, coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg"], stateBinder := 2 }] }
  discard <| (SourceScope.resolve localLet letSelection).run 524288
  mustReject "source.let_coordinate" do
    discard <| (SourceScope.resolve localLet { letSelection with coordinates := #[0,1] }).run 524288
  mustReject "source.let_reconstruction" do
    discard <| (SourceScope.reconstruct localLet.type (changedLet localLet.type)).run 524288
  mustReject "source.telescope_reconstruction" do
    discard <| (SourceScope.reconstruct localLet.type (changedMode localLet.type)).run 524288
  -- A source let used beneath an internal lambda must not capture that lambda's binder.
  let context : Array SourceBinder := #[
    { name := `n, info := .default, domain := mkConst ``Nat },
    { name := `k, info := .default, domain := mkConst ``Nat, value := some (.bvar 0) }]
  let term := Expr.lam `x (mkConst ``Nat) (.app (.app (mkConst ``Nat.add) (.bvar 1)) (.bvar 0)) .default
  let (projected, _) ← (SourceScope.transport context #[0] term).run 524288
  unless projected == Expr.lam `x (mkConst ``Nat)
      (.app (.app (mkConst ``Nat.add) (.bvar 1)) (.bvar 0)) .default do
    throwError "let inverse transport captured lambda binder"
  logInfo "[PASS] source-let inverse transport preserves internal binders"

end LeanInformationAuditRegTests.LexicalSourceContract
