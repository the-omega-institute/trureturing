module
public import OmegaChecks.InitPort.CertifiedFunction
public import OmegaChecks.InitPort.Translation
public import Init.Data.String.Lemmas.Pattern.TakeDrop.Basic

open Lean String.Slice.Pattern String.Slice.Pattern.Model
namespace OmegaChecks.InitPort.PatternMatch

@[expose] public noncomputable def forward {ρ : Type} (pat : ρ) [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : String.Slice} (p : s.Pos) := matchAt? pat p

@[expose] public def skip {ρ : Type} (pat : ρ) [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : String.Slice} (p : s.Pos) := p.skip? pat

public theorem forward_eq : @forward = @skip := by
  funext ρ pat model pattern law s p
  exact Pos.skip?_eq_matchAt?.symm

@[expose] public noncomputable def backward {ρ : Type} (pat : ρ) [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : String.Slice} (p : s.Pos) := revMatchAt? pat p

@[expose] public def revSkip {ρ : Type} (pat : ρ) [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : String.Slice} (p : s.Pos) := p.revSkip? pat

public theorem backward_eq : @backward = @revSkip := by
  funext ρ pat model pattern law s p
  exact Pos.revSkip?_eq_revMatchAt?.symm

public structure MatchRule where
  original : Name
  helper : Name
  reference : Name
  implementation : Name
  agreement : Name

public def owner := `Init.Data.String.Lemmas.Pattern.Basic

public def rules : List MatchRule := [
  ⟨``matchAt?, mkPrivateNameCore owner `String.Slice.Pos.matchWithForwardPattern,
    ``forward, ``skip, ``forward_eq⟩,
  ⟨``revMatchAt?, mkPrivateNameCore owner `String.Slice.Pos.matchWithBackwardPattern,
    ``backward, ``revSkip, ``backward_eq⟩]

/-- Only a lawful search operation for the exact pattern model can realize its longest match. -/
public def specialize? (rule : MatchRule) (sub : Expr) : MetaM (Option Expr) := do
  let #[ρ, pat, model, s, p] := sub.getAppArgs | return none
  try
    return some (← Meta.mkAppOptM rule.helper #[ρ, pat, model, none, none, s, p])
  catch _ => return none

public def addReferences (source templates : Environment) : IO Environment := do
  let mut env := source
  for rule in rules do
    unless source.contains rule.original do continue
    let some (.defnInfo ref) := templates.find? rule.reference | throw <| IO.userError s!"missing {rule.reference}"
    let decl := Declaration.defnDecl {ref with name := rule.helper, all := [rule.helper]}
    match env.addDeclCore 0 1000 decl none with
    | .ok out => env := out
    | .error e => throw <| IO.userError (← e.toMessageData {} |>.toString)
  return env

end OmegaChecks.InitPort.PatternMatch
