module
public import OmegaChecks.InitPort.CharacterSplit
public import OmegaChecks.InitPort.SingletonSelection
public import OmegaChecks.InitPort.SearcherSplit
public import OmegaChecks.InitPort.SemiringImage
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
  owner : Name
  original : Name
  helper : Name
  reference : Name
  implementation : Name
  agreement : Name

private def owner := `Init.Data.String.Lemmas.Pattern.Basic

private def predOwner := `Init.Data.String.Lemmas.Pattern.Split.Pred
private def splitOwner := `Init.Data.String.Lemmas.Pattern.Split.Basic
private def charOwner := `Init.Data.String.Lemmas.Pattern.Split.Char

private def ringOwner := `Init.Grind.Ring.CommSemiringAdapter

public def rules : List MatchRule := [
  ⟨`Init.Classical, ``Classical.epsilon, mkPrivateNameCore `Init.Classical `Classical.selectSingleton,
    ``SingletonSelection.epsilon, ``SingletonSelection.witness, ``SingletonSelection.epsilonAgreement⟩,
  ⟨`Init.Data.Erased, ``Erased.out, mkPrivateNameCore `Init.Data.Erased `Erased.outOfMk,
    ``SingletonSelection.erased, ``SingletonSelection.witness, ``SingletonSelection.erasedAgreement⟩,
  ⟨owner, ``matchAt?, mkPrivateNameCore owner `String.Slice.Pos.matchWithForwardPattern,
    ``forward, ``skip, ``forward_eq⟩,
  ⟨owner, ``revMatchAt?, mkPrivateNameCore owner `String.Slice.Pos.matchWithBackwardPattern,
    ``backward, ``revSkip, ``backward_eq⟩,
  ⟨predOwner, ``Model.split, mkPrivateNameCore predOwner `String.Slice.splitOnBool,
    ``CharacterSplit.boolReference, ``CharacterSplit.split, ``CharacterSplit.boolAgreement⟩,
  ⟨predOwner, ``Model.split, mkPrivateNameCore predOwner `String.Slice.splitOnDecidablePred,
    ``CharacterSplit.predReference, ``CharacterSplit.predSplit, ``CharacterSplit.predAgreement⟩,
  ⟨charOwner, ``Model.split, mkPrivateNameCore charOwner `String.Slice.splitOnChar,
    ``CharacterSplit.charReference, ``CharacterSplit.charSplit, ``CharacterSplit.charAgreement⟩,
  ⟨splitOwner, ``Model.split, mkPrivateNameCore splitOwner `String.Slice.splitAtEnd,
    ``SearcherSplit.terminalReference, ``SearcherSplit.terminal, ``SearcherSplit.terminalAgreement⟩,
  ⟨splitOwner, ``Model.split, mkPrivateNameCore splitOwner `String.Slice.splitFromLawfulSearcher,
    ``SearcherSplit.searchReference, ``SearcherSplit.search, ``SearcherSplit.searchAgreement⟩,
  ⟨ringOwner, ``HAdd.hAdd, mkPrivateNameCore ringOwner `Lean.Grind.CommRing.Expr.addDenoted,
    ``SemiringImage.addReference, ``SemiringImage.add, ``SemiringImage.addAgreement⟩,
  ⟨ringOwner, ``HMul.hMul, mkPrivateNameCore ringOwner `Lean.Grind.CommRing.Expr.mulDenoted,
    ``SemiringImage.mulReference, ``SemiringImage.mul, ``SemiringImage.mulAgreement⟩,
  ⟨ringOwner, ``HPow.hPow, mkPrivateNameCore ringOwner `Lean.Grind.CommRing.Expr.powDenoted,
    ``SemiringImage.powReference, ``SemiringImage.pow, ``SemiringImage.powAgreement⟩]

public def MatchRule.trigger (rule : MatchRule) : Name :=
  if rule.owner == ringOwner then ``Grind.CommRing.Expr.denoteSAsRing else rule.original

/-- Numerals in the quotient envelope reduce to the explicit nonnegative representative. -/
public def semiringNumeral? (sub : Expr) : MetaM (Option Expr) := do
  unless sub.getAppFn.isConstOf ``OfNat.ofNat do return none
  let #[type, k, _] := sub.getAppArgs | return none
  unless type.getAppFn.isConstOf ``Grind.Ring.OfSemiring.Q do return none
  let #[α, inst] := type.getAppArgs | return none
  let result ← Meta.mkAppOptM ``Grind.Ring.OfSemiring.natCast #[α, inst, k]
  if ← Meta.isDefEq sub result then return some result else return none

/-- Match the reference implementation and its instances at the applied operands. -/
public def specialize? (rule : MatchRule) (sub : Expr) : MetaM (Option Expr) := do
  if rule.original == ``Classical.epsilon || rule.original == ``Erased.out then
    return ← SingletonSelection.specialize? rule.helper sub
  if rule.owner == ringOwner then
    let #[_, _, _, _, lhs, rhs] := sub.getAppArgs | return none
    unless lhs.getAppFn.isConstOf ``Grind.CommRing.Expr.denoteSAsRing do return none
    let #[α, inst, ctx, a] := lhs.getAppArgs | return none
    let b ← if rule.original == ``HPow.hPow then pure rhs else do
      unless rhs.getAppFn.isConstOf ``Grind.CommRing.Expr.denoteSAsRing do return none
      let #[_, _, _, b] := rhs.getAppArgs | return none
      pure b
    let candidate := mkAppN (.const rule.helper lhs.getAppFn.constLevels!) #[α, inst, ctx, a, b]
    if ← Meta.isDefEq candidate sub then return some candidate else return none
  if rule.original == ``Model.split then
    let #[ρ, pat, model, strict, s, first, curr, le] := sub.getAppArgs | return none
    let args : Array (Option Expr) :=
      if rule.reference == ``SearcherSplit.terminalReference then
        if curr.getAppFn.isConstOf ``String.Slice.endPos then #[ρ, pat, model, strict, s, first, le] else #[]
      else if rule.reference == ``SearcherSplit.searchReference then
        if first.getAppFn.isConstOf ``String.Slice.startPos && curr.getAppFn.isConstOf ``String.Slice.startPos then
          #[ρ, pat, model, strict, none, none, none, none, none, s, le] else #[]
      else if rule.reference == ``CharacterSplit.predReference then #[pat, none, s, first, curr, le]
      else #[pat, s, first, curr, le]
    if args.isEmpty then return none
    try
      let candidate ← Meta.mkAppOptM rule.helper args
      -- The same pattern type can have a different local model. Match its instance too.
      if ← Meta.isDefEq candidate sub then return some candidate else return none
    catch _ => return none
  let #[ρ, pat, model, s, p] := sub.getAppArgs | return none
  try
    return some (← Meta.mkAppOptM rule.helper #[ρ, pat, model, none, none, s, p])
  catch _ => return none

public def addReferences (source templates : Environment) : IO Environment := do
  let mut env := source
  for rule in rules do
    unless (source.getModuleIdx? rule.owner).isSome && source.contains rule.original do continue
    let some (.defnInfo ref) := templates.find? rule.reference | throw <| IO.userError s!"missing {rule.reference}"
    unless ref.type.getUsedConstants.all source.contains && ref.value.getUsedConstants.all source.contains do continue
    let decl := Declaration.defnDecl {ref with name := rule.helper, all := [rule.helper]}
    match env.addDeclCore 0 1000 decl none with
    | .ok out => env := out
    | .error e => throw <| IO.userError (← e.toMessageData {} |>.toString)
  return env

end OmegaChecks.InitPort.PatternMatch
