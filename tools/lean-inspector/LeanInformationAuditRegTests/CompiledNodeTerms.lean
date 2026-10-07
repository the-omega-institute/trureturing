import Reg.Support.CompiledNodeTerm
import Lean.Elab.Command

namespace LeanInformationAuditRegTests.CompiledNodeTerms
open Lean Meta Elab Command

def value : Nat := id 7
def head : Nat := compiled_head%
  "{\"declaration\":[\"LeanInformationAuditRegTests\",\"CompiledNodeTerms\",\"value\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

def scopedValue (x : Nat) : Nat := id x
def scopedHead : Nat → Nat := compiled_head%
  "{\"declaration\":[\"LeanInformationAuditRegTests\",\"CompiledNodeTerms\",\"scopedValue\"],\"part\":\"value\",\"path\":[\"body\"],\"levels\":[]}"
def scopedExpected (x : Nat) : Nat := x

def intrinsicHead : Nat → Nat := compiled_head%
  "{\"declaration\":[\"LeanInformationAuditRegTests\",\"CompiledNodeTerms\",\"scopedValue\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

def generic.{u} {T : Sort u} (x : T) : T := id x
def genericHead.{u} : {T : Sort u} → T → T := @(compiled_head%
  "{\"declaration\":[\"LeanInformationAuditRegTests\",\"CompiledNodeTerms\",\"generic\"],\"part\":\"value\",\"path\":[\"body\",\"body\"],\"levels\":[[\"param\",[\"u\"]]]}")
def genericExpected.{u} {T : Sort u} (x : T) : T := x

def letScoped : Nat := let x := 7; id x
def letHead : Nat := compiled_head%
  "{\"declaration\":[\"LeanInformationAuditRegTests\",\"CompiledNodeTerms\",\"letScoped\"],\"part\":\"value\",\"path\":[\"letBody\"],\"levels\":[]}"

example : value = head := rfl
example : scopedValue = scopedHead := rfl
example : @generic = @genericHead := rfl
example : letScoped = letHead := rfl

run_meta do
  let env ← getEnv
  let readValue := fun name => do
    let some info := env.find? name | throwError "compiled_head:missing_test"
    let some value := info.value? | throwError "compiled_head:missing_value"
    pure value
  unless (← readValue ``head).equal (mkRawNatLit 7) do
    throwError "compiled_head:value"
  for (actual, expected) in #[(``scopedHead, ``scopedExpected),
      (``genericHead, ``genericExpected), (``intrinsicHead, ``scopedValue)] do
    unless (← readValue actual).equal (← readValue expected) do
      throwError "compiled_head:raw_telescope:{actual}"
  let .letE binder domain assigned _ _ ← readValue ``letScoped
    | throwError "compiled_head:let_source"
  unless (← readValue ``letHead).equal
      (.letE binder domain assigned (.bvar 0) true) do
    throwError "compiled_head:let_telescope"

/-- error: compiled_head:edge_shape:LeanInformationAuditRegTests.CompiledNodeTerms.value -/
#guard_msgs in
example : Nat := compiled_head%
  "{\"declaration\":[\"LeanInformationAuditRegTests\",\"CompiledNodeTerms\",\"value\"],\"part\":\"value\",\"path\":[\"letBody\"],\"levels\":[]}"


def dagIdentity.{u} : {T : Sort u} → T → T := @(compiled_term% "[[\"sort\",[\"param\",[\"u\"]]],[\"bvar\",0],[\"lam\",[\"x\"],\"default\",1,1],[\"lam\",[\"T\"],\"implicit\",0,2]]")
def dagModes : (x : Nat) → {y : Nat} → ⦃z : Nat⦄ → [w : Inhabited Nat] → Nat := @(compiled_term% "[[\"const\",[\"Nat\"],[]],[\"const\",[\"Inhabited\"],[[\"succ\",[\"zero\"]]]],[\"app\",1,0],[\"bvar\",3],[\"lam\",[\"w\"],\"instImplicit\",2,3],[\"lam\",[\"z\"],\"strictImplicit\",0,4],[\"lam\",[\"y\"],\"implicit\",0,5],[\"lam\",[\"x\"],\"default\",0,6]]")
def expectedModes (x : Nat) {y : Nat} ⦃z : Nat⦄ [w : Inhabited Nat] : Nat := x

def dagLet : Nat := compiled_term% "[[\"const\",[\"Nat\"],[]],[\"nat\",7],[\"bvar\",0],[\"let\",[\"x\"],0,1,2,true]]"
def dagDependentLet : Nat → Nat := compiled_term% "[[\"sort\",[\"succ\",[\"zero\"]]],[\"const\",[\"Nat\"],[]],[\"bvar\",0],[\"lam\",[\"x\"],\"default\",2,2],[\"let\",[\"T\"],0,1,3,false]]"
def dagUniverse.{u,v} : Type (max (u + 1) v) := compiled_term% "[[\"sort\",[\"max\",[\"param\",[\"u\"]],[\"imax\",[\"param\",[\"v\"]],[\"succ\",[\"param\",[\"u\"]]]]]]]"
def pair : Nat × Bool := (3, true)
def dagProjection : Nat := compiled_term% "[[\"const\",[\"LeanInformationAuditRegTests\",\"CompiledNodeTerms\",\"pair\"],[]],[\"proj\",[\"Prod\"],0,0]]"
def dagBinder : Nat → Nat := compiled_term% "[[\"const\",[\"Nat\"],[]],[\"bvar\",0],[\"lam\",[\"binder\",13],\"default\",0,1]]"
def dagApplication : Nat := compiled_term% "[[\"const\",[\"Nat\"],[]],[\"nat\",7],[\"const\",[\"id\"],[[\"succ\",[\"zero\"]]]],[\"app\",2,0],[\"app\",3,1]]"
def dagString : String := compiled_term% "[[\"str\",\"binding: x.{u}; \\\"quoted\\\"; λ;\\n\\t\"]]"

run_meta do
  let rawName := Name.str (Name.num (Name.str `_private
    "LeanInformationAuditRegTests.CompiledNodeTerms") 17) "candidate"
  addDecl <| .defnDecl {
    name := rawName, levelParams := [], type := mkConst ``Nat,
    value := .mdata { entries := [(`transportAnnotation, .ofString "original")] } (mkRawNatLit 7),
    hints := .abbrev, safety := .safe }

noncomputable def dagPrivate : Nat := compiled_term% "[[\"const\",[\"_private\",\"LeanInformationAuditRegTests.CompiledNodeTerms\",17,\"candidate\"],[]]]"
def dagAnnotated : Nat := compiled_term% "[[\"nat\",7],[\"mdata\",0]]"
noncomputable def annotatedExact : LeanInformationAudit.Contract.NodeFact := compiled_exact%
  "{\"declaration\":[\"_private\",\"LeanInformationAuditRegTests.CompiledNodeTerms\",17,\"candidate\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"
  "{\"declaration\":[\"LeanInformationAuditRegTests\",\"CompiledNodeTerms\",\"dagAnnotated\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

example : @dagIdentity = @genericExpected := rfl
example : dagLet = 7 := rfl
example : dagDependentLet = (fun x : Nat => x) := rfl
example : dagProjection = 3 := rfl
example : dagApplication = 7 := rfl
example : dagAnnotated = dagPrivate := rfl

run_meta do
  let env ← getEnv
  let readValue := fun name => do
    let some info := env.find? name | throwError "compiled_term:missing_test"
    let some value := info.value? | throwError "compiled_term:missing_value"
    pure value
  unless (← readValue ``dagIdentity).equal (← readValue ``genericExpected) do
    throwError "compiled_term:dependent_binders"
  unless (← readValue ``dagModes).equal (← readValue ``expectedModes) do
    throwError "compiled_term:binder_modes"
  unless (← readValue ``dagLet).equal
      (.letE `x (mkConst ``Nat) (mkRawNatLit 7) (.bvar 0) true) do
    throwError "compiled_term:nondependent_let_flag"

  unless (← readValue ``dagUniverse).equal
      (.sort (.max (.param `u) (.imax (.param `v) (.succ (.param `u))))) do
    throwError "compiled_term:raw_universe_constructors"
  unless (← readValue ``dagProjection).equal (.proj ``Prod 0 (mkConst ``pair)) do
    throwError "compiled_term:projection"
  unless (← readValue ``dagBinder).equal
      (.lam (.num `binder 13) (mkConst ``Nat) (.bvar 0) .default) do
    throwError "compiled_term:binder_name_components"
  unless (← readValue ``dagString).equal (.lit (.strVal "binding: x.{u}; \"quoted\"; λ;\n\t")) do
    throwError "compiled_term:string_literal"
  let rawName := Name.str (Name.num (Name.str `_private
    "LeanInformationAuditRegTests.CompiledNodeTerms") 17) "candidate"
  unless (← readValue ``dagPrivate).equal (mkConst rawName) do
    throwError "compiled_term:private_name_components"
  let .mdata originalAnnotations originalBody ← readValue rawName
    | throwError "compiled_term:annotated_source_wrapper"
  let .mdata helperAnnotations helperBody ← readValue ``dagAnnotated
    | throwError "compiled_term:helper_metadata_edge"
  unless !originalAnnotations.isEmpty && helperAnnotations.isEmpty &&
      originalBody.equal helperBody do
    throwError "compiled_term:metadata_construction_boundary"
  unless (env.find? ``annotatedExact).isSome do
    throwError "compiled_term:metadata_kernel_exact_missing"

run_elab Lean.Elab.Term.withoutErrToSorry do
  for (wire, flag) in #[
      ("[[\"const\",[\"Nat\"],[]],[\"nat\",7],[\"bvar\",0],[\"let\",[\"x\"],0,1,2,true]]", true),
      ("[[\"const\",[\"Nat\"],[]],[\"nat\",7],[\"bvar\",0],[\"let\",[\"x\"],0,1,2,false]]", false)] do
    let literal : TSyntax `str := ⟨Syntax.mkStrLit wire⟩
    let .letE _ _ _ _ actual ← Lean.Elab.Term.elabTerm
        (← `(term| compiled_term% $literal)) none
      | throwError "compiled_term:let_constructor"
    unless actual == flag do throwError "compiled_term:raw_let_flag"
  let malformed := #["[]",
    "[[\"app\",0,0]]",
    "[[\"nat\",7],[\"app\",1,0]]",
    "[[\"nat\",7,8]]",
    "[[\"bvar\",0]]",
    "[[\"fvar\",[\"x\"]]]",
    "[[\"mvar\",[\"x\"]]]",
    "[[\"sort\",[\"mvar\",[\"u\"]]]]",
    "[[\"const\",[\"Nat\"],[]],[\"bvar\",0],[\"lam\",[\"x\"],\"invalid\",0,1]]"]
  for wire in malformed do
    let literal : TSyntax `str := ⟨Syntax.mkStrLit wire⟩
    let accepted ← try
      discard <| Lean.Elab.Term.elabTerm (← `(term| compiled_term% $literal)) none
      pure true
    catch _ => pure false
    if accepted then throwError "compiled_term:malformed_accepted:{wire}"
  let literal : TSyntax `str := ⟨Syntax.mkStrLit "[[\"nat\",7],[\"const\",[\"Nat\"],[]],[\"app\",0,1]]"⟩
  let accepted ← try
    let expression ← Lean.Elab.Term.elabTerm (← `(term| compiled_term% $literal)) none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    checkWithKernel (← instantiateMVars expression)
    pure true
  catch _ => pure false
  if accepted then throwError "compiled_term:ill_typed_kernel_accepted"
  let expected ← Lean.Elab.Term.elabTerm (← `(term|
    LeanInformationAudit.Contract.ExactMatch (7 : Nat) (compiled_term% "[[\"nat\",8]]"))) none
  let accepted ← try
    let expression ← Lean.Elab.Term.elabTerm
      (← `(term| LeanInformationAudit.Contract.ExactMatch.evidence)) (some expected)
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    checkWithKernel (← instantiateMVars expression)
    pure true
  catch _ => pure false
  if accepted then throwError "compiled_term:false_exact_kernel_accepted"

end LeanInformationAuditRegTests.CompiledNodeTerms
