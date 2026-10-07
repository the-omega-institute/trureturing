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

end LeanInformationAuditRegTests.CompiledNodeTerms
