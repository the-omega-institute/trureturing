module
public import Init.Prelude

/-! A pure macro method table cannot be packed and recovered at every context. -/

namespace OmegaChecks.InitBoundaries.MacroReferences
open Lean
open Macro

private def context (ref : MethodsRef) : Context := ⟨ref, .anonymous, 0, 0, 0, .missing⟩
private def initial : State := default

private def query (read : MacroM Methods) (ref : MethodsRef) : Bool :=
  match read (context ref) initial with
  | .error .. => false
  | .ok methods s =>
    match methods.hasDecl .anonymous (context ref) s with
    | .error .. => false
    | .ok answer _ => answer

private def table (answer : MethodsRef → Bool) : Methods where
  expandMacro? := fun _ => pure none
  getCurrNamespace := pure .anonymous
  hasDecl := fun _ ctx st => .ok (answer ctx.methods) st
  resolveNamespace := fun _ => pure []
  resolveGlobalName := fun _ => pure []

/-- Each callback is tested with its own packed reference in the context. -/
public def preservesQuery (pack : type_of% @mkMethods) (read : type_of% @getMethods) : Prop :=
  ∀ answer : MethodsRef → Bool, query read (pack (table answer)) = answer (pack (table answer))

public theorem noQueryRoundTrip (pack : type_of% @mkMethods) (read : type_of% @getMethods)
    (preserves : preservesQuery pack read) : False := by
  let diagonal (ref : MethodsRef) := !(query read ref)
  let ref := pack (table diagonal)
  have fixed : query read ref = !(query read ref) := preserves diagonal
  cases h : query read ref <;> rw [h] at fixed <;> cases fixed

/-- Recovering the whole table and state also recovers its answer to the single query. -/
public theorem noRoundTrip (pack : type_of% @mkMethods) (read : type_of% @getMethods)
    (recover : ∀ (m : Methods) (ctx : Context) (s : State), ctx.methods = pack m → read ctx s = .ok m s) : False := by
  apply noQueryRoundTrip pack read
  intro answer
  unfold query
  rw [recover (table answer) (context _) initial rfl]
  rfl

end OmegaChecks.InitBoundaries.MacroReferences
