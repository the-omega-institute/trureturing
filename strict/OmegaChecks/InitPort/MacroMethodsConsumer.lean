module
prelude
public import OmegaInit.Prelude

/-- Call the method table recovered from this context, preserving its input state. -/
@[export omega_macro_methods_query]
public def queryTable (methods : Omega.Lean.Macro.Methods) (context : Omega.Lean.Macro.Context)
    (state : Omega.Lean.Macro.State) : Omega.EStateM.Result Omega.Lean.Macro.Exception Omega.Lean.Macro.State Omega.Bool :=
  let ctx := { context with methods := Omega.Lean.Macro.mkMethods methods }
  match Omega.Lean.Macro.getMethods ctx state with
  | .error err s => .error err s
  | .ok table s => table.hasDecl .anonymous ctx s
