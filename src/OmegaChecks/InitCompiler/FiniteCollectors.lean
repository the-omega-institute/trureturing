module
public import Lean
import Init.Data.Iterators.Consumers.Collect
import Init.Data.Iterators.Consumers.Total

/-! Specialize a list collection only when its finite instance is available and the
pinned source kernel accepts the complete replacement by definitional equality. -/

namespace OmegaChecks.InitCompiler
open Lean Meta

public def finiteCollectors (env : Environment) (input : Expr) : IO Expr := do
  unless input.getUsedConstants.contains ``Std.Iter.toList do return input
  let rewrite : MetaM Expr := Meta.transform input (pre := fun sub => do
    unless sub.isAppOfArity ``Std.Iter.toList 4 do return .continue
    let args := sub.getAppArgs
    let total := mkAppN (.const ``Std.Iter.ensureTermination sub.getAppFn.constLevels!)
      #[args[0]!, args[1]!, args[3]!]
    try
      let value ← mkAppOptM ``Std.Iter.Total.toList #[args[0]!, args[1]!, args[2]!, none, total]
      return .done (← instantiateMVars value)
    catch _ => return .continue)
  let .ok result ← (rewrite.run' |>.toIO' {fileName := "<finite collector>", fileMap := default} {env}).toBaseIO
    | return input
  unless !result.equal input && !result.hasMVar && (Kernel.check env {} result).isOk &&
      Kernel.isDefEqGuarded env {} input result do return input
  return result

end OmegaChecks.InitCompiler
