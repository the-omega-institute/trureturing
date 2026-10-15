import Lean

set_option Elab.async false

open Lean Elab Tactic

syntax "capture_declaration" command : command

elab_rules : command
  | `(command| capture_declaration $declaration:command) => do
      Command.elabCommand declaration
      let mut diagnostics : Array Json := #[]
      for diagnostic in (← get).messages.reportedPlusUnreported do
        diagnostics := diagnostics.push <| Json.mkObj [("error", toJson (diagnostic.severity == .error)),
          ("line", toJson diagnostic.pos.line), ("column", toJson diagnostic.pos.column),
          ("message", toJson (← diagnostic.data.toString))]
      IO.FS.writeFile
        "/Users/macstudio/omega/research/voa-string-01a124be/checkpoint-original-Q-filtered-no-ghost-20261013/nonzero-charge-normalized-null-frame-existence-r1/runner-home/6acd0915e8c398f812efafe6/attempt-1/compiler-declaration-diagnostics.json"
        (toJson diagnostics).compress

syntax "capture_compiler" tacticSeq : tactic

elab_rules : tactic
  | `(tactic| capture_compiler $proof:tacticSeq) => do
      try
        evalTactic (← `(tactic| ($proof:tacticSeq)))
      catch failure =>
        let message ← failure.toMessageData.toString
        let mut diagnostics : Array Json := #[]
        for diagnostic in (← getThe Core.State).messages.reportedPlusUnreported do
          diagnostics := diagnostics.push <| Json.mkObj [("error", toJson (diagnostic.severity == .error)),
            ("line", toJson diagnostic.pos.line), ("column", toJson diagnostic.pos.column),
            ("message", toJson (← diagnostic.data.toString))]
        let evidence := Json.mkObj [("kind", toJson "direct-elaborator-exception"),
          ("message", toJson message), ("diagnostics", toJson diagnostics)]
        IO.FS.writeFile
          "/Users/macstudio/omega/research/voa-string-01a124be/checkpoint-original-Q-filtered-no-ghost-20261013/nonzero-charge-normalized-null-frame-existence-r1/runner-home/6acd0915e8c398f812efafe6/attempt-1/compiler-diagnostic.json"
          evidence.compress
        throw failure

run_cmd do
  let mut diagnostics : Array Lean.Json := #[]
  for diagnostic in (← get).messages.reportedPlusUnreported do
    diagnostics := diagnostics.push <| Lean.Json.mkObj [("error", Lean.toJson (diagnostic.severity == .error)),
      ("message", Lean.toJson (← diagnostic.data.toString))]
  IO.FS.writeFile
    "/Users/macstudio/omega/research/voa-string-01a124be/checkpoint-original-Q-filtered-no-ghost-20261013/nonzero-charge-normalized-null-frame-existence-r1/runner-home/6acd0915e8c398f812efafe6/attempt-1/compiler-capture-diagnostics.json"
    (Lean.toJson diagnostics).compress
