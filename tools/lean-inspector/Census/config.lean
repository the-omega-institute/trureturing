import Lake.Toml.Load

open Lean Lake.Toml

private partial def jsonValue : Value → Json
  | .string _ value => toJson value
  | .array _ values => Json.arr (values.map jsonValue)
  | .table _ values => Json.mkObj (values.items.toList.map fun (key, value) =>
      (key.toString, jsonValue value))
  | _ => Json.null

def main (args : List String) : IO Unit := do
  let [source] := args | throw <| IO.userError "expected Lake TOML configuration"
  let result ← (loadToml (Parser.mkInputContext (← IO.FS.readFile source) source)).toBaseIO
  let .ok table := result | throw <| IO.userError "IE-C044 Lake TOML parse failed"
  (← IO.getStdout).putStrLn (jsonValue (.table .missing table)).compress
