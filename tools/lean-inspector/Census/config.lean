import Lake.Toml.Load

open Lean Lake.Toml

private partial def jsonValue : Value → Json
  | .string _ value => toJson value
  | .array _ values => Json.arr (values.map jsonValue)
  | .table _ values => Json.mkObj (values.items.toList.map fun (key, value) =>
      (key.toString, jsonValue value))
  | _ => Json.null

def main (args : List String) : IO Unit := do
  let (source, output) ← match args with
    | [source] => pure (source, none)
    | [source, "--output", output] => pure (source, some output)
    | _ => throw <| IO.userError "expected Lake TOML configuration [--output FILE]"
  let result ← (loadToml (Parser.mkInputContext (← IO.FS.readFile source) source)).toBaseIO
  let .ok table := result | throw <| IO.userError "IE-C044 Lake TOML parse failed"
  let json := (jsonValue (.table .missing table)).compress
  match output with
  | none => (← IO.getStdout).putStrLn json
  | some path => IO.FS.writeFile path (json ++ "\n")
