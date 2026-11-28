import OmegaChecks.InitPort.Translation

open Lean InitKernelPort

private def checkConsumer (dir : System.FilePath) (owner promise token : Name) (elim : String) : IO Unit := do
  let args := if elim == "rec" then "(fun _ _ => b) p" else "p (fun _ _ => b)"
  let consumer := "universe u\nnoncomputable def use {α : Type} {β : Sort u} " ++
    s!"(p : {promise} α) (b : β) : β := {promise}.{elim} (motive := fun _ => β) {args}\n"
  for access in ["", "all "] do
    let source := s!"module\nprelude\nimport {access}{owner}\n" ++ consumer
    let result ← IO.Process.output {
      cmd := "lean", args := #["--stdin", "--json"],
      env := #[("LEAN_PATH", some dir.toString)]} (some source)
    if access == "" then
      let diagnostic := (Json.parse result.stdout).toOption
      let exactError := diagnostic.any fun msg =>
        (msg.getObjValAs? String "severity").toOption == some "error" &&
          (msg.getObjValAs? String "data").toOption == some s!"(kernel) unknown constant '{token}'"
      unless result.exitCode == 1 && exactError do
        throw <| IO.userError s!"unexpected ordinary import for {promise}.{elim}: {result.stdout}{result.stderr}"
    else unless result.exitCode == 0 do
      throw <| IO.userError s!"import all failed for {promise}.{elim}: {result.stdout}{result.stderr}"

/-- Check the exact eliminator types with the same visibility as a consumer of the
pinned Promise module. Its branch telescopes mention the private pointed token type. -/
def main (args : List String) : IO Unit := do
  let library :: names := args | throw <| IO.userError "expected a strict library directory and eliminators"
  let upstream := `Init.System.Promise
  let target := `OmegaInit.System.Promise
  let token := mkPrivateNameCore upstream `IO.PromisePointed
  let load (dir : System.FilePath) (owner : Name) := do
    searchPathRef.set [dir]
    let visible ← importModules #[{ module := owner }] {} (level := .exported)
    let full ← importModules #[{ module := owner, importAll := true }] {}
    return (visible, full)
  let officialDir ← getLibDir (← findSysroot)
  let (visible, full) ← load officialDir upstream
  let (strict, strictFull) ← load library target
  let failsOn (env : Environment) (type : Expr) (hidden : Name) : Bool :=
    match Kernel.check env {} type with
    | .error (.unknownConstant _ missing) => missing == hidden
    | _ => false
  for elim in names do
    unless ["rec", "recOn", "casesOn"].contains elim do throw <| IO.userError s!"unknown eliminator {elim}"
    let name := Name.str `IO.Promise elim
    let n := portName name
    let some src := visible.find? name | throw <| IO.userError s!"missing upstream {name}"
    let some dst := strict.find? n | throw <| IO.userError s!"missing strict {n}"
    let pinned := src.type.instantiateLevelParams src.levelParams (dst.levelParams.map Level.param)
    let expected := translate portName pinned
    unless src.numLevelParams == dst.numLevelParams &&
        visible.getModuleIdxFor? name == visible.getModuleIdx? upstream &&
        strict.getModuleIdxFor? n == strict.getModuleIdx? target &&
        (full.find? name).any (fun ci => ci.type.equal src.type) &&
        (strictFull.find? n).any (fun ci => ci.type.equal dst.type) &&
        failsOn visible pinned token && failsOn strict expected (portName token) &&
        (Kernel.check full {} pinned).isOk && (Kernel.check strictFull {} expected).isOk &&
        (Kernel.check strictFull {} dst.type).isOk && Kernel.isDefEqGuarded strictFull {} expected dst.type do
      throw <| IO.userError s!"unexpected Promise eliminator type or visibility for {name}"
    checkConsumer officialDir upstream `IO.Promise token elim
    checkConsumer library target (portName `IO.Promise) (portName token) elim
    IO.println (toJson #[upstream.toString, name.toString, token.toString, (portName token).toString]).compress
