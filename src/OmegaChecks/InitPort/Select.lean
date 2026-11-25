import Lean
import OmegaChecks.Interface
import OmegaChecks.ModuleSurface

open Lean

/-- Bisect a rejected group. A successful check certifies all its roots in one pass. -/
partial def rejectedRoots (strict visible standard : Environment) (rows : Array (Name × Name))
    (log : IO.FS.Handle) (pending : System.FilePath) : IO Unit := do
  if rows.isEmpty then return
  IO.FS.writeFile pending (toJson (rows.map (·.1.toString))).compress
  try
    OmegaChecks.Interface.check strict visible standard rows
    return
  catch err =>
    if rows.size == 1 then
      let name := rows[0]!.1.replacePrefix `Omega .anonymous
      log.putStrLn (toJson #[name.toString, err.toString]).compress
      return
    let mid := rows.size / 2
    rejectedRoots strict visible standard (rows.extract 0 mid) log pending
    rejectedRoots strict visible standard (rows.extract mid rows.size) log pending

def main (args : List String) : IO Unit := do
  let path :: seed :: transfer :: report :: roots := args | throw <| IO.userError "expected target path, seed, transfer, report and modules"
  let original ← searchPathRef.get
  let lib ← getLibDir (← findSysroot)
  let strictPath := System.SearchPath.parse path
  searchPathRef.set [transfer, seed]
  let data ← importModules #[{module := `OmegaImported}] {}
  let some home := data.getModuleIdx? `OmegaImported | throw <| IO.userError "missing candidate declarations"
  let candidates := data.header.moduleData[home]!.constNames
  searchPathRef.set strictPath
  let imports := roots.toArray.map (fun n => {module := n.toName : Import})
  let strict ← importModules imports {} (level := .private)
  let visible ← importModules imports {} (level := .exported)
  let owners ← OmegaChecks.ModuleSurface.officialModules strict lib
  let official := owners.map fun n => {module := n : Import}
  searchPathRef.set (original ++ [lib])
  let standard ← importModules (official.push {module := `OmegaChecks.Interface.Equations}) {}
  let log ← IO.FS.Handle.mk report .write
  let mut rows := #[]
  for n in candidates do
    if isPrivateName n || n.isInternal then continue
    let some idx := strict.getModuleIdxFor? n | throw <| IO.userError s!"no owner for {n}"
    rows := rows.push (n, strict.header.moduleNames[idx]!.replacePrefix `OmegaInit `Init)
  let pending := (System.FilePath.mk report).withExtension "pending"
  let mut i := 0
  while i < rows.size do
    rejectedRoots strict visible standard (rows.extract i (i + 32)) log pending
    i := i + 32
