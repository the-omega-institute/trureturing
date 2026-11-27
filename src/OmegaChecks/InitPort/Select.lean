import Lean
import OmegaChecks.Interface
import OmegaChecks.ModuleSurface

open Lean

/-- Bisect a rejected group. A successful check certifies all its roots in one pass. -/
partial def rejectedRoots (strict visible standard : Environment) (rows : Array (Name × Name))
    (log : IO.FS.Handle) (pending : System.FilePath)
    (checked : IO.Ref OmegaChecks.Interface.CheckedSites) : IO Unit := do
  if rows.isEmpty then return
  IO.FS.writeFile pending (toJson (rows.map (·.1.toString))).compress
  try
    let next ← OmegaChecks.Interface.checkSites strict visible standard rows (← checked.get)
    checked.set next
    return
  catch err =>
    if rows.size == 1 then
      let name := rows[0]!.1.replacePrefix `Omega .anonymous
      log.putStrLn (toJson #[name.toString, err.toString]).compress
      return
    let mid := rows.size / 2
    rejectedRoots strict visible standard (rows.extract 0 mid) log pending checked
    rejectedRoots strict visible standard (rows.extract mid rows.size) log pending checked

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
  let mut official := owners.map fun n => {module := n : Import}
  if roots.contains "OmegaInit" then
    let sourceDir ← IO.currentDir
    let mut downstream := #[]
    for file in ← (sourceDir / "OmegaMathlib").walkDir do
      if file.extension == some "lean" then
        let name ← moduleNameOfFileName file sourceDir
        downstream := downstream.push (name.replacePrefix `OmegaMathlib `Mathlib)
    downstream := downstream.qsort Name.lt
    let targets := downstream.map fun n => s!"@mathlib/+{n}:olean"
    let job ← IO.Process.spawn {cmd := "lake", args := #["build"] ++ targets}
    unless (← job.wait) == 0 do throw <| IO.userError "failed to build the official OmegaMathlib counterparts"
    official := official ++ downstream.map fun n => {module := n : Import}
  searchPathRef.set (original ++ [lib])
  let standard ← importModules (official.push {module := `OmegaChecks.Interface.Equations}) {}
  let log ← IO.FS.Handle.mk report .write
  -- A downstream import can select a different copy of a generated upstream name.
  -- Computational entries must agree in full. Theorems may have distinct proofs
  -- of a structurally identical proposition at each definition site.
  let candidateNames := NameSet.ofList (candidates.toList.map (·.replacePrefix `Omega .anonymous))
  let mut encountered : NameSet := {}
  let mut duplicated : NameSet := {}
  for data in standard.header.moduleData do
    for n in data.constNames do
      if candidateNames.contains n then
        if encountered.contains n then duplicated := duplicated.insert n
        encountered := encountered.insert n
  let mut conflicts : NameSet := {}
  for (owner, data) in standard.header.moduleNames.zip standard.header.moduleData do
    for n in data.constNames do
      if duplicated.contains n && !conflicts.contains n && !OmegaChecks.Interface.declaredIn standard n owner then
        conflicts := conflicts.insert n
        log.putStrLn (toJson #[n.toString, s!"distinct official declarations under the same name in {owner} and other modules"]).compress
  let mut rows := #[]
  for n in candidates do
    if isPrivateName n || n.isInternal then continue
    if conflicts.contains (n.replacePrefix `Omega .anonymous) then continue
    let some idx := strict.getModuleIdxFor? n | throw <| IO.userError s!"no owner for {n}"
    rows := rows.push (n, strict.header.moduleNames[idx]!.replacePrefix `OmegaInit `Init)
  let pending := (System.FilePath.mk report).withExtension "pending"
  let checked ← IO.mkRef {}
  let mut i := 0
  while i < rows.size do
    rejectedRoots strict visible standard (rows.extract i (i + 32)) log pending checked
    i := i + 32
