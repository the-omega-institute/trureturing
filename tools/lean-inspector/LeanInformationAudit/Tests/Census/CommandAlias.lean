import LeanInformationAudit.Tests.Census.Command

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command

namespace LeanInformationAudit.Tests.Census.CommandAlias

-- Q2: exercise the command, input bytes, and environment commit together.
/-- info: alias-rejected=true report-preserved=true certificate-absent=true -/
#guard_msgs in
run_cmd IO.FS.withTempDir fun dir => do
  let reportPath := dir / "report.json"
  let digest := Syntax.mkStrLit ("sha256:" ++ Sha256.hex Command.inputBytes.toUTF8)
  IO.FS.writeFile reportPath Command.inputBytes
  for args in [#["-s", reportPath.toString, (dir / "symlink.json").toString],
      #[reportPath.toString, (dir / "hardlink.json").toString]] do
    let result ← IO.Process.output { cmd := "/bin/ln", args := args }
    unless result.exitCode == 0 do throwError "link fixture setup failed: {result.stderr}"
  for destination in [reportPath, dir / "." / "report.json", dir / "child" / ".." / "report.json",
      dir / "symlink.json", dir / "hardlink.json"] do
    IO.FS.createDirAll (dir / "child")
    IO.FS.writeFile reportPath Command.inputBytes
    let input := Syntax.mkStrLit reportPath.toString
    let destinationStx := Syntax.mkStrLit destination.toString
    let before ← get
    elabCommand (← `(command|
        #disposition_census root LeanInformationAudit.Tests.Census.Evidence
          report $input head "fixture-head" report_sha256 $digest
          inventory LeanInformationAudit.Tests.Census.Evidence.inventory
          certificate aliasCoverage output $destinationStx))
    let messages := (← get).messages.toList.drop before.messages.toList.length
    let expected := "IE-C044 DispositionCensusMismatch head=fixture-head \
      component=output_path expected=distinct-from-report actual=report-alias"
    let rejected ← messages.anyM fun message => do
      pure (message.severity == .error && (← message.data.toString) == expected)
    modify fun state => { state with messages := before.messages }
    let preserved := (← IO.FS.readFile reportPath) == Command.inputBytes
    let absent := !(← getEnv).contains
      `LeanInformationAudit.Tests.Census.CommandAlias.aliasCoverage
    unless rejected && preserved && absent do
      throwError "alias-rejected={rejected} report-preserved={preserved} \
        certificate-absent={absent}"
  logInfo "alias-rejected=true report-preserved=true certificate-absent=true"

end LeanInformationAudit.Tests.Census.CommandAlias
