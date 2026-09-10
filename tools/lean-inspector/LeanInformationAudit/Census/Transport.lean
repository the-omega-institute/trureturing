import LeanInformationAudit.Census.Report

namespace LeanInformationAudit.CensusTransport

open Lean Meta DispositionCensus

/-- Consume the exact whole-stream handoff. The query lane owns classification;
publication binds its compact-row hash, scope table and receipt digest. -/
def readHandoff (rows receipt digest : String) (report : FrozenReport)
    (generate : Option (String × String × String) := none) : IO (Array StatementKey) :=
  IO.FS.withTempDir fun directory => do
    let keys := directory / "keys.json"
    let repository ← IO.currentDir
    let direct := #[
      (repository / "tools/lean-inspector/Census/Certificate/handoff.py").toString,
      "--rows", rows, "--receipt", receipt, "--digest", digest,
      "--head", report.headSha, "--report-sha", report.reportSha256, "--output", keys.toString]
    let args := match generate with
      | none => direct
      | some (output, reportPath, selectionPrefix) => #[
          (repository / "tools/lean-inspector/Census/resources.py").toString,
          "--directory", output ++ "/logs", "--label", "handoff",
          "--budget-gib", "1", "--design-limit-gib", "1", "--wall-limit-s", "60",
          "--phase-path", output ++ "/handoff.phase", "--", "python3",
          (repository / "tools/lean-inspector/Census/Certificate/manifest.py").toString,
          "--directory", output, "--report", reportPath, "--rows", rows,
          "--receipt", receipt, "--digest", digest, "--prefix", selectionPrefix,
          "--keys-output", keys.toString]
    let result ← IO.Process.output { cmd := "python3", args }
    unless result.exitCode == 0 do throw <| IO.userError result.stderr
    let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile keys)
    (← IO.ofExcept json.getArr?).mapM fun row => do
      return ⟨← IO.ofExcept <| parseNameJson (← IO.ofExcept <| row.getObjVal? "theorem_name"),
        ← IO.ofExcept <| stringField row "statement_id"⟩

def publish (destination : String) (metadata : Json) : IO Unit :=
  IO.FS.withTempDir fun directory => do
    let certificate := directory / "certificate.json"
    IO.FS.writeFile certificate metadata.compress
    let repository ← IO.currentDir
    let result ← IO.Process.output { cmd := "python3", args := #[
      (repository / "tools/lean-inspector/Census/Certificate/handoff.py").toString,
      "--certificate", certificate.toString, "--output", destination] }
    unless result.exitCode == 0 do throw <| IO.userError result.stderr

end LeanInformationAudit.CensusTransport
