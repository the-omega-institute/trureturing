import LeanInformationAudit.Projection.AsciiHierarchy

open Lean LeanInformationAudit

namespace LeanInformationAudit.Tests.Projection

run_cmd do
  let projection : KernelProjectionRecord := {
    denominator := 12
    nodes := #[{
      key := "K_full", generators := #[`id], escapeCount := 0,
      relationCertificate := `full }, {
      key := "K_empty", generators := #[], escapeCount := 12, relationCertificate := `empty }]
    edges := #[{
      source := "K_empty", target := "K_full", theoremName := `id,
      isCover := false, captureCount := 12, certificate := `shortcut }] }
  let output ← match renderAsciiHierarchy `Root `Catalog `Arena projection with
    | .ok output => pure output
    | .error message => throwError message
  unless output == "CATALOG Catalog arena=Arena verdict=irredundant\nNODE K_empty selected=0 escape=12/12\nNODE K_full selected=1 escape=0/12\nSPECTRUM h=()\n" do
    throwError "covers-only renderer mismatch: {output}"
  let other ← match renderAsciiHierarchy `Root `Catalog `Arena
      { projection with nodes := projection.nodes.reverse } with
    | .ok output => pure output
    | .error message => throwError message
  unless output == other do throwError "renderer order is not canonical"

end LeanInformationAudit.Tests.Projection
