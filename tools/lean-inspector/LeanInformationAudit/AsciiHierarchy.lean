import LeanInformationAudit.ProjectionSchema

namespace LeanInformationAudit

open Lean

/-- Output-only layout of the same typed rows used by the JSON serializer. -/
def renderAsciiHierarchy (root catalog arena : Name) (projection : KernelProjectionRecord) :
    Except String String := do
  projection.validateReferences root catalog
  let p := projection.canonical
  let mut lines := #[s!"CATALOG {catalog} arena={arena} verdict={p.verdict}"]
  for node in p.nodes do
    lines := lines.push s!"NODE {node.key} selected={node.generators.size} \
escape={node.escapeCount}/{p.denominator}"
    for edge in p.edges do
      if edge.source == node.key && edge.isCover then
        lines := lines.push s!"  +--[{edge.theoremName} \
capture={edge.captureCount}/{p.denominator} cert={edge.certificate}]--> {edge.target}"
    for addition in p.collapsedAdditions do
      if addition.atNode == node.key then
        lines := lines.push s!"  `--[{addition.theoremName} collapsed \
cert={addition.equalityCertificate}] {addition.atNode}"
  for row in p.leaveOneOut do
    lines := lines.push s!"LOO {row.theoremName} node={row.node} \
unique={row.uniqueCaptureCount}/{p.denominator} cert={row.certificate}"
  for row in p.certifiedChains do
    let generators := String.intercalate "," (row.generators.toList.map (·.toString))
    let classes := String.intercalate "," row.stepClasses.toList
    let increments := String.intercalate "," (row.increments.toList.map toString)
    lines := lines.push s!"CHAIN {row.chainId} generators=({generators}) classes=({classes}) \
increments=({increments}) terminal_escape={row.terminalEscapeCount} cert={row.partitionCertificate}"
  let spectrum := String.intercalate "," (p.multiplicitySpectrum.toList.map (toString ·.count))
  lines := lines.push s!"SPECTRUM h=({spectrum})"
  pure (String.intercalate "\n" lines.toList ++ "\n")

end LeanInformationAudit
