// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class CellLabelsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/CellLabels"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/CellLabels"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("CellLabels"),
        Blocks(
            Node("wheelcell", "wheelCell", "wheelCell",
                "The original wheel transform removes the interface coordinate only when it actually occurs, and uses the new 1-spoke only in that branch. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("wheelcell_recovery", "wheelCell_recovery", "wheelCell_recovery",
                "The new first spoke distinguishes the two branches and recovers e. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("wheelcell_card", "wheelCell_card", "wheelCell_card",
                "Exact +2 in BOTH branches, including an interface critical singleton. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("wheelcell_count", "wheelCell_count", "wheelCell_count",
                "No critical-face count is lost to image collisions. This is a consequence of the explicit recovery equation, not a count assumption of the compiler. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("label", "Label", "Label",
                "The full supply of original labels; a finite prefix uses only finitely many. No Fintype on this infinite pool is assumed by any native collapse. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("p", "p", "p",
                "The full supply of original labels; a finite prefix uses only finitely many. No Fintype on this infinite pool is assumed by any native collapse. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("u", "u", "u",
                "The full supply of original labels; a finite prefix uses only finitely many. No Fintype on this infinite pool is assumed by any native collapse. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("v", "v", "v",
                "The full supply of original labels; a finite prefix uses only finitely many. No Fintype on this infinite pool is assumed by any native collapse. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("r", "r", "r",
                "Source index j,k denotes the mathematical label r(j+1,k+1). Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("s", "S", "S",
                "Source index j,k denotes the mathematical label r(j+1,k+1). Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("interface", "interface", "interface",
                "Source index j,k denotes the mathematical label r(j+1,k+1). Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("first", "first", "first",
                "Source index j,k denotes the mathematical label r(j+1,k+1). Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("second", "second", "second",
                "Source index j,k denotes the mathematical label r(j+1,k+1). Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("ground", "ground", "ground",
                "Source index j,k denotes the mathematical label r(j+1,k+1). Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("critical_recurrence", "critical_recurrence", "critical_recurrence",
                "The literal closed-chain label formula is consumed by the ORIGINAL conditional critical transform, with no block-diagonal row replacement. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("critical_sizes", "critical_sizes", "critical_sizes",
                "Every finite closed prefix has exactly the stated critical sizes. This arithmetic does not instantiate a closed-chain native history or its graph binding. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("rows", "rows", "rows",
                "Coupled original chord rows, retained as an ordered list before root union. This is source preparation for the graph-bound iteration, not that theorem. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
