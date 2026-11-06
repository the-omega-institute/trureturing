// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class ParentCellsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/ParentCells.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/ParentCells"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/ParentCells"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("ParentCells"),
        Blocks(
            Node("parentcore", "parentCore", "parentCore",
                "Exact Cout from the ORIGINAL proof, on the full original parent ground. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("parentcritical", "parentCritical", "parentCritical",
                "Ordered-index provenance is retained by the compiler schedules; this finite set is the actual output critical family, after proving no unwanted inclusions. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("mem-parentcritical", "mem_parentCritical", "mem_parentCritical",
                "Literal critical provenance, consumed by the filling endpoint assembly. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("parentcelldata", "parentCellData", "parentCellData",
                "Complete critical-face proof for the COMPUTED Cout. Compiler constructs the main and separate core lists; neither collapse is a hypothesis here. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
