// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class RectanglesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Rectangles.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/Rectangles"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/Rectangles"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("Rectangles"),
        Blocks(
            Node("phi-split", "phi_split", "phi_split",
                "Exact split-coordinate membership of the raw parent, including raw empty. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("deletionrectangle", "deletionRectangle", "deletionRectangle",
                "The deletion rectangle has no assumed local or parent schedule. All cofaces are derived from native child freeness, alpha not in L, and raw E downwardness. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("linkrectangle", "linkRectangle", "linkRectangle",
                "A link projection can have an empty alpha. Its raw coface condition is obtained from an actual child e-containing pair by the caller. Every emitted lower is nonempty because each selected tau lies outside delta(Z). Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
