// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class VerticalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Vertical.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/Vertical"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/Vertical"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("Vertical"),
        Blocks(
            Node("verticalgamma", "verticalGamma", "verticalGamma",
                "Source/endpoints are literal Phi states with the single maximal left fibre removed. No parent collapse, collar, or endpoint equality is an assumption. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("verticalvoid", "verticalVoid", "verticalVoid",
                "The separate VOID rule uses an original r in nonempty R. The empty right fibre emits lower=a, which is genuinely nonempty; it never collapses UNIT to VOID. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
