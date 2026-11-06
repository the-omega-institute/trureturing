// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class ConeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Cone.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/Cone"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/Cone"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("Cone"),
        Blocks(
            Node("collapsecone", "collapseCone", "collapseCone",
                "Every ordinary cone, on the full unchanged original ground, collapses to its actual apex by the descending list of nonempty faces avoiding that apex. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("terminalgamma", "terminalGamma", "terminalGamma",
                "Terminal p=e branch with X nonempty: run the supplied right Gamma in the Y-piece, fixing the whole delta(X)*E term, before using an original X-apex. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("terminalatinterface", "terminalAtInterface", "terminalAtInterface",
                "Output type records the computed original vertex, not an assumed endpoint. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
