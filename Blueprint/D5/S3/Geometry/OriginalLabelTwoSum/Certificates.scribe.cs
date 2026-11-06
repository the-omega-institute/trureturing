// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class CertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Certificates.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/Certificates"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/Certificates"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("Certificates"),
        Blocks(
            Node("facets", "facets", "facets",
                "A finite union of raw simplices, with the empty index family equal to VOID. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("endpoint", "endpoint", "endpoint",
                "A finite union of raw simplices, with the empty index family equal to VOID. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("criticaldata", "CriticalData", "CriticalData",
                "Exact ordinary critical-cell conditions, including ALL proper subfaces. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("filling", "Filling", "Filling",
                "A local filling need not have a contractible collar. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("certificate", "Certificate", "Certificate",
                "A left input carries an actual vertex and ordinary main/core lists. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("critical_intersection", "critical_intersection", "critical_intersection",
                "Actual literal simplex/core intersection, with the empty face retained. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("critical_overlap", "critical_overlap", "critical_overlap",
                "Distinct retained cells meet only in proper boundary faces. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
