// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class FibreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Fibre.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/Fibre"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/Fibre"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("Fibre"),
        Blocks(
            Node("liftfibre", "liftFibre", "liftFibre",
                "Non-VOID local sequences lift over a literal fibre. This is used for Gamma and filling/collar schedules; all ordinary lower faces are still nonempty even when a=empty. No homotopy or parent certificate is an input. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("liftfibre-pairs", "liftFibre_pairs", "liftFibre_pairs",
                "Exact ordered coverage for the ACTUAL native fibre list, including every pair of a supplied Gamma, filling-main or separate collar sequence. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
