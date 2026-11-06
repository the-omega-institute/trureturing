// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class WheelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Wheel.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/Wheel"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/Wheel"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("Wheel"),
        Blocks(
            Node("label", "Label", "Label",
                "Actual source declaration; elaboration, native selection and audits remain OPEN.", DescribeRole.Definition),
            Node("y", "Y", "Y",
                "Actual source declaration; elaboration, native selection and audits remain OPEN.", DescribeRole.Definition),
            Node("r", "R", "R",
                "Actual source declaration; elaboration, native selection and audits remain OPEN.", DescribeRole.Definition),
            Node("z", "Z", "Z",
                "Actual source declaration; elaboration, native selection and audits remain OPEN.", DescribeRole.Definition),
            Node("e", "E", "E",
                "Actual source declaration; elaboration, native selection and audits remain OPEN.", DescribeRole.Definition),
            Node("a0", "A0", "A0",
                "Actual source declaration; elaboration, native selection and audits remain OPEN.", DescribeRole.Definition),
            Node("a1", "A1", "A1",
                "Actual source declaration; elaboration, native selection and audits remain OPEN.", DescribeRole.Definition),
            Node("b1", "B1", "B1",
                "Actual source declaration; elaboration, native selection and audits remain OPEN.", DescribeRole.Definition),
            Node("gamma", "gamma", "gamma",
                "All four ORIGINAL Gamma pairs, in their actual evolving complexes. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("gamma_pairs", "gamma_pairs", "gamma_pairs",
                "Ordered extraction uses the real native pairs. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("interface_equations", "interface_equations", "interface_equations",
                "A0 is E intersect the original Z-simplex; A1 retains the e-row simplex. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("fill0", "fill0", "fill0",
                "No pair at all in either list of filling zero. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("fill1", "fill1", "fill1",
                "The collar pair is on B1 alone, while the main endpoint also contains 134. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("collar_not_free_in_main", "collar_not_free_in_main", "collar_not_free_in_main",
                "A concrete obstruction to performing the collar pair in the whole endpoint: two distinct strict cofaces remain there. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("certificate", "certificate", "certificate",
                "The wheel's absolute certificate is a consumer of the same path E. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("seedlabel", "SeedLabel", "SeedLabel",
                "The wheel's absolute certificate is a consumer of the same path E. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("root", "root", "root",
                "p=0,u=1,v=2; no label is globally removed as a ghost. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("seed", "seed", "seed",
                "p=0,u=1,v=2; no label is globally removed as a ghost. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
