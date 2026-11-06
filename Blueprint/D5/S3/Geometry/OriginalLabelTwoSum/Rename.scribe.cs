// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class RenameDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Rename.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/Rename"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/Rename"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("Rename"),
        Blocks(
            Node("renamefamily", "renameFamily", "renameFamily",
                "Direct image of raw faces, without adjoining empty to a VOID source. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("project-rename", "project_rename", "project_rename",
                "Projection agrees exactly with the pinned mathlib image-complex API. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("renamepair", "renamePair", "renamePair",
                "Ordinary free pairs transport through an injective label map. Freeness is proved on all cofaces of the mapped ambient, rather than postulated. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("renamesequence", "renameSequence", "renameSequence",
                "Recursive transport of the ACTUAL native list. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("renamesequence-pairs", "renameSequence_pairs", "renameSequence_pairs",
                "Exact ordered coverage of the transported ordinary pairs. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("rename-operations", "rename_operations", "rename_operations",
                "Simplex, intersections and endpoint families are transported literally. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("renamefilling", "renameFilling", "renameFilling",
                "A local filling can be installed on any fresh original labels. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("renamecertificate", "renameCertificate", "renameCertificate",
                "Absolute certificates transport with every original ground/ghost label. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
