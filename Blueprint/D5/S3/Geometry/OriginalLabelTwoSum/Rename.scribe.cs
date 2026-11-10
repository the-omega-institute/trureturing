// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class RenameDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Rename.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/Rename",
            "Injective original-label transport reuses mathlib complex maps and transports actual native pairs, sequences and fillings.",
            "original-label-two-sum-rename",
            Anchor.ParseCanonical("mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic")),
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
            role == DescribeRole.Definition ? StatementSource.WithoutFormula() : StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(SourceText(prose)), role);

    // TextRun is one line. Keep every quoted source line, including blank separators,
    // as typed text; this is commentary, never a substitute for a Lean projection.
    private static DocumentBlock SourceText(string value) => value.Contains('\n')
        ? new DocumentBlock.Section(H("Source text"), Blocks(Array.ConvertAll(
            value.Split('\n'), line => Paragraph(Text(line.Length == 0 ? " " : line)))))
        : Paragraph(Text(value));
}
