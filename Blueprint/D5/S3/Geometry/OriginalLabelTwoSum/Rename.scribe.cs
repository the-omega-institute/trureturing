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
                "Direct image of raw faces, without adjoining empty to a VOID source.", DescribeRole.Definition),
            Node("project-rename", "project_rename", "project_rename",
                "Projection agrees exactly with the pinned mathlib image-complex API.", DescribeRole.Theorem),
            Node("renamepair", "renamePair", "renamePair",
                "Ordinary free pairs transport through an injective label map. Freeness is proved on all cofaces of the mapped ambient, rather than postulated.", DescribeRole.Definition),
            Node("renamesequence", "renameSequence", "renameSequence",
                "Recursive transport of the ACTUAL native list.", DescribeRole.Definition),
            Node("renamesequence-pairs", "renameSequence_pairs", "renameSequence_pairs",
                "Exact ordered coverage of the transported ordinary pairs.", DescribeRole.Theorem),
            Node("rename-operations", "rename_operations", "rename_operations",
                "Simplex, intersections and endpoint families are transported literally.", DescribeRole.Theorem),
            Node("renamefilling", "renameFilling", "renameFilling",
                "A local filling can be installed on any fresh original labels.", DescribeRole.Definition),
            Node("renamecertificate", "renameCertificate", "renameCertificate",
                "Absolute certificates transport with every original ground/ghost label.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            role == DescribeRole.Definition ? StatementSource.WithoutFormula() : StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(SourceText(prose)), role);

    // TextRun is one line. Keep every quoted source line, including blank separators,
    // as typed text; this is commentary, never a substitute for a Lean projection.
    private static DocumentBlock SourceText(string value) => value.Contains('\n')
        ? new DocumentBlock.Section(H("Source text"), Blocks(Array.ConvertAll(
            value.Split('\n'), line => Paragraph(Text(line.Length == 0 ? "Definitions and proofs are in the paired Lean module." : line)))))
        : Paragraph(Text(value));
}
