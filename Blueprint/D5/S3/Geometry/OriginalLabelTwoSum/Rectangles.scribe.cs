using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class RectanglesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Rectangles.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/Rectangles",
            "Deletion and link rectangles derive whole-current coface proofs before emitting descending native pairs.",
            "original-label-two-sum-rectangles",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("Rectangles"),
        Blocks(
            Node("phi-split", "phi_split", "phi_split",
                "Exact split-coordinate membership of the raw parent, including raw empty. ", DescribeRole.Theorem),
            Node("deletionrectangle", "deletionRectangle", "deletionRectangle",
                "The deletion rectangle has no assumed local or parent schedule. All cofaces are derived from native child freeness, alpha not in L, and raw E downwardness. ", DescribeRole.Definition),
            Node("linkrectangle", "linkRectangle", "linkRectangle",
                "A link projection can have an empty alpha. Its raw coface condition is obtained from an actual child e-containing pair by the caller. Every emitted lower is nonempty because each selected tau lies outside delta(Z). ", DescribeRole.Definition)
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
