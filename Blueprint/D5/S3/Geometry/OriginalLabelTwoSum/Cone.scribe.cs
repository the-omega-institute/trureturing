using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class ConeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Cone.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/Cone",
            "Descending native cone schedules and the genuine terminal Gamma branch handle removal of the left core vertex.",
            "original-label-two-sum-cone",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("Cone"),
        Blocks(
            Node("collapsecone", "collapseCone", "collapseCone",
                "Every ordinary cone, on the full unchanged original ground, collapses to its actual apex by the descending list of nonempty faces avoiding that apex.", DescribeRole.Definition),
            Node("terminalgamma", "terminalGamma", "terminalGamma",
                "Terminal p=e branch with X nonempty: run the supplied right Gamma in the Y-piece, fixing the whole delta(X)*E term, before using an original X-apex.", DescribeRole.Definition),
            Node("terminalatinterface", "terminalAtInterface", "terminalAtInterface",
                "Output type records the computed original vertex, not an assumed endpoint.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(SourceText(prose)), role);

    // TextRun is one line. Keep every quoted source line, including blank separators,
    // as typed text; this is commentary, never a substitute for a Lean projection.
    private static DocumentBlock SourceText(string value) => value.Contains('\n')
        ? new DocumentBlock.Section(H("Source text"), Blocks(Array.ConvertAll(
            value.Split('\n'), line => Paragraph(Text(line.Length == 0 ? "Definitions and proofs are in the paired Lean module." : line)))))
        : Paragraph(Text(value));
}
