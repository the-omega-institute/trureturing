using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class ParentFibresDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/ParentFibres.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/ParentFibres",
            "Actual critical-fibre boundaries and coface exclusions permit independent native filling and collar batches.",
            "original-label-two-sum-parent-fibres",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("ParentFibres"),
        Blocks(
            Node("criticalpart", "criticalPart", "criticalPart",
                "These are literal X-parts; the removed label e is not an output coordinate.", DescribeRole.Definition),
            Node("localwindow", "localWindow", "localWindow",
                "These are literal X-parts; the removed label e is not an output coordinate.", DescribeRole.Definition),
            Node("localbase", "localBase", "localBase",
                "These are literal X-parts; the removed label e is not an output coordinate.", DescribeRole.Definition),
            Node("parent-fibre-base", "parent_fibre_base", "parent_fibre_base",
                "Boundary and fibre-intersection facts for the COMPUTED Cbase.", DescribeRole.Theorem),
            Node("parent-fibre-cross", "parent_fibre_cross", "parent_fibre_cross",
                "Exact cross-fibre exclusion. The one direction that can intersect is the second-kind fibre into a first-kind block, and its right part then lies in Z.", DescribeRole.Theorem),
            Node("parent-initial-fibres", "parent_initial_fibres", "parent_initial_fibres",
                "The initial fibre decomposition is PROVED from proper-boundary membership, not assumed as an endpoint or desired parent row equation.", DescribeRole.Theorem)
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
