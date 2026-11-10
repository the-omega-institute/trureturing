using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class ParentCellsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/ParentCells.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/ParentCells",
            "The original compiler computes its parent core and proves critical nonemptiness, all boundaries, absence and antichains.",
            "original-label-two-sum-parent-cells",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("ParentCells"),
        Blocks(
            Node("parentcore", "parentCore", "parentCore",
                "Exact Cout from the ORIGINAL proof, on the full original parent ground.", DescribeRole.Definition),
            Node("parentcritical", "parentCritical", "parentCritical",
                "Ordered-index provenance is retained by the compiler schedules; this finite set is the actual output critical family, after proving no unwanted inclusions.", DescribeRole.Definition),
            Node("mem-parentcritical", "mem_parentCritical", "mem_parentCritical",
                "Literal critical provenance, consumed by the filling endpoint assembly.", DescribeRole.Theorem),
            Node("parentcelldata", "parentCellData", "parentCellData",
                "Complete critical-face proof for the COMPUTED Cout. Compiler constructs the main and separate core lists; neither collapse is a hypothesis here.", DescribeRole.Definition)
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
