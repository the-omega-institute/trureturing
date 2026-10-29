using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class FerrersLevelGluingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/FerrersLevelGluing.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithSums/RookTheory/barrese2023levels");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The last-row bound is exactly the information needed to glue successive levels of the same Ferrers board.",
        H("Gluing Ordered Levels"),
        Blocks(
            Node("ferrerslevelgluing-flatPathsEquiv", "Exact gluing bijection", "flatPathsEquiv",
                "For every r,U,a,u, cut the flat row tuple into consecutive blocks of r+1 rows. The last row v of the first block bounds every row of the remainder because the full tuple is decreasing. Conversely, a first block ending at v and a decreasing remainder bounded by v concatenate to a decreasing tuple. These two operations are mutually inverse and preserve every ordered block sum. Induction includes the unique empty tuple and empty path.", DescribeRole.Definition),
            Node("ferrerslevelgluing-flat-card", "All flat rows are counted", "flat_card",
                "The cardinality of the complete flat fiber equals F(a,u). There are no omitted compatibility conditions between the blocks: the inverse gluing proof establishes global weak decrease across each boundary. The count applies to zero rows, zero dimensions and infeasible ordered totals.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
