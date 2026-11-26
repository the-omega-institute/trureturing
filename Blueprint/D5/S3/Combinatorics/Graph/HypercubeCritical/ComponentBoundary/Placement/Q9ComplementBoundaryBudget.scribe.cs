using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9ComplementBoundaryBudgetDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9ComplementBoundaryBudget.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A 258-vertex subcubic restriction of the nine-cube leaves room for at most 369 omitted edges.",
        H("The edge budget of the complement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complement-darts-le"),
                DeclarationHandle.Create(Owner + "complement_darts_le"),
                H("At most 738 oriented complement edges"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A 258-vertex induced subcubic set sends at least six edges per vertex to its "
                    + "complement. Edge reversal counts these incidences at the complement, whose 254 "
                    + "vertices have ambient degree nine. At most 738 oriented edges then remain inside the "
                    + "complement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("packed-darts-le"),
                DeclarationHandle.Create(Owner + "packed_darts_le"),
                H("Internal and crossing edges share the budget"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For two disjoint subsets of a finite vertex set of the nine-cube, their internal "
                    + "edges and their crossing edges contribute twice each to the total number of oriented "
                    + "edges in that vertex set."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9ExteriorEdgeLiftCount"))
        ]));
}
