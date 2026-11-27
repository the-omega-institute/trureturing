using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9K33SmallSupportClausesDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportClauses.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The selected supports satisfy the direction-pair and size clauses used by the refutation.",
        H("Corner and support-size clauses for the contact rectangles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pairclause"),
                DeclarationHandle.Create(Owner + "pairClause"),
                H("Direction-pair witnesses satisfy the corner clauses"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A variable records a cube point and its two selected flips. A realized corner makes the disjunction over the possible points true."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sizeclause"),
                DeclarationHandle.Create(Owner + "sizeClause"),
                H("Escape from a support of size below sixty"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any component of size at least sixty has a vertex outside any listed set of fewer than sixty vertices. Seven instances supply the size clauses in the refutation."))), DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoCNF"))
        ]));
}
