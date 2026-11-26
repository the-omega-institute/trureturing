using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9SharedContactCNFDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9SharedContactCNF.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized shared-contact supports satisfy the degree, parity and geometric clauses.",
        H("Clauses satisfied by the cube supports"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("upper-clause"),
                DeclarationHandle.Create(Owner + "upperClause"),
                H("Upper degree clauses"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The valuation makes each vertex bit equal to support membership. Four distinct "
                    + "occupied neighbors would violate cubicity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lower-clause"),
                DeclarationHandle.Create(Owner + "lowerClause"),
                H("Lower degree clauses"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Seven omitted neighbors at an occupied vertex would violate cubicity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parity-clause"),
                DeclarationHandle.Create(Owner + "parityClause"),
                H("Each prefix parity extends by exclusive-or"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The prefix variables store successive parities of occupied neighbors. At the last "
                    + "coordinate the output is the occupancy bit. The four clauses give the truth table for "
                    + "one such update."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("square-clause"),
                DeclarationHandle.Create(Owner + "squareClause"),
                H("Square exclusion clauses"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("XOR with one coordinate bit gives the corresponding cube neighbor. The four occupied "
                    + "vertices would form a square."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("separation-clause"),
                DeclarationHandle.Create(Owner + "separationClause"),
                H("Separation clauses"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two supports cannot contain both vertices of a cross-pair at distance at most "
                    + "two."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9SharedContactClauseSemantics"))
        ]));
}
