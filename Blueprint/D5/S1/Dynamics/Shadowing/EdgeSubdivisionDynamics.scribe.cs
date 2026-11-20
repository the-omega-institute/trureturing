using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class EdgeSubdivisionDynamicsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/EdgeSubdivisionDynamics.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exactness and expansion from closed edge subdivisions",
        H("Exactness and expansion from closed edge subdivisions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("contracting-inverse-charts-exactness"),
                DeclarationHandle.Create(Owner + "topologicallyExact_of_inverse_charts"),
                H("Contracting inverse charts give exactness"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pull a contracting branch through a prescribed point at each iterate. The branch eventually fits inside the given open set while its image covers a whole edge. The next iterate covers the carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compact-cell-expansion"),
                DeclarationHandle.Create(Owner + "forwardBowenBound_one_of_compact_cells"),
                H("Finite compact cells give a uniform expansion scale"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Disjoint compact cells have a common positive lower bound on separation. Along an orbit pair lying below that scale, intersecting cells force exponential growth of the distance, hence every sufficiently small forward Bowen set is a singleton."))),
                DescribeRole.Theorem))));
}
