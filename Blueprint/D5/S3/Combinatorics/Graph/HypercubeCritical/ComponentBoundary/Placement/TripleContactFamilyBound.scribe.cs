using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class TripleContactFamilyBoundDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "TripleContactFamilyBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triple systems with at least three extensions of each occurring pair.",
        H("A gap above the complete family on five axes"),
        Blocks(Describe.Lean(
            DescribeId.Create("triple-contact-family-fifteen"),
            DeclarationHandle.Create(Owner + "eq_five_axis_powerset_or_card_ge_fifteen_of_three_extensions"),
            H("Ten triples on five axes, or at least fifteen"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Counting triples through each axis gives the bound for at least "
                + "eight axes. On seven axes the only lower count would force every link to be "
                + "the complete graph on four axes, hence each component of the pair graph "
                + "would have five axes. On six axes, two absent pairs would force an unused "
                + "axis. At least four links therefore have at least eight edges, and every "
                + "link has at least six. On five axes the lower bound fills all ten triples."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Placement + "MinimumContactDisplacementCount"))]));
}
