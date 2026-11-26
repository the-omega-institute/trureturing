using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9DistanceThreeUnsharedDirectionsDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9DistanceThreeUnsharedDirections.";
    private const string Problem = "<https://arxiv.org/html/2610.09483v1#Thmproblem2>";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Direction structure at minimum-distance-three contacts without a shared flip.",
        H("Direction partitions and two-step moves"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-unshared-contact-axes"),
                DeclarationHandle.Create(Owner + "unsharedContactAxes"),
                H("The axes in the contact displacements"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take the union of the three-axis displacements to one fixed endpoint."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q9-unshared-contact-direction-partition"),
                DeclarationHandle.Create(Owner + "axes_and_partition_of_unshared_contacts"),
                H("Five contact axes force a partition of the neighbor directions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume both supports are balanced induced cubic sets at separation at "
                    + "least three. Fix an endpoint whose nearest partners at distance three "
                    + "all have disjoint occupied directions with it. Even exterior degree "
                    + "lets a contact replace each of its three "
                    + "differing axes. With only four axes available, the three repairs and the "
                    + "original endpoint would give four neighbors of one vertex. The at least "
                    + "five contact axes each occur an odd number of times in the six second-step "
                    + "directions at the fixed endpoint. Thus each of the six occurs once. " + Problem))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-unshared-contact-direction-origin"),
                DeclarationHandle.Create(Owner + "directionOrigin"),
                H("Translation by the occupied directions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Flip the occupied direction axes at the given vertex."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q9-unshared-two-step-direction-exchange"),
                DeclarationHandle.Create(Owner + "unshared_two_step_preserves_direction_origin"),
                H("Each differing axis admits a two-step move preserving the translated vertex"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume all distance-three pairs have disjoint occupied directions. For "
                    + "each differing axis of such a pair, the two occupied "
                    + "triples partition the agreeing axes. A two-step move in the second component "
                    + "replaces one differing axis by a first-step axis. Its direction triple "
                    + "exchanges the same two axes, so the translated vertex is unchanged."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9TightContactStar")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentDirectionTypes"))
        ]));
}
