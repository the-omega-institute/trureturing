using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9DirectionCoverageDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Direction coverage in induced components of the nine-cube",
        H("Two-axis and five-axis restrictions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-direction-pair-coverage"),
                DeclarationHandle.Create(Module + ".exists_pair_directions"),
                H("A singular two-axis mask forces a turn"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In a fixed actual component, a mask of two directions with singular Huang Gram defect forces a vertex incident with both directions. Without such a vertex the masked edges form a matching, and the two parity degree bounds have product at most one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-five-mask-three-directions"),
                DeclarationHandle.Create(Module + ".exists_three_directions_in_five_mask"),
                H("A singular five-axis mask forces three directions at one vertex"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If all vertices had at most two neighbors within a mask of five axes, the product of the degree bounds would be at most four. This is below the mask size, so a singular defect forces a vertex with at least three active directions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-five-mask-direction-type"),
                DeclarationHandle.Create(Module + ".exists_direction_type_in_five_mask"),
                H("A five-axis mask singular on a fixed parity contains a whole direction triple in a subcubic component"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix an actual subcubic component and a parity. If the masked Huang Gram defect is singular on that parity for a mask of five axes, some vertex in the component has exactly three neighbors in the component, and all three of its directions lie inside the mask."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-two-direction-covering-components"),
                DeclarationHandle.Create(Module + ".exists_two_direction_covering_components"),
                H("Two actual components of a 258-point candidate satisfy both coverage conditions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Any 258-point subset of the nine-cube inducing maximum degree at most three has two distinct actual connected components in which every direction pair meets at a vertex and every five-axis set contains a complete three-direction type. The components are selected before the masks, so both coverage conditions hold throughout each of the two components.")),
                    Paragraph(Text("In each component, a pair can be covered by the direction set of any actual vertex that contains both axes. Each five-axis set must contain the whole direction triple of an actual degree-three vertex. Relabeling the axes preserves both conditions. These restrictions apply to candidates for Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
