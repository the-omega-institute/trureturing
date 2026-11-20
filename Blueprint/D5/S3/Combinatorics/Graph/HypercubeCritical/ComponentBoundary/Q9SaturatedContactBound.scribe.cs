using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SaturatedContactBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SaturatedContactBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Saturated pairs force many distance-two contacts",
        H("Saturated pairs force many distance-two contacts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-saturated-contact-bound"),
                DeclarationHandle.Create(Prefix + "distanceTwoPairs_card_ge_322"),
                H("Saturated pairs force many distance-two contacts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Suppose a 258-vertex candidate consists of two separated balanced "
                        + "cubic components of orders 72 and 186. If the 72-vertex component has "
                        + "at least 142 exterior neighbors, the two components have at least 322 "
                        + "ordered cross pairs at Hamming distance two.")),
                    Paragraph(Text("Partition the exterior points by their neighbor counts in the larger "
                        + "component. A vertex with eight selected neighbors has a unique "
                        + "exterior mate. High-high mates form eightfold edges, and the other "
                        + "mates satisfy the signed direction bound.")),
                    Paragraph(Text("The resulting incidence budget forces enough neighbors of the larger "
                        + "component in the common boundary. Every such incidence is counted by "
                        + "the cross-distance-two pairs because each common neighbor has a "
                        + "positive even count on the smaller side."))),
                DescribeRole.Theorem)),
        []));
}
