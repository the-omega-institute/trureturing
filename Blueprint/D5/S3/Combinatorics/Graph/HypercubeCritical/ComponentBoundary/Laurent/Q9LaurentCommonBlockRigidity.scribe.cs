using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent;

internal sealed class Q9LaurentCommonBlockRigidityDocument : IScribeDocumentDefinition
{
    private const string Boundary =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/";
    private const string Owner = Boundary + "Q9LaurentCommonBlockRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A shared direction triple forces order fifty-four in a connected cubic Laurent component.",
        H("A shared direction triple forces a constant partition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-laurent-common-block-order-fifty-four"),
                DeclarationHandle.Create(Owner + "constant_partition_and_card_eq_fiftyFour_of_common_block"),
                H("Constant row partition and fifty-four vertices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a connected induced cubic subgraph of the nine-cube satisfy a "
                        + "Laurent identity on one parity side. If one direction triple belongs to "
                        + "every row partition on that side, all those partitions agree and the "
                        + "subgraph has fifty-four vertices.")),
                    Paragraph(Text("Deleting the common triple preserves each remaining component's "
                        + "partition, since two shared blocks determine all three. Its projected rows "
                        + "form a product of two three-point stars with a height inherited from the "
                        + "Laurent exponent. These products realize the balanced cut boxes in the "
                        + "shared-cut theorem. Hence the remaining two blocks agree up to exchange. "
                        + "The constant partition gives only three direction triples, excluding the "
                        + "seven-or-more alternative in the published order theorem.")),
                    Paragraph(Text("This settles the common-triple case of the one-sided Laurent "
                        + "approach to Hong, Wu and Xia’s Problem 2. "
                        + "<https://arxiv.org/html/2610.09483v1#Thmproblem2>"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9LaurentNormalizedBoxes")),
         DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9LaurentSharedCutBoxes")),
         DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9LaurentTransverseFibers")),
         DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9LaurentFiveTypeExclusion"))]));
}
