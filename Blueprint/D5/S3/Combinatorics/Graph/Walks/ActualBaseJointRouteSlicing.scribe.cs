using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualBaseJointRouteSlicingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualBaseJointRouteSlicing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Slice the Exceptional Base Q Route from Actual Joint Pieces.",
        H("Slice the Exceptional Base Q Route from Actual Joint Pieces"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-base-joint-route-slicing-actual-base-joint-route-three-fragments"), DeclarationHandle.Create(Prefix + "actual_base_joint_route_three_fragments"),
                H("Earn the Exceptional Two-Cut Order"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At the exceptional second order, the actual middle boundary is recovered as the join of three concrete joint pieces and two restored seams. The two retained cuts lie in its first and third joint pieces, which earns their strict order on the supplied full Q route. The output exhausts that same route with exact support and edge identities; no higher-order crossing hypothesis is substituted."))), DescribeRole.Theorem))));
}
