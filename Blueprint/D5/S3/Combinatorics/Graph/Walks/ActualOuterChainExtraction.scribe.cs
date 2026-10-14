using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualOuterChainExtractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualOuterChainExtraction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extract the literal intermediate route and its inventories from a supplied closed parent.",
        H("Actual Route Inventories"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-closed-route-outer-chain"),
                DeclarationHandle.Create(Prefix + "actual_closed_route_outer_chain"),
                H("Extract the Entire Outside Chain"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("From a supplied linked route whose first and final pieces are kept distinct, the theorem constructs the complete walk between their adjacent endpoints. Its interior support is exactly the concatenated supports of the intermediate pieces. Both the support and edge permutations are earned for the same supplied reversed parent cycle, including the single closing seam. The intermediate route is not supplied as a factorization assumption."))), DescribeRole.Theorem))));
}
