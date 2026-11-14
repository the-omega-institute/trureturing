using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class SixSupportEndpointTwoTailDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact received three-prime spectral statements with actual ideal-graph consumers.",
        H("SixSupportEndpointTwoTail"),
        Blocks(
            Describe.Lean(DescribeId.Create("rectangle"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointTwoTail.rectangle"), H("rectangle"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every ordered real a>=8 on the exact h_C(2)=0 surface, b<2a-2 and c<9a/4-8. Inverse rational parameters are derived from these exact inequalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("endpoint-signs"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointTwoTail.endpoint_signs"), H("endpoint_signs"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every ordered real a>=40 on the complete endpoint-two surface, h_C(4)>0>h_C(5), by the source D4,D5 identities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointTwoTail.result"), H("result"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The entire original real endpoint-two tail has a noninteger quotient root strictly between four and five."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-nonintegral"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointTwoTail.actual_nonintegral"), H("actual_nonintegral"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Every positive integer triple in the full endpoint-two tail, for every three distinct primes, has nonintegral actual ideal-intersection Laplacian."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportIdealIntersectionLift"))]));
}
