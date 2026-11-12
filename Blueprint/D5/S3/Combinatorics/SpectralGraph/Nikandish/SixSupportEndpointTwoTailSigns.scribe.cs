using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class SixSupportEndpointTwoTailSignsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact received three-prime spectral statements with actual ideal-graph consumers.",
        H("SixSupportEndpointTwoTailSigns"),
        Blocks(
            Describe.Lean(DescribeId.Create("first-positive"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointTwoTailSigns.first_positive"), H("first_positive"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Outside b<2a-2, the exact positive expansion proves h_C(2)>0 for every ordered real a>=8. This is the complete portion needed by the endpoint-two classifier; the distinct sharp-alpha boundary is not claimed here."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("second-positive"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointTwoTailSigns.second_positive"), H("second_positive"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The original84-term remainder identity, retaining both nonnegative square terms, proves h_C(2)>0 in the complete rationally parameterized c>=9a/4-8 region at a>=8."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fifth-difference-positive"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointTwoTailSigns.fifth_difference_positive"), H("fifth_difference_positive"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The source44-coefficient expansion proves 4h_C(2)-h_C(5)>0 for arbitrary three real exponents each>=8."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourth-difference-positive"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointTwoTailSigns.fourth_difference_positive"), H("fourth_difference_positive"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The source112-coefficient identity proves h_C(4)-3h_C(2)>0 on the complete real a>=40 ratio rectangle; all denominator factors are proved positive."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportIdealIntersectionLift"))]));
}
