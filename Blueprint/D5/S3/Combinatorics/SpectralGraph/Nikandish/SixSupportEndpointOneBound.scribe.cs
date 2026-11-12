using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class SixSupportEndpointOneBoundDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact received three-prime spectral statements with actual ideal-graph consumers.",
        H("SixSupportEndpointOneBound"),
        Blocks(
            Describe.Lean(DescribeId.Create("sum-model"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointOneBound.sumModel"), H("sumModel"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The source q=b+c,z=bc model of h_C(1), with exact Q,K and cubic P_a(q) coefficients."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sum-model-identity"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointOneBound.sumModel_identity"), H("sumModel_identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The q,z expression is exactly the original quintic at one for every real a,b,c."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointOneBound.result"), H("result"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every ordered real 2<=a<=b<=c with h_C(1)=0, b+c>=2a^2-2a+1. Equality holds exactly at b=a,c=(a-1)(2a-1). The entire comparison at z0=a(q-a) and the strict negative B factor are derived. The separate received spectral-order and separation statements remain distinct obligations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("third-exponent-bound"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointOneBound.third_exponent_bound"), H("third_exponent_bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Every ordered integer endpoint-one triple with 2<=a<b<=c satisfies c>a^2-a, as required by the full largest-root route."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportIdealIntersectionLift"))]));
}
