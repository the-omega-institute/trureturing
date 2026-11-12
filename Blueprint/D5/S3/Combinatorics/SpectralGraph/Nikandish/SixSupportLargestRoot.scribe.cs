using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class SixSupportLargestRootDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact received three-prime spectral statements with actual ideal-graph consumers.",
        H("SixSupportLargestRoot"),
        Blocks(
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportLargestRoot.result"), H("result"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("On the entire original real domain 2<=a, a+3<=b<=c and c>=a^2-a, the largest real quotient eigenvalue lies in (M,M+1), M=bc+a+b+c. A sign change gives a root; the finite set of all real quintic roots has a maximum. Positivity on the entire upper half-line bounds that maximum, and every real eigenpair is at most it."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-nonintegral"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportLargestRoot.actual_nonintegral"), H("actual_nonintegral"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every three distinct primes and every integer triple in that entire domain, the noninteger largest quotient root gives actual ideal-graph Laplacian nonintegrality. The actual eigenvector lift is consumed, not postulated."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportIdealIntersectionLift"))]));
}
