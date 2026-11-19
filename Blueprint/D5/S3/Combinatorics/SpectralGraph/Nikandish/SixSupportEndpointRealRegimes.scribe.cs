using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class SixSupportEndpointRealRegimesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete received real endpoint-one regimes with all original integer-point boundaries.",
        H("SixSupportEndpointRealRegimes"),
        Blocks(
            Describe.Lean(DescribeId.Create("threshold-signs"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointRealRegimes.threshold_signs"), H("threshold_signs"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every real a>=9, the complete endpoint polynomial is negative at the equality threshold on b=a+3 and positive there on b=2a. Exact polynomial identities and positive coefficients prove both signs without finite samples."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exponent-points"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointRealRegimes.exponent_points"), H("exponent_points"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every real a>=9, there is an actual endpoint-one third exponent c>b in each of the two original strict sign regimes. The intermediate-value witnesses belong to the full original cubic, not an encoded answer premise or assumed feasible subset."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointRealRegimes.result"), H("result"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Neither strict regime eventually dominates the real endpoint surface: for every a>=9 the b=a+3 family has its low residual root above b, and b=2a has it below b. Both statements consume the complete actual quotient quartic factorization, the exact endpoint equations and all three roots above the total sum. Real exponents here do not assert integer exponent points."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportMiddleSpectrum")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportUniformTail"))]));
}
