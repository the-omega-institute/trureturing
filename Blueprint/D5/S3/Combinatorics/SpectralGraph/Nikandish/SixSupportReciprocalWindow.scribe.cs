using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class SixSupportReciprocalWindowDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportReciprocalWindow." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full endpoint-one reciprocal window and its necessary integer-spectrum test.",
        H("Strict reciprocal windows for the complete residual spectrum"),
        Blocks(
            Item("three-reciprocals", "three_reciprocals", "Three separated positive roots",
                "For every positive threshold s and all three real roots strictly above it, their reciprocal sum is positive and strictly less than 2/s+1/(T-2s). The proof allows repeated roots and consumes two exact pairwise strict inequalities."),
            Item("window", "result", "The full minimum-four endpoint-one window",
                "For every ordered real 4<=a<=b<=c on h(1)=0, the actual residual quartic factors into one root mu in (a,min(c,a+b)) and three roots above s=a+b+c. With its exact coefficients N and D and R=2/s+1/(A-min(c,a+b)-2s), the proof establishes D-NR>0 before inversion and N/D<mu<N/(D-NR). No integral splitting, selected exponent family or supplied root oracle is assumed."),
            Item("integer-candidates", "integer_candidates", "Necessary integer-spectrum candidates",
                "For every ordered integer minimum-four endpoint-one triple, if all real residual roots are integers, there is a positive divisor d of N with F(d)=0 in the strict intersection of both spectral and reciprocal windows. All three other integer roots are at least s+1, and their full factorization is retained. A surviving divisor is not a sufficient integer-spectrum test and does not bound the unbounded exponent domain. The real b=2a width-limit and all reported control-candidate/congruence data remain separate source obligations; this theorem does not certify those calculations.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportMiddleSpectrum")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointOneArithmetic"))]));
}
