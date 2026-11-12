using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class SixSupportMiddleSpectrumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete received real endpoint-one regimes with all original integer-point boundaries.",
        H("SixSupportMiddleSpectrum"),
        Blocks(
            Describe.Lean(DescribeId.Create("factor-roots"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportMiddleSpectrum.factor_roots"), H("factor_roots"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The complete actual endpoint-one residual splits into four real linear factors, with one root in (a,min(c,a+b)) and all three remaining roots above a+b+c, counting multiplicity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportMiddleSpectrum.result"), H("result"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every ordered real a>2+sqrt(3) on h_C(1)=0, sign(c+a-b(b+2)) equals the sign of the unique low residual root minus b. The equality branch and both strict branches retain the full factorization and all three high roots; no integer-point existence is implied."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointOneSpectrum"))]));
}
