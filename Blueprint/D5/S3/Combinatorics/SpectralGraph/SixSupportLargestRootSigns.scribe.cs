using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class SixSupportLargestRootSignsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact received three-prime spectral statements with actual ideal-graph consumers.",
        H("SixSupportLargestRootSigns"),
        Blocks(
            Describe.Lean(DescribeId.Create("upper-base"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportLargestRootSigns.upperBase"), H("upperBase"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The exact upper endpoint bc+a+b+c+1 from the original largest-root theorem."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("upper-halfline"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportLargestRootSigns.upper_halfline"), H("upper_halfline"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For all real a>=2, b>=a+3, c>=b, c>=a^2-a and y>=0, h_C(bc+a+b+c+1+y) is strictly positive. All six shifted coefficients are positive. The a>=3 branch retains the source170-term constant coefficient; the complete a=2..3 branch bounds every negative power coefficient using 0<=a-2<=1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lower-factor"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportLargestRootSigns.lowerFactor"), H("lowerFactor"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The source T polynomial whose negative multiple is the characteristic value at M=bc+a+b+c."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lower-negative"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportLargestRootSigns.lower_negative"), H("lower_negative"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For all real a>=2, b>=a+3 and c>=b, h_C(M)=-a^2bc*T is strictly negative. Its full shifted positive identity has no finite base."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportIdealIntersectionLift"))]));
}
