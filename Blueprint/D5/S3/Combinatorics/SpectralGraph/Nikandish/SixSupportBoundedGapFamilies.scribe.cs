using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class SixSupportBoundedGapFamiliesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original complete bounded-gap families; actual operator and graph consumers, source prerequisites and attribution retained.",
        H("SixSupportBoundedGapFamilies"),
        Blocks(
            Describe.Lean(DescribeId.Create("gaps"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportBoundedGapFamilies.gaps"), H("gaps"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The original four gaps (1,2), (1,3), (2,3), (3,4)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("inertia-differences"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportBoundedGapFamilies.inertia_differences"), H("inertia_differences"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The exact upper-inertia differences for all four full real parameter families."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("low-count"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportBoundedGapFamilies.low_count"), H("low_count"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Exactly two positive roots of the actual six-cell quotient lie below three, with algebraic multiplicities, for every real minimum at least four."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportBoundedGapFamilies.result"), H("result"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Every actual ideal-intersection graph with the original four positive-integer gap families is Laplacian nonintegral. The large-minimum route consumes the two-root count and original endpoint certificates; the full classification supplies only the small-minimum foundation."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportInertiaIntervals"))]));
}
