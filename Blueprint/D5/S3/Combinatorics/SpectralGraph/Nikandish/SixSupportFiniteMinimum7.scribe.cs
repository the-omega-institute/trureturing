using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class SixSupportFiniteMinimum7Document : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact received three-prime spectral statements with actual ideal-graph consumers.",
        H("SixSupportFiniteMinimum7"),
        Blocks(
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportFiniteMinimum7.result"), H("result"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Both characteristic endpoints one and two are nonzero at all15051 original parameter pairs with minimum7, using complete kernel Boolean evaluation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("domain-card"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportFiniteMinimum7.domain_card"), H("domain_card"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The complete original strict-pair domain for minimum7 contains exactly15051 parameter positions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-application"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportFiniteMinimum7.actual_application"), H("actual_application"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every three distinct primes and every original pair in this entire15051-position base, the actual ideal graph has nonintegral Laplacian spectrum. This is a full finite-domain consumer of the uniform positive-real low-root theorem."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportIdealIntersectionLift"))]));
}
