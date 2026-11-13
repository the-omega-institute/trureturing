using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class SixSupportLaplacianPolynomialDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact polynomial identities for the actual six-support quotient.",
        H("SixSupportLaplacianPolynomial"),
        Blocks(
            Describe.Lean(DescribeId.Create("zero-factor"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportLaplacianPolynomial.charpoly_zero_factor"), H("Zero factor"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Over every commutative coefficient ring, the characteristic polynomial of the literal six-cell matrix is X times its reduced characteristic polynomial. The zero eigenvalue is removed exactly once as a polynomial factor; no nonzero root or multiplicity is silently discarded."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("determinant-formula"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportLaplacianPolynomial.determinant_formula"), H("Division-free determinant"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For all parameters and every commutative ring, the actual six-by-six determinant equals the full three-factor expression with all mixed correction terms. The proof uses the literal matrix and exact minors. Specializations, arithmetic restrictions and actual graph eigenvalue transport are separate consumers."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot"))]));
}
