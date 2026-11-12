using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class SixSupportIdealIntersectionLiftDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full six-cell transport to the actual ideal-intersection graph.",
        H("SixSupportIdealIntersectionLift"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-eigenvalue"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportIdealIntersectionLift.actual_eigenvalue"), H("Actual eigenvalue transport"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every injective triple of primes, positive integer exponent triple and nonzero six-cell eigenvector at a nonzero eigenvalue, the reflected value V minus that eigenvalue is an eigenvalue of the actual combinatorial Laplacian on all nonzero proper ideals of ZMod n. The proof derives weighted cancellation, proves the lifted vector nonzero and verifies the exact complement action. A polynomial root alone is not an eigenvector premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportIdealIntersectionLift.result"), H("Full low-root consumer"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every ordered positive exponent triple on three distinct primes, the actual ideal graph has an eigenvalue strictly between V minus three and V. This consumes the original complete positive-real low-root theorem and the actual support/ideal isomorphism. Full nonintegrality uses additional integer-root exclusions; general higher-prime Q3 remains separate."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions"))]));
}
