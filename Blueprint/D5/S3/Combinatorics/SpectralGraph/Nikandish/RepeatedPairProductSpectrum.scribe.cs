using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class RepeatedPairProductSpectrumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductSpectrum." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full finite-tail product criterion, including equality.",
        H("The full finite-tail product criterion, including equality."),
        Blocks(
            Paragraph(Text("The source is repeated-pair-product-tail at PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02, blob 66664013207b88567bf74f1a9a0c6eaf65d07f24. Every tail subset and every positive parameter is retained. Diagonal similarity, the complete energy identity, a nonempty proper support and the real finite spectral theorem give the actual minimum. The equality argument requires at least two tail coordinates and makes no claim for the three-prime equality block. General Q3 outside the sufficient condition remains open.")),
            Item("minimum", "product_minimum_window", "A genuine smallest eigenvalue in (1,2)", "For every finite nontrivial tail index, a>=1, all positive real tail weights, and a squared times the full tail product at least (a squared minus one) times the shifted tail product plus (a-1)(a-2), the complete operator has a nonzero eigenvector of eigenvalue strictly between one and two. This eigenvalue is no larger than the eigenvalue of every nonzero real eigenpair of the same full operator. Equality in the hypothesis is included."),
            Item("actual", "actual_product_tail", "Actual ideal-graph nonintegrality for every number of primes at least four", "For arbitrary distinct prime coordinates, positive natural repeated exponent and positive tail exponents over every finite nontrivial index, the exact source product condition gives an actual graph eigenvalue strictly between V-1 and V and proves nonintegrality. The vertex count is the natural cardinal expression, not a scalar surrogate or a redefined graph.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductTail")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairSupport"))]));
}
