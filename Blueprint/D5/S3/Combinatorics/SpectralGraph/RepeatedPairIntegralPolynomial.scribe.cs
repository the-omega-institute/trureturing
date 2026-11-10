using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class RepeatedPairIntegralPolynomialDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/RepeatedPairIntegralPolynomial." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full integer polynomial from actual graph integrality", H("Full integer polynomial from actual graph integrality"),
        Blocks(
            Paragraph(Text("Source: repeated-pair-modular, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02, original blob 68f394977f82d9f5f20003d20797bb5706a72bff, with the actual product-tail graph lift. The full original scientific domains, attribution, source reports and failed-method/open boundaries remain binding. Exact source controls are historical reported evidence, not a claim that they were newly reproduced by Lean. General Q3 and cases passing all prime-divisor tests remain open. Academic approval/publication boundaries are unchanged. The escape audit remains unfinished under linked issue #28398.")),
            Item("map-operator", "map_operator", "Every ring reduction is the full repeated-pair operator", "The map identity retains every support subset and every entry."),
            Item("actual-factorization", "actual_factorization", "Actual integrality yields a complete integer factorization", "The full Hermitian eigenbasis, actual nonzero graph lifts and integral eigenvalues give every characteristic root with multiplicity."),
            Item("actual-reduction-splits", "actual_reduction_splits", "Every field reduction splits", "This follows from the entire integer factorization, rather than sampling a few eigenvalues or reductions.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/RepeatedPairProductSpectrum"))]));
}
