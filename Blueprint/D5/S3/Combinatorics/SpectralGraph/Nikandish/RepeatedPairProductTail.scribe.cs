using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class RepeatedPairProductTailDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductTail." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strict lower endpoint for every finite repeated-pair support operator.",
        H("Positive energy on the complete tail powerset"),
        Blocks(
            Paragraph(Text("The source is the repeated-pair-product-tail note at PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02, blob 66664013207b88567bf74f1a9a0c6eaf65d07f24. This representation proves the arbitrary-index lower endpoint using the complete weighted signless energy. The empty-support loop and its edge to every tail support make the energy strictly positive; no fixed-size tensor or sampled support replaces the full domain. The upper product criterion and its equality case remain separate obligations.")),
            Item("energy", "lower_energy", "Strict weighted energy",
                "For every finite tail index set, positive real repeated exponent a, positive real tail weights, and nonzero function h on every subset, the weighted quadratic form of K-I is positive. The proof is a full sum-of-squares identity plus the nonnegative diagonal remainder. Empty tail index sets are included."),
            Item("lower-endpoint", "eigenvalue_gt_one", "The general lower endpoint",
                "For every nonzero real eigenvector of the full K at positive real parameters, its eigenvalue is strictly greater than one. No upper criterion, integer assumption, fixed number of primes, or spectrum-integrality premise is used.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairSupport"))]));
}
