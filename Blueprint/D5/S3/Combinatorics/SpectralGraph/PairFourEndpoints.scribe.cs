using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairFourEndpointsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/PairFourEndpoints." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All endpoint exclusions for repeated exponent four.", H("All endpoint exclusions for repeated exponent four."),
        Blocks(
            Paragraph(Text("Source: four-prime-pair-four, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The original parameter domains, attribution and failed-method limitations are retained. Formal proofs are task-local integrations of the full source results. General four-prime and higher-prime Q3 remain open outside the stated families. Original academic approval and publication boundaries are unchanged.")),
            Item("two", "two_nonzero", "All positive integer tails at least two avoid root two", "The full unbounded integer-tail exclusion includes the sixteen strict nonsquare discriminants, the exceptional rational factorization rows, the small positive region and the entire large-tail negative region. No tail rectangle is scanned."),
            Item("three", "three_zero_iff", "The exact exchanged endpoint-three pair", "Among all integer tails at least two, root three occurs exactly for tails two and six in either order. This exact exception is retained in the spectral consumer.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionDeterminants"))]));
}
