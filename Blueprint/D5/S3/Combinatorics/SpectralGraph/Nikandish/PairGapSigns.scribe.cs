using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairGapSignsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairGapSigns." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete exact signs for all original high-root windows.", H("Complete exact signs for all original high-root windows."),
        Blocks(
            Paragraph(Text("Source: the four small-gap and midpoint notes, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The original parameter domains, attribution and failed-method limitations are retained. Formal proofs are task-local integrations of the full source results. General four-prime and higher-prime Q3 remain open outside the stated families. Original academic approval and publication boundaries are unchanged.")),
            Item("midpoint", "midpoint_positive", "The generic positive midpoint", "All eighteen source coefficients are included for every positive real a,b,r, with no size restriction."),
            Item("square", "square_lower_negative", "The full square-size negative endpoint", "The entire real a>=1,r>=2,b>=r squared domain is covered by all 91 positive coefficients, including equality."),
            Item("weighted", "weighted_lower_negative", "The complete weighted half-unit endpoint", "All 128 coefficients prove negativity for positive real a,r>=3 and 4ab>=(2a+1)r squared, including equality."),
            Item("even", "even_lower_negative", "The full parity-aware lower endpoint", "All 128 coefficients prove negativity for real r>=2 and 8ab>=(2a+1)r squared. Using the resulting unit interval to exclude integers separately requires even integer r."),
            Item("unequal", "unequal_lower_negative", "The full unequal-tail negative endpoint", "Every positive real a and c>b>=1 has the original negative value at a+b+1."),
            Item("two", "gap_two_positive", "Every gap-two intermediate positive value", "The full source positive polynomial is retained over all positive real a,b.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionDeterminants"))]));
}
