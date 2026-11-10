using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class RepeatedPairModularFamilyDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/RepeatedPairModularFamily." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full unbounded odd family beyond the recorded sufficient regions", H("The full unbounded odd family beyond the recorded sufficient regions"),
        Blocks(
            Paragraph(Text("Source: repeated-pair-modular, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02, original blob 68f394977f82d9f5f20003d20797bb5706a72bff, with the actual product-tail graph lift. The full original scientific domains, attribution, source reports and failed-method/open boundaries remain binding. Exact source controls are historical reported evidence, not a claim that they were newly reproduced by Lean. General Q3 and cases passing all prime-divisor tests remain open. Academic approval/publication boundaries are unchanged. The escape audit remains unfinished under linked issue #28398.")),
            Item("actual-family", "actual_family", "Every odd a>=5 on arbitrary distinct graph primes", "The actual four-prime exponents are a,a,2a,2a squared plus one. No finite parameter bound is used."),
            Item("comparison-identities", "comparison_identities", "All five exact positive-coefficient comparison identities", "Both repeated-coordinate choices and the other two coordinates are retained in the small-exponent comparison."),
            Item("comparison-positive", "comparison_positive", "Every original sufficient-region margin is strictly positive", "The product-tail and weighted odd-gap criteria fail, and all four choices in the small-exponent criterion fail."),
            Item("remaining-comparisons", "remaining_comparisons", "All gap and large-tail comparisons", "The family has no exponent one through four, no second equal pair, gap at least 41 and tail beyond the balanced region; the midpoint and large-tail cutoff comparisons hold for the full ray. This is a comparison with recorded sufficient criteria, not a literature-priority claim.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/RepeatedPairModularTables"))]));
}
