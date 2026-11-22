using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry.Permutohedra;

internal sealed class PrefixExchangesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Geometry/Permutohedra/PrefixExchanges";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/rossi2026permutohedron");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent exchanges and prefix ranks.",
        H("Adjacent exchanges and prefix ranks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prefixexchanges-exchange"),
                DeclarationHandle.Create(Module + ".exchange"),
                H("Adjacent exchange"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a proper rank d, exchange swaps the entries at positions d minus one and d in the zero-based list of a permutation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prefixexchanges-exchange-prefix-ne-iff"),
                DeclarationHandle.Create(Module + ".exchange_prefix_ne_iff"),
                H("One exchange"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Interchanging adjacent positions across rank d changes the unordered prefix exactly at rank d."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prefixexchanges-batch"),
                DeclarationHandle.Create(Module + ".batch"),
                H("Sequential exchanges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Fold the list of proper ranks from left to right, applying each exchange to the current permutation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prefixexchanges-batch-prefix-ne-iff"),
                DeclarationHandle.Create(Module + ".batch_prefix_ne_iff"),
                H("A batch of exchanges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Apply the exchanges in list order to the current permutation. For a list of distinct proper ranks, the final prefix differs from the original prefix exactly at the ranks in the list. At a given rank only the exchange across that rank can change its prefix."))),
                DescribeRole.Theorem))));
}
