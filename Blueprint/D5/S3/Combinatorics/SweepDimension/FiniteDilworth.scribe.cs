using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SweepDimension;

internal sealed class SweepFiniteDilworthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SweepDimension/FiniteDilworth.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/atlas2026dilworth");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite poset admits a chain cover with no more chains than the size of a maximum antichain.", H("Finite Dilworth chain covers"),
        Blocks(
            Describe.Lean(DescribeId.Create("width"), DeclarationHandle.Create(Prefix + "maxAntichainSize"),
                H("Maximum antichain size"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Width is the maximum cardinality of an antichain of the finite poset."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("antichain-bound"), DeclarationHandle.Create(Prefix + "card_le_maxAntichainSize"),
                H("The width bounds every antichain"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every antichain has cardinality at most the width."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("maximum-antichain"), DeclarationHandle.Create(Prefix + "exists_isAntichain_card_eq_maxAntichainSize"),
                H("A maximum antichain exists"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Some antichain attains the width, including the empty carrier case."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chain-cover"), DeclarationHandle.Create(Prefix + "exists_chain_cover"),
                H("A cover by at most width many chains"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("There is a finite family of chains covering every point, whose cardinality is at most the width. This is the finite Dilworth chain-cover theorem; the supplied proof splits at a maximum antichain and joins the resulting chain covers."))), DescribeRole.Theorem)
        )));
}
