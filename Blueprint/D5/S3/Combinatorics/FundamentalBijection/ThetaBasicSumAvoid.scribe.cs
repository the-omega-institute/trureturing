using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaBasicSumAvoidDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumAvoid.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Descending endpoints confine triples to a single direct-sum factor, and 312-avoidance orders record blocks.",
        H("Descending Triples and Direct Sums"),
        Blocks(
            Node("fundamental-bijection-thetabasicsumavoid-descendingtriple", "A triple with descending endpoints", "DescendingTriple",
                "A descending triple consists of three increasing positions whose first value exceeds their last value and whose values satisfy a specified ternary relation.", DescribeRole.Definition),
            Node("fundamental-bijection-thetabasicsumavoid-descendingtriple-sum-iff", "Triples in a direct sum", "descendingTriple_sum_iff",
                "For a ternary relation invariant under adding the same integer to all three values, a direct sum contains a descending triple satisfying that relation exactly when one of its two factors does.", DescribeRole.Theorem),
            Node("fundamental-bijection-thetabasicsumavoid-avoid312-record-block-decreasing", "Decreasing tails of record blocks", "avoid312_record_block_decreasing",
                "In a 312-avoiding permutation, entries strictly after a left-to-right maximum and before the next record boundary decrease with position.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
