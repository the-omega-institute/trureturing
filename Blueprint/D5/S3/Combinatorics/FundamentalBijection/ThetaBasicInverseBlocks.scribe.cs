using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaBasicInverseBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseBlocks.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The inverse fundamental bijection closes consecutive record blocks into cycles.",
        H("Cycles from Record Blocks"),
        Blocks(
            Node("fundamental-bijection-thetabasicinverseblocks-cyclefrom-b-record-block", "The cycle of a record maximum", "cycleFrom_B_record_block",
                "For a permutation p, a block beginning at a left-to-right maximum and ending immediately before the next such maximum, or at the end of p, is exactly the cycle of its initial value in the inverse image of p.", DescribeRole.Theorem),
            Node("fundamental-bijection-thetabasicinverseblocks-nonrecord-not-b-leader", "Cycle maxima are record values", "nonrecord_not_B_leader",
                "A letter whose position in a permutation is not a left-to-right maximum is not the largest element of its cycle in the inverse image under the fundamental bijection.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
