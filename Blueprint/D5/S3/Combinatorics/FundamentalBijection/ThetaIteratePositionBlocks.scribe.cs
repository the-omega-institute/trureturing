using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIteratePositionBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIteratePositionBlocks.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous 132-avoidance of a permutation and its inverse constrains the positions of one and the maximum.",
        H("Positional Constraints in Record Blocks"),
        Blocks(
            Node("fundamental-bijection-thetaiteratepositionblocks-suffix-after-one-increasing", "The increasing suffix after one", "suffix_after_one_increasing",
                "In a 132-avoiding permutation, the entries after an occurrence of one increase with position.", DescribeRole.Theorem),
            Node("fundamental-bijection-thetaiteratepositionblocks-final-block-predecessor-one", "One at the end of the final block", "final_block_predecessor_one",
                "If a permutation and its inverse fundamental image both avoid 132 and its maximum occurs at a position strictly above zero and at least two places before the end, then the permutation ends with one.", DescribeRole.Theorem),
            Node("fundamental-bijection-thetaiteratepositionblocks-one-block-second-one", "One after an initial maximum", "one_block_second_one",
                "If a permutation of size at least three and its inverse fundamental image both avoid 132, the permutation starts with its maximum and ends with a value greater than one, then its second entry is one.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
