using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenThirteen;

internal sealed class FishburnBasicSumInsertionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicSumInsertion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inserting a new maximum destroys direct-sum boundaries precisely when each preceding boundary has an inversion across it.",
        H("Indecomposability after Maximum Insertion"),
        Blocks(
            Node("fishburnbasicsuminsertion-indecomposable-maximum-insertion", "The boundary criterion", "indecomposable_maximum_insertion",
                "Let p be a permutation of one through n and let s be an insertion position from zero through its length. Inserting n + 1 at s produces a sum-indecomposable permutation if and only if, for every boundary b with zero less than b and b at most s, there are positions i and j with i less than b, b at most j, and j less than the length of p such that the entry at j is at most the entry at i. Positions are numbered from zero.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
