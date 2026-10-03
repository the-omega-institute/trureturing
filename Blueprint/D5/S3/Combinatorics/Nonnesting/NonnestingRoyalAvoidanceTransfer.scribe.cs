using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingRoyalAvoidanceTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingRoyalAvoidanceTransfer.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reversed occurrence positions transfer avoidance between the two pairs of patterns.",
        H("Transfer Between Two Avoidance Classes"),
        Blocks(
            Node("nonnesting-nonnestingroyalavoidancetransfer-avoidance-transfer", "Avoidance under occurrence reversal", "avoidance_transfer",
                "Let positive block sizes sum to n. Let w and v be doubled nonnesting words whose first-occurrence orders are respectively the increasing-block permutation and the hook-block permutation with reversed block sizes. Suppose, for each index i less than n, the first position of the reversed-index hook letter in v plus the second position of the corresponding increasing-block letter in w plus one equals the length of w, and the same equality holds with first and second positions exchanged. Then w avoids 1132 and 2213 if and only if v avoids 1233 and 1322.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
