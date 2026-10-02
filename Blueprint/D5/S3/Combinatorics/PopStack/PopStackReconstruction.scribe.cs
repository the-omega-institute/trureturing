using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackReconstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackReconstruction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let a permutation be written as a prefix, a nonempty block of consecutive values, and a suffix. There are a permutation skeleton and a standardized block whose inflation recovers the original permutation; their lengths are respectively the prefix length plus one plus the suffix length, and the block length. If every proper nontrivial interval of the original permutation is contained in that block, then the skeleton occurs in the original permutation and is simple. If the original permutation also belongs to C, so does the skeleton.",
        H("Recovering a skeleton from a consecutive-value block"),
        Blocks(
            Node("pop-stack-popstackreconstruction-reconstruct-interval", "Recovering a skeleton from a consecutive-value block", "reconstruct_interval",
                "Let a permutation be written as a prefix, a nonempty block of consecutive values, and a suffix. There are a permutation skeleton and a standardized block whose inflation recovers the original permutation; their lengths are respectively the prefix length plus one plus the suffix length, and the block length. If every proper nontrivial interval of the original permutation is contained in that block, then the skeleton occurs in the original permutation and is simple. If the original permutation also belongs to C, so does the skeleton.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
