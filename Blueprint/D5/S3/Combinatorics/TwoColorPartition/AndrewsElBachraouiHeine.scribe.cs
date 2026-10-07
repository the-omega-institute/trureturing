using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TwoColorPartition;

internal sealed class AndrewsElBachraouiHeineDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiHeine.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/andrews2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite q-difference recurrence yields the nilpotent q-binomial identity.",
        H("Finite Nilpotent q-Binomial Identity"),
        Blocks(
            Node("andrews-el-bachraoui-heine-nilpotent-q-binomial", "Nilpotent q-binomial transformation", "nilpotent_q_binomial", "Let R be a commutative ring, let a, q and z belong to R, and let N be natural. If q raised to N and z raised to N are zero, then the product over i below N of (1 minus a z q raised to i) times the inverse of (1 minus z q raised to i) equals the sum over r below N of z raised to r times the corresponding finite product with factors (1 minus a q raised to i) and inverses of (1 minus q raised to i plus 1).", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
