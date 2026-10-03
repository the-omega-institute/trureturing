using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingBasicRoyalReverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalReverse.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reversal with exchanged step directions is an involution on Dyck paths.",
        H("Reflection of Dyck Paths"),
        Blocks(
            Node("nonnesting-nonnestingbasicroyalreverse-reflection", "Reflected path equivalence", "reflection",
                "Reverse a Dyck path and exchange upsteps with downsteps. This operation gives a bijection of Dyck paths with itself, with the same operation as inverse.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
