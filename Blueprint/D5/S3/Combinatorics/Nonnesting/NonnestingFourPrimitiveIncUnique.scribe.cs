using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingFourPrimitiveIncUniqueDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveIncUnique.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exactly one increasing-order word is primitive at each positive size.",
        H("Unique Primitive Increasing Word"),
        Blocks(
            Node("nonnesting-nonnestingfourprimitiveincunique-primitive-increasing-exists", "Existence at each positive size", "primitive_increasing_exists",
                "For every positive n, at least one increasing-order avoider of size n is primitive.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingfourprimitiveincunique-primitive-increasing-unique", "Uniqueness at each positive size", "primitive_increasing_unique",
                "Any two primitive increasing-order avoiders of the same positive size are equal.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
