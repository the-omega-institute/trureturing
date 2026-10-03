using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingFourPrimitiveTwoPrefixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveTwoPrefix.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primitivity fixes the positions of the first two small letters.",
        H("Forced Prefix after an Initial Two"),
        Blocks(
            Node("nonnesting-nonnestingfourprimitivetwoprefix-primitive-two-positions", "Positions of one, two, and three", "primitive_two_positions",
                "A primitive avoider of size at least three beginning with two has its first one at position one, first three at position two, second two at position three, and second one at position four.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
