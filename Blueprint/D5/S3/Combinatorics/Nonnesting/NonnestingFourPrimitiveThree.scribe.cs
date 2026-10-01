using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingFourPrimitiveThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveThree.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forbidden patterns restrict the two occurrence orders of three distinct letters.",
        H("Three-Letter Order Restrictions"),
        Blocks(
            Node("nonnesting-nonnestingfourprimitivethree-forbidden-last-first", "A smallest letter cannot start last", "forbidden_last_first",
                "For three increasing letters with matching first and second orders, avoiding 2231 and 3221 excludes either ordering in which the smallest letter first appears after both others.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingfourprimitivethree-separated-three-orders", "Separation forced by the remaining patterns", "separated_three_orders",
                "Avoiding 1231 and 1312 forces the second occurrence of the earliest relevant letter before a later first occurrence in each of three specified first-order arrangements.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
