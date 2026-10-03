using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.IndecomposableInversion;

internal sealed class FranklinInversionBasicDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionBasic.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/franklin2024inversions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stars and five-block permutations describe the forms of indecomposable permutations avoiding 321 and 1342.",
        H("FranklinInversionBasic"),
        Blocks(
            Node("franklininversionbasic-star-definition", "Star permutation", "star", "For a nonnegative integer k, the star permutation is the entry k plus one followed by the increasing list from one through k. At k equal to zero it is the singleton permutation consisting of one.", DescribeRole.Definition),
            Node("franklininversionbasic-fiveblock-definition", "Five-block permutation", "fiveBlock", "For natural numbers r, t, d and h, concatenate the increasing block of r entries starting at t plus one, the increasing block of t minus d entries starting at one, the singleton r plus t plus h plus one, the increasing block of d entries starting at t minus d plus one, and the increasing block of h entries starting at t plus r plus one. Subtraction of natural numbers is truncated at zero.", DescribeRole.Definition),
            Node("franklininversionbasic-fiveblock-mem-avoiders-theorem", "Avoidance and inversions of the five-block family", "fiveBlock_mem_avoiders", "For natural numbers r, t, d and h with r, t and d positive and d at most t, the five-block permutation belongs to I_(rt + d + h)(321, 1342). It is a nonempty indecomposable permutation of length r plus t plus h plus one, avoids 321 and 1342, and has rt plus d plus h inversions.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
