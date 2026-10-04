using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TwoColorPartition;

internal sealed class AndrewsElBachraouiCharacterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiCharacter.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/andrews2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A character modulo four and a hyperbola decomposition bound the alternating odd divisor sum.",
        H("Alternating Odd Divisor Sums"),
        Blocks(
            Node("andrews-el-bachraoui-character-alternating-odd-divisor-sum-bound", "Square-root bound for the alternating divisor sum", "alternating_odd_divisor_sum_bound", "For every natural number n, the absolute value of the sum over i from zero through n of (-1) raised to n minus i, multiplied by the number of positive divisors of 2i plus one, is at most the integer quotient of the natural square root of 2n plus one, increased by one, divided by two. The character modulo four expresses the sum as a signed divisor convolution. Splitting the divisor pairs at the square root gives the bound.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
