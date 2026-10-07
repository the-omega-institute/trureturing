using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TwoColorPartition;

internal sealed class AndrewsElBachraouiBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiBounds.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/andrews2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd divisor pairing and triangular coefficient counting give the required bounds.",
        H("Divisor and Gauss-Product Bounds"),
        Blocks(
            Node("andrews-el-bachraoui-bounds-odd-divisors-card-le", "Odd divisor cardinality bound", "odd_divisors_card_le", "For every natural number M that is odd, the cardinality of its divisor set is at most the natural square root of M plus one.", DescribeRole.Theorem),
            Node("andrews-el-bachraoui-bounds-gauss-product-coefficient-count-bound", "Gauss-product coefficient bound", "gauss_product_coefficient_count_bound", "For every natural number n, the coefficient of degree n in the finite Gauss product equals the cardinality of the parity-compatible triangular pairs. When n is at least 5, its real value is at most 97 divided by 120 times n, plus 27 divided by 32 times the square root of 2n plus one half, plus 13 divided by 25.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
