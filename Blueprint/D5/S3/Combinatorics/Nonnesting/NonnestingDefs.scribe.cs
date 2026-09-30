using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Doubled-word avoidance classes and their generating-function identities are defined.",
        H("Nonnesting Avoidance and Generating Functions"),
        Blocks(
            Node("nonnesting-nonnestingdefs-letters", "Number of pattern letters", "letters",
                "The largest letter appearing in a pattern specifies its ordered alphabet.", DescribeRole.Definition),
            Node("nonnesting-nonnestingdefs-occurs", "Pattern occurrence", "Occurs",
                "A pattern occurs in a word when an ordered relabeling of the pattern is a subsequence of that word.", DescribeRole.Definition),
            Node("nonnesting-nonnestingdefs-avoiders", "Nonnesting pattern avoiders", "avoiders",
                "An avoider is a permutation of two copies of each letter from one through n that avoids 1221, 2112, and every listed pattern.", DescribeRole.Definition),
            Node("nonnesting-nonnestingdefs-gf", "Ordinary generating function", "gf",
                "The coefficient of degree n is the number of avoiders of size n.", DescribeRole.Definition),
            Node("nonnesting-nonnestingdefs-claim1322", "Single-pattern counting identity", "claim1322",
                "For every positive n, n times the number of 1322 avoiders equals a finite sum of products of binomial coefficients.", DescribeRole.Definition),
            Node("nonnesting-nonnestingdefs-isroyalroot", "Quadratic power-series identity", "IsRoyalRoot",
                "A power series satisfies the quadratic equation x times its square minus the square of one minus x times the series plus that square equals zero.", DescribeRole.Definition),
            Node("nonnesting-nonnestingdefs-claim1132", "The 1132 and 2213 identity", "claim1132",
                "The generating function for avoiding 1132 and 2213 satisfies the quadratic power-series identity.", DescribeRole.Definition),
            Node("nonnesting-nonnestingdefs-claim1233", "The 1233 and 1322 identity", "claim1233",
                "The generating function for avoiding 1233 and 1322 satisfies the same quadratic power-series identity.", DescribeRole.Definition),
            Node("nonnesting-nonnestingdefs-claimfour", "The four-pattern rational identity", "claimFour",
                "The generating function for avoiding 1231, 1312, 2231, and 3221, multiplied by (1 - 3x)(1 - x - x squared), equals 1 - 3x + 2x squared.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

