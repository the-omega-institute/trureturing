using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DottedStack;

internal sealed class ShiehYangYuTwelveDotWestDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotWest.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/yangshiehyu2025dotted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "West's stack map sorts distinct words exactly when they avoid 231, and peak runs preserve the entries of a word.",
        H("Stack Sorting and Peak-Run Structure"),
        Blocks(
            Node("syy-twelve-dot-west-criterion-theorem", "West's sorting criterion", "west_criterion",
                "For every word of pairwise distinct natural numbers, the output of West's "
                + "stack map is strictly increasing if and only if the word avoids the pattern "
                + "231. An occurrence of 231 consists of three entries in their original order "
                + "whose third entry is smaller than the first and whose first entry is smaller "
                + "than the second.", DescribeRole.Theorem),
            Node("syy-twelve-dot-peak-structure-theorem", "Structure of peak runs", "peak_structure",
                "For every word of natural numbers, concatenating its peak runs recovers the "
                + "word, and s12 produces a permutation of that word. Each peak run is nonempty "
                + "and has a leading entry at least as large as every entry in its remaining "
                + "body. For any two peak runs in their original order, every entry of the "
                + "earlier run is strictly smaller than the leading entry of the later run.",
                DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
