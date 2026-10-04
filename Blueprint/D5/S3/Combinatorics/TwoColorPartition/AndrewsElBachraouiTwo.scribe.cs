using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TwoColorPartition;

internal sealed class AndrewsElBachraouiTwoDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiTwo.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/andrews2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-color partition series C-prime at parameters 2 and 4 has nonnegative coefficients.",
        H("Andrews and El Bachraoui Conjecture Two"),
        Blocks(
            Node("andrews-el-bachraoui-two-result", "Positivity of C-prime", "result", "For every natural number n, the coefficient cCoeff 2 4 n is nonnegative. Thus the two-color partition series C-prime with parameters 2 and 4 has no negative coefficient. A finite Heine transformation and partial fractions express the coefficients in terms of divisor counts, a periodic term and weighted alternating sums. Character bounds give nonnegativity for large degrees, and exact evaluation treats the remaining degrees.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
