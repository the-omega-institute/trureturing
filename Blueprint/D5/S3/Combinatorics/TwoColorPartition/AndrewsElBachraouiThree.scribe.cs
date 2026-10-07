using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TwoColorPartition;

internal sealed class AndrewsElBachraouiThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiThree.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/andrews2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-color partition series D-prime at parameters 2 and 2 has nonnegative coefficients.",
        H("Andrews and El Bachraoui Conjecture Three"),
        Blocks(
            Node("andrews-el-bachraoui-three-result", "Positivity of D-prime", "result", "For every natural number n, the coefficient dCoeff 2 2 n is nonnegative. Thus the two-color partition series D-prime with parameters 2 and 2 has no negative coefficient.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("andrews-el-bachraoui-d22-positivity"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
