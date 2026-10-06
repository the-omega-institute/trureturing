using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TwoColorPartition;

internal sealed class AndrewsElBachraouiFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFour.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/andrews2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-color partition series D-prime at parameters 2 and 3 has negative coefficients exactly at degrees 10 and 22.",
        H("Andrews and El Bachraoui Conjecture Four"),
        Blocks(
            Node("andrews-el-bachraoui-four-result", "The two negative coefficients of D-prime", "result", "For every natural number n, the coefficient dCoeff 2 3 n is negative if and only if n is 10 or 22. Thus the two-color partition series D-prime with parameters 2 and 3 has precisely these two negative coefficients. A finite Heine transformation reduces the coefficients to triangular-pair counts and alternating odd divisor sums; their bounds give nonnegativity for large degrees, and exact evaluation treats the remaining degrees.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("andrews-el-bachraoui-d23-sign-pattern"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
