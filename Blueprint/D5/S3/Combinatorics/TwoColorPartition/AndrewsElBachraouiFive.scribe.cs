using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TwoColorPartition;

internal sealed class AndrewsElBachraouiFiveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFive.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/andrews2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Andrews and El Bachraoui Conjecture Five.",
        H("Andrews and El Bachraoui Conjecture Five"),
        Blocks(
            Node("andrews-el-bachraoui-five-result", "Complete eventual D-prime coefficient positivity", "result", "For all natural k and m, if one is at most m and m is less than k, there exists a natural threshold N such that for every natural n at least N, the original dCoeff k m n is nonnegative. The threshold may depend on k and m. Both parities and both endpoint families are included. The exact source transformation supplies a fixed rational series minus a Gauss convolution series. Arithmetic-progression summation proves the rational coefficient limit on every n and propagates a sharp upper sequence for the product coefficients. Finite subset integration computes the rational leading constant, and the strict Wallis gap makes the difference eventually positive. No radial-to-coefficient inference or unproved analytic premise is used.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("andrews-el-bachraoui-dprime-eventual-positivity"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
