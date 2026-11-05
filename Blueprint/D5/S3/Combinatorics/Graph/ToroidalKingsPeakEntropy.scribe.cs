using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ToroidalKingsPeakEntropyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/ToroidalKingsPeakEntropy.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/kotesovec2026a394697");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Toroidal king modal coefficients and the literal square-tiling growth constant.",
        H("The all-integer toroidal king peak-entropy limit"),
        Blocks(
            Paragraph(Text("The source is the conjecture in OEIS A394697 revision 24: a(n)^(1/n^2) tends to A247413. A247413 revision 41 identifies that constant as the limit of A063443(m)^(1/m^2), and A063443 revision 104 counts tilings by unit and two-by-two squares, equivalently free king boards of side m-1. The common OEIS data revision is 77073cc8105b8042be07ec0d885da5ea5960ff3c. The graph, full coefficient range, literal constant and all-integer quantifiers are retained.")),
            Node("square-area-root", "rootGrowth", "Square-area root", "Cast a(n) to a real number and raise it to the reciprocal of n squared. This is the real exponent 1/n squared in the published question.", DescribeRole.Definition),
            Node("literal-constant", "a247413", "The source constant", "a247413 is limUnder atTop of rootGrowth(a063443). It is defined from the square-tiling sequence independently of toroidal counts. The proof establishes convergence of this exact sequence before identifying its limit.", DescribeRole.Definition),
            Node("all-integer-limit", "result", "The complete convergence statement", "For every positive real epsilon there is a natural N at least three such that, for every natural n at least N, the absolute difference between peak(n)^(1/n squared) and a247413 is less than epsilon. Empty seams give freeCount(n-1)<=torusCount(n)<=freeCount(n), while torusCount(n)<=(n squared plus one)*peak(n) and peak(n)<=torusCount(n). The shifted free logarithmic limit and the vanishing polynomial logarithmic loss squeeze log(peak(n))/n squared to the same value. Exponentiation and uniqueness of the separately defined tiling limit yield the stated literal constant. Both periodic coordinates, odd n, empty configurations and every cardinality from zero through n squared remain in scope.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a394697-toroidal-king-peak-entropy"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string name, string title, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Owner + name), H(title), StatementSource.FromLean(),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolution);
}
