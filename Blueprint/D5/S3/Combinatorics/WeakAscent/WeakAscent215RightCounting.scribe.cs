using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215RightCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two continuation counts and rational power series encode the second avoidance class.",
        H("Continuation Series for the Second Class"),
        Blocks(
            Node("weak-ascent-weakascent215rightcounting-continuationcounts", "The paired continuation recursion", "continuationCounts",
                "For every nonnegative budget b, define q_0(b) = p_0(b) = 1. For nonnegative d, let S_d(b) be the sum of p_d(i + 1) over integers i from zero through b minus one. Then q_(d+1)(b) = q_d(b + 1) + S_d(b), and p_(d+1)(b) = q_d(b) + p_d(b + 1) + S_d(b). The continuation counts are the ordered pair of these q and p values.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215rightcounting-qseries", "The q continuation series", "qSeries",
                "For a nonnegative budget b, the rational power series Q_b(x) has coefficient q_d(b) in degree d.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215rightcounting-pseries", "The p continuation series", "pSeries",
                "For a nonnegative budget b, the rational power series P_b(x) has coefficient p_d(b) in degree d.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215rightcounting-numerator", "The numerator series", "numerator",
                "For a rational power series T, the numerator series is T squared times the formal inverse of 1 minus x squared times T squared.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215rightcounting-ratio", "The ratio series", "ratio",
                "For a rational power series T, the ratio series is its numerator series multiplied by the formal inverse of T, with the inverse taken to be zero when T has zero constant coefficient.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215rightcounting-positivebase", "The positive-base series", "positiveBase",
                "For a rational power series T, the positive-base series is its numerator series multiplied by 1 + xT.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
