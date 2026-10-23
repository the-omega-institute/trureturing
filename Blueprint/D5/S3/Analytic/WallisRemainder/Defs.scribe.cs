using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.WallisRemainder;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/mahmoudmortici2026wallisratio");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Wallis gamma ratio and three normalized remainder functions.",
        H("Wallis remainder functions"), Blocks(
            Entry("wallis-ratio", "wallisB", "The gamma ratio",
                "For real x, B(x) is the square root of x times Gamma(x+1/2), divided by Gamma(x+1)."),
            Entry("wallis-mu", "mu", "The reciprocal remainder",
                "For real x, mu(x) is minus x squared minus the reciprocal of the whole expression 24+(3/x)/log B(x)."),
            Entry("wallis-theta", "theta", "The first normalized difference",
                "For real x, theta(x) is (23040/31) times x to the fifth power times the sum of 3x/(24x squared+1) and log B(x)."),
            Entry("wallis-chi", "chi", "The second normalized difference",
                "For real x, chi(x) is (358400/257) times x to the seventh power times the sum of (120x squared+31)/(96x(10x squared+3)) and log B(x)."),
            Entry("wallis-claim", "claim", "The monotonicity assertion",
                "On the positive real ray, log B(x) and the inner reciprocal denominator of mu(x) are nonzero; mu and chi are strictly increasing and theta is strictly decreasing."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/WallisRemainder/Defs." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
