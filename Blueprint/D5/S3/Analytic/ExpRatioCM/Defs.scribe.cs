using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ExpRatioCM;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/weiguo2014completemonotonicity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed derivatives of two exponential reciprocals and their consecutive ratios.",
        H("Exponential derivative ratios"), Blocks(
            Entry("exp-ratio-f", "F", "The first signed derivative family",
                "F(i,t) is (-1)^i times the i-th derivative of 1/(exp(t)-1)."),
            Entry("exp-ratio-g", "G", "The second signed derivative family",
                "G(i,t) is (-1)^i times the i-th derivative of 1/(1-exp(-t))."),
            Entry("exp-ratio-ratiof", "ratioF", "The first consecutive ratio",
                "The ratio is F(i+1,t)/F(i,t)."),
            Entry("exp-ratio-ratiog", "ratioG", "The second consecutive ratio",
                "The ratio is G(i+1,t)/G(i,t)."),
            Entry("exp-ratio-cm", "CompletelyMonotoneOn", "Complete monotonicity",
                "A real function is smooth on the positive half-line and every signed iterated derivative (-1)^k h^(k)(t) is nonnegative there."),
            Entry("exp-ratio-claim", "claim", "The assertion for all indices",
                "For every natural index both consecutive ratios are completely monotone on the positive half-line."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Defs." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
