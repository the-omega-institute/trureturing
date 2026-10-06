using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SixCellPositiveMarginObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Infinite/SixCellPositiveMarginObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connected scalar instruments and the six-cell positive-margin obstruction.",
        H("Connected Instruments and Positive Margins"),
        Blocks(
            Node("cell", "Actual cells",
                "The cell of color i consists of scalars x in X=[-1,1+t] with Q(x)=i. "
                + "The function outside X has no effect on the instrument."),
            Node("connectedInstrument", "Connected instruments",
                "Each color fibre is a nonempty connected subset of the real line. "
                + "Singleton cells and every endpoint assignment are allowed; colors need not be ordered."),
            Node("closedGridPure", "Closed grid purity",
                "For every pair of closed cell coordinates, all legal branch points in that rectangle "
                + "have the same window label. The legal tail interval is [-1,1+t] for three, null and two, "
                + "and [-1,t] for five and twenty-five.")
        )));

    private static DocumentBlock Node(string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create("six-cell-margin-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
