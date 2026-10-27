using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums.GiniStationaryTest;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/grunwaldpales2024gini");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gini comparison and stationary normalization.",
        H("Gini means and the stationary criterion"), Blocks(
            Entry("giniMean", "The complete Gini mean",
                "For unequal parameters the existing Gini mean is used directly. For equal parameters the mean is the exponential of the power-weighted average of logarithms. On positive tuples both branches agree with the defining formulas."),
            Entry("chi", "The characteristic function",
                "The characteristic function is the divided difference of powers for distinct parameters, and the power times the logarithm for equal parameters."),
            Entry("chiDeriv", "Characteristic derivative",
                "The derivative is the real derivative of the characteristic function."),
            Entry("Gamma", "Comparison on an interval",
                "Gamma records the parameter pairs for which the first Gini mean is at most the second on every tuple from the interval."),
            Entry("stationaryTest", "The normalized stationary criterion",
                "For each positive tuple with first Gini mean one, a common multiplier is required in all characteristic derivative equations. The criterion asks that the second Gini mean be at least one at every such tuple."),
            Entry("claim", "Characterization by stationary tuples",
                "The claim quantifies over every n at least three and every nonempty positive interval whose quotient set has infimum zero. For every four real parameters, it asserts equivalence between comparison on the interval and the normalized stationary criterion."))));

    private static DocumentBlock Entry(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("gini-stationary-defs-" + name.ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/ArithSums/GiniStationaryTest/Defs." + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
