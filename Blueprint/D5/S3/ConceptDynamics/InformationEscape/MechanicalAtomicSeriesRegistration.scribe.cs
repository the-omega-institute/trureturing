using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class MechanicalAtomicSeriesRegistrationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicSeriesRegistration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The atomic series is observed as three functions of its real parameters.",
        H("MechanicalAtomicSeriesRegistration"),
        Blocks(
            Node("series-readout", "seriesReadout", "Atomic series readout",
                "The readout returns the floor expansion, its total coefficient mass, and the "
                + "threshold-atom expansion as functions of the ratio, slope, and phase."),
            Node("series-arena", "seriesArena", "Series law",
                "One CUT slot retains those full functions. The law compares both expansions "
                + "with the geometric mechanical readout and fixes the coefficient mass at one."),
            Node("series-realization", "seriesRealization", "Selected series",
                "The selected realization reads the actual atomic series functions."))));

    private static DocumentBlock.Describe Node(
        string id, string declaration, string title, string text) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Definition);
}
