using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class MechanicalReadoutSourcesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/MechanicalReadoutSources.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mechanical observations retain their real parameters, finite words, countable atoms, and phase averages.",
        H("Mechanical Readout Sources"),
        Blocks(
            Node("slopeReadout", "The set contains precisely the unit phases where two finite lower mechanical words differ."),
            Node("phaseReadout", "The volume measures word disagreement under simultaneous slope and phase changes."),
            Node("actualPrefix", "An arbitrary real weight sequence sums the observed mechanical letters to a finite horizon."),
            Node("actualCompletion", "The geometric infinite readout is paired with all its finite weighted prefixes."),
            Node("seriesReadout", "The floor series, its coefficient mass, and the threshold-counting series share the same parameters."),
            Node("geometricAtomicMeasure", "Each numbered threshold contributes its geometric weight as a Dirac mass."),
            Node("massReadout", "For admissible ratio and phase, the readout records total mass and mass on the positive unit interval."),
            Node("phaseAverageIntegral", "The phase average integrates the atomic measure of a measurable target over the unit phase interval."))));

    private static DocumentBlock.Describe Node(string declaration, string text) =>
        Describe.Lean(
            DescribeId.Create("mechanical-source-" + declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Definition);
}
