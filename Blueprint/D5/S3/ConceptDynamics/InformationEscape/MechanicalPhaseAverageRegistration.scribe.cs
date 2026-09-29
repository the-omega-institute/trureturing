using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class MechanicalPhaseAverageRegistrationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The atomic phase average and volume are functions on the same admissible inputs.",
        H("MechanicalPhaseAverageRegistration"),
        Blocks(
            Node("phase-average-input", "PhaseAverageInput", "Admissible input",
                "An input contains a ratio strictly between zero and one and a measurable real set "
                + "contained in the unit interval."),
            Node("phase-average-integral", "phaseAverageIntegral", "Phase average",
                "The first function integrates the geometric atomic measure over half-open phases."),
            Node("phase-average-volume", "phaseAverageVolume", "Volume",
                "The second function assigns the volume of the same target set."),
            Node("phase-average-arena", "phaseAverageArena", "Readout comparison",
                "Two CUT roles compare the full functions on admissible inputs. The source object "
                + "domain is the type of real sets; finite readout states only select the roles."),
            Node("phase-average-realization", "phaseAverageRealization", "Selected readouts",
                "The selected realization reads the phase-average and volume functions."))));

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
