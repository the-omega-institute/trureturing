using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class MechanicalSlopeCalibrationRegistrationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/MechanicalSlopeCalibrationRegistration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local slope and joint phase laws retain their actual real-parameter observations.",
        H("MechanicalSlopeCalibrationRegistration"),
        Blocks(
            Node("slope-readout", "slopeReadout", "Slope disagreement",
                "This function returns the phases on which two finite mechanical words disagree."),
            Node("phase-readout", "phaseReadout", "Joint mismatch volume",
                "This function measures the phases on which simultaneous slope and phase changes "
                + "alter a finite mechanical word."),
            Node("slope-arena", "slopeArena", "Local slope law",
                "One CUT slot retains the parameterized disagreement sets, including their exact "
                + "measure and the signed changes in the underlying letters."),
            Node("phase-arena", "phaseArena", "Calibration law",
                "One CUT slot retains mismatch volume under every admissible displacement and "
                + "compares the centered displacement with all local alternatives."),
            Node("slope-realization", "slopeRealization", "Selected slope readout",
                "The selected realization reads actual slope disagreement sets."),
            Node("phase-realization", "phaseRealization", "Selected phase readout",
                "The selected realization reads actual joint mismatch volumes."))));

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
