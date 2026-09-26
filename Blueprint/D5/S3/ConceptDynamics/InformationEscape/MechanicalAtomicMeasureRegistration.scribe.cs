using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class MechanicalAtomicMeasureRegistrationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The atomic measure is compared with its mass, distribution, hit, and support targets on complete admissible parameter families.",
        H("MechanicalAtomicMeasureRegistration"),
        Blocks(
            Node("mass-input", "MassInput", "Mass parameters",
                "The ratio is nonnegative and below one, and the phase belongs to the half-open unit interval."),
            Node("mass-readout", "massReadout", "Mass readout",
                "The first coordinate is total mass and the second is mass on the positive unit interval."),
            Node("mass-target", "massTarget", "Mass target",
                "Both mass coordinates equal one."),
            Node("mass-output", "MassOutput", "Mass family",
                "Each readout retains its value on every admissible mass input."),
            Node("distribution-input", "DistributionInput", "Distribution parameters",
                "The threshold lies in the closed unit interval and the phase in the half-open unit interval."),
            Node("distribution-readout", "distributionReadout", "Distribution readout",
                "The geometric atomic measure is evaluated on the interval below the threshold."),
            Node("distribution-target", "distributionTarget", "Distribution target",
                "The target is the completed mechanical readout at the same ratio, threshold, and phase."),
            Node("distribution-output", "DistributionOutput", "Distribution family",
                "The readout is a function on all admissible distribution parameters."),
            Node("hit-input", "HitInput", "Singleton parameters",
                "The phase belongs to the half-open unit interval and the threshold is interior."),
            Node("hit-readout", "hitReadout", "Singleton mass",
                "The atomic measure is evaluated at the singleton threshold."),
            Node("hit-target", "hitTarget", "Integer-hit series",
                "Each time contributes its coefficient when its translated threshold is an integer."),
            Node("hit-output", "HitOutput", "Singleton family",
                "The singleton law retains all admissible ratios, phases, and thresholds."),
            Node("support-input", "SupportInput", "Support parameters",
                "The ratio is strictly between zero and one and the phase belongs to the half-open unit interval."),
            Node("support-readout", "supportReadout", "Measured support",
                "The readout is the topological support of the geometric atomic measure."),
            Node("support-target", "supportTarget", "Support target",
                "The target is the closed unit interval."),
            Node("support-output", "SupportOutput", "Support family",
                "The support comparison retains every admissible ratio and phase."),
            Node("mass-arena", "massArena", "Mass comparison",
                "Two CUT roles compare complete functions of admissible mass parameters."),
            Node("distribution-arena", "distributionArena", "Distribution comparison",
                "Two CUT roles compare the full distribution and mechanical readout functions."),
            Node("hit-arena", "hitArena", "Singleton comparison",
                "Two CUT roles compare singleton mass and the full integer-hit series."),
            Node("support-arena", "supportArena", "Support comparison",
                "Two CUT roles compare the support functions."),
            Node("mass-realization", "massRealization", "Mass realization",
                "The selected readouts are the measured mass pair and the unit target pair."),
            Node("distribution-realization", "distributionRealization", "Distribution realization",
                "The selected readouts are the atomic distribution and completed mechanical readout."),
            Node("hit-realization", "hitRealization", "Singleton realization",
                "The selected readouts are singleton mass and the integer-hit series."),
            Node("support-realization", "supportRealization", "Support realization",
                "The selected readouts are measured support and the closed unit interval."),
            Node("jump-output", "JumpOutput", "Complete readout",
                "The output records the completed mechanical readout at every ratio, slope, and phase."),
            Node("jump-readout", "jumpReadout", "Selected readout",
                "The selected function is the completed mechanical readout."),
            Node("left-jump-arena", "leftJumpArena", "Left jump law",
                "The CUT function has a left limit whose difference from its value is the integer-hit series."),
            Node("rational-jump-arena", "rationalJumpArena", "Rational jump law",
                "At reduced rational slopes and zero phase, the CUT function has the stated geometric jump."),
            Node("jump-realization", "jumpRealization", "Readout realization",
                "The realization uses the same completed mechanical readout in both jump laws."))));

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
