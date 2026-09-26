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
                "Both coordinates equal one on admissible parameters; elsewhere the target equals the measured readout."),
            Node("mass-output", "MassOutput", "Mass family",
                "Each readout retains its value on every admissible mass input."),
            Node("distribution-input", "DistributionInput", "Distribution parameters",
                "The threshold lies in the closed unit interval and the phase in the half-open unit interval."),
            Node("distribution-readout", "distributionReadout", "Distribution readout",
                "The geometric atomic measure is evaluated on the interval below the threshold."),
            Node("distribution-target", "distributionTarget", "Distribution target",
                "On admissible parameters the target is the completed mechanical readout; elsewhere it equals the measured distribution."),
            Node("distribution-output", "DistributionOutput", "Distribution family",
                "The readout is a function on all admissible distribution parameters."),
            Node("hit-input", "HitInput", "Singleton parameters",
                "The phase belongs to the half-open unit interval and the threshold is interior."),
            Node("hit-readout", "hitReadout", "Singleton mass",
                "The atomic measure is evaluated at the singleton threshold."),
            Node("hit-target", "hitTarget", "Integer-hit series",
                "On admissible parameters each integer-hit time contributes its coefficient; elsewhere the target equals singleton mass."),
            Node("hit-output", "HitOutput", "Singleton family",
                "The singleton law retains all admissible ratios, phases, and thresholds."),
            Node("support-input", "SupportInput", "Support parameters",
                "The ratio is strictly between zero and one and the phase belongs to the half-open unit interval."),
            Node("support-readout", "supportReadout", "Measured support",
                "The readout is the topological support of the geometric atomic measure."),
            Node("support-target", "supportTarget", "Support target",
                "The target is the closed unit interval on admissible parameters and the measured support elsewhere."),
            Node("support-output", "SupportOutput", "Support family",
                "The support comparison retains every admissible ratio and phase."),
            Node("mass-arena", "massArena", "Mass comparison",
                "One CUT role reads the complete mass function; the law equates it with the target on every parameter."),
            Node("distribution-arena", "distributionArena", "Distribution comparison",
                "One CUT role reads the atomic distribution function; the law equates it with the completed mechanical readout."),
            Node("hit-arena", "hitArena", "Singleton comparison",
                "One CUT role reads singleton mass; the law equates it with the integer-hit series."),
            Node("support-arena", "supportArena", "Support comparison",
                "One CUT role reads the support function; the law equates it with the closed-interval target."),
            Node("mass-realization", "massRealization", "Mass realization",
                "The selected readout is the measured mass pair at each ratio and phase."),
            Node("distribution-realization", "distributionRealization", "Distribution realization",
                "The selected readout is the atomic distribution at each ratio, threshold, and phase."),
            Node("hit-realization", "hitRealization", "Singleton realization",
                "The selected readout is singleton mass at each ratio, phase, and threshold."),
            Node("support-realization", "supportRealization", "Support realization",
                "The selected readout is measured support at each ratio and phase."),
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
