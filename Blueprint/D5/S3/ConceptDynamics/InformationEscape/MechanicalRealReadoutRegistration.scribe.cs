using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class MechanicalRealReadoutRegistrationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/MechanicalRealReadoutRegistration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real mechanical readouts retain their full parameter dependence in a finite observation slot.",
        H("MechanicalRealReadoutRegistration"),
        Blocks(
            Node("PrefixOutput", "A readout of weights, slope, phase, and finite horizon is a real number."),
            Node("CompletionOutput", "A completed real readout is paired with all its geometric finite prefixes."),
            Node("actualPrefix", "The finite component sums weighted mechanical letters at the given slope and phase."),
            Node("actualCompletion", "The paired components are the geometric series and its finite weighted prefix."),
            Node("localOrderClaim", "Local order preservation at every phase is equivalent to decreasing weights with a nonnegative terminal weight."),
            Node("isometricClaim", "The completed readout has uniform tails, integrability, exact finite and infinite L1 distances, and a mixed-error formula."),
            Node("uniformBoundClaim", "Geometric readouts lie within one minus the ratio of the slope, with phase-sensitive one-sided bounds."),
            Node("iteratedLimitClaim", "Finite horizons converge to the completion; flattening first sends each finite prefix to zero while the completion tends to the slope."),
            Node("regularityClaim", "Integer hits classify fixed-phase continuity and give a quantitative lower jump at each hit."),
            Node("localOrderArena", "One CUT slot retains the entire weighted-prefix function for the order law."),
            Node("isometricArena", "One CUT slot retains both real functions needed for the L1 completion law."),
            Node("uniformBoundArena", "The same paired observation supports the uniform slope bound."),
            Node("iteratedLimitArena", "The same paired observation supports the two limiting orders."),
            Node("regularityArena", "The completed-value component supports the continuity and jump law."),
            Node("localOrderRealization", "The slot is filled with actual finite mechanical-letter sums."),
            Node("completionRealization", "The slot is filled with the actual geometric readout and its finite prefixes."))));

    private static DocumentBlock.Describe Node(string declaration, string text) =>
        Describe.Lean(
            DescribeId.Create("mechanical-real-readout-" + declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Definition);
}
