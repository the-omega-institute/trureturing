using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class SwapInvariantEventMassDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/"
            + "SwapInvariantEventMass.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Swap-connected causal orders induce identical event masses, finite event "
            + "profiles, and linear query values under every fixed exogenous law.",
        H("Swap-Invariant Event Masses"),
        Blocks(
            Paragraph(Text(
                "Pointwise equality of structural response profiles is transported through a finite exogenous weighted sum. Probability normalization is irrelevant to this pure invariance identity.")),
            Paragraph(Text(
                "The result applies simultaneously to a finite family of Boolean final-state events and to every rational linear objective assembled from their masses.")),
            Paragraph(Text(
                "This is the semantic-to-linear bridge needed to prove that causal-order LP data and query values do not depend on the selected compatible extension once swap connectivity is available.")),
            Describe.Lean(
                DescribeId.Create("event-mass-swap-invariance"),
                DeclarationHandle.Create(
                    Prefix + "eventMass_invariant_of_swap_chain"),
                H("Swap-connected orders assign equal mass to every event"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every summand agrees because the event readout agrees pointwise for the same exogenous state."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("event-profile-swap-invariance"),
                DeclarationHandle.Create(
                    Prefix + "eventMassProfile_invariant_of_swap_chain"),
                H("The complete finite event profile is extension invariant"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Function extensionality applies the scalar event-mass identity to every compiled event index."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("linear-event-query-swap-invariance"),
                DeclarationHandle.Create(
                    Prefix + "linearEventQuery_invariant_of_swap_chain"),
                H("Every linear query on the event profile is invariant"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equality of event-mass profiles immediately preserves all rational linear objectives used by the finite causal LP layer."))),
                DescribeRole.Theorem))));
}
