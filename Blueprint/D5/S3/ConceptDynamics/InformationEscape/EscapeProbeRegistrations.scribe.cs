using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class EscapeProbeRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trigger probe: one new public theorem carrying a complete four-slot escape registration.",
        H("EscapeProbeRegistrations"),
        Blocks(
            Node("probe_four_slot_true", "The identity readout over Bool never changes a bit; this is the probe theorem.", DescribeRole.Theorem),
            Node("probeArena", "One CUT slot reads a Boolean state and the law fixes the readout at false.", DescribeRole.Definition),
            Node("probe_bridge", "The statement is equivalent to the arena law of the identity readout.", DescribeRole.Theorem),
            Node("probe_emptyProof", "The identity kernel separates both states, so the closure leaves no residual.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/EscapeProbeRegistrations." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
