using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class CardinalityRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact cardinality registration programs over finite object states.",
        H("CardinalityRegistrationTemplates"),
        Blocks(
            Node("cardinalitySignature", "One Boolean ADMIT readout records which original states contribute to the count.", DescribeRole.Definition),
            Node("cardinalityRealization", "The supplied Boolean function remains the admission readout.", DescribeRole.Definition),
            Node("cardinalityArena", "The fixed target is compared with the cardinality of the states admitted by the realization.", DescribeRole.Definition),
            Node("cardinalityLegacy", "Admitting every state recovers the original Fintype.card equation by normalizing only the constant-true filter.", DescribeRole.Theorem),
            Node("cardinality_sensitivity", "All-state and empty admission witness the single slot for a nonzero target equal to the source cardinality.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrationTemplates." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
