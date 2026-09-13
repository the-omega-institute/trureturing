using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class InclusionRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact inclusion registration programs over finite supports.",
        H("InclusionRegistrationTemplates"),
        Blocks(
            Node("inclusionSignature", "Two independent ADMIT slots retain source and target membership.", DescribeRole.Definition),
            Node("inclusionRealization", "Each readout evaluates its supplied state-dependent predicate.", DescribeRole.Definition),
            Node("inclusionArena", "The fixed law requires target admission whenever source admission holds.", DescribeRole.Definition),
            Node("inclusionLegacy", "The finite union contains every possible counterexample to the complete original inclusion, including for an infinite ambient type.", DescribeRole.Theorem),
            Node("inclusion_sensitivity", "Changing either ADMIT slot alone changes the law while the other slot remains fixed.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/InclusionRegistrationTemplates." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
