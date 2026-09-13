using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class IffRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boolean predicate registrations over finite object states.",
        H("IffRegistrationTemplates"),
        Blocks(
            Node("iffSignature", "Two Boolean CUT readouts retain the two predicates in an iff statement.", DescribeRole.Definition),
            Node("iffRealization", "The supplied predicates are converted to Boolean readouts without changing their expressions.", DescribeRole.Definition),
            Node("iffArena", "The law equates the two Boolean readouts at every state of the supplied finite arena.", DescribeRole.Definition),
            Node("iffLegacy", "The universally quantified iff statement is definitionally the generated pointwise law.", DescribeRole.Theorem),
            Node("iff_sensitivity", "An inhabited state and distinct Boolean values witness sensitivity of each readout slot.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
