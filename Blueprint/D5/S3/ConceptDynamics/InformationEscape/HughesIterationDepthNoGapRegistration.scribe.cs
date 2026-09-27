using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class HughesIterationDepthNoGapRegistrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite two-origin arena records the no-gap theorem and a falsifying shifted readout.",
        H("HughesIterationDepthNoGapRegistration"),
        Blocks(
            Node("depthOriginRealization", "The identity readout preserves the published zero-based depth origin.", DescribeRole.Definition),
            Node("depthNoGapArena", "The arena law requires downward closure of the arbitrary-language iteration-depth spectrum at the read origin.", DescribeRole.Definition))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/HughesIterationDepthNoGapRegistration." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
