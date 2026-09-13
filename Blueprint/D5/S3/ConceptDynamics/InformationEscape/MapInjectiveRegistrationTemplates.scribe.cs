using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class MapInjectiveRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact injectivity registration programs over finite object states.",
        H("MapInjectiveRegistrationTemplates"),
        Blocks(
            Node("mapInjectiveSignature", "One typed CUT slot retains the complete map as its readout.", DescribeRole.Definition),
            Node("mapInjectiveRealization", "The supplied map remains unchanged; its values are not replaced by truth labels.", DescribeRole.Definition),
            Node("mapInjectiveArena", "The law is injectivity of the readout on the supplied finite arena, with no arbitrary law parameter.", DescribeRole.Definition),
            Node("mapInjectiveLegacy", "The complete Function.Injective statement is definitionally the generated law.", DescribeRole.Theorem),
            Node("mapInjective_sensitivity", "An injective readout and two distinct states witness sensitivity of the only CUT slot: replacing the map by a constant falsifies the law.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrationTemplates." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
