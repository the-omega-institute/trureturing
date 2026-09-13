using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class CardinalityRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact cardinality registration programs over finite object states.",
        H("CardinalityRegistrations"),
        Blocks(
            Node("cognitiveArena", "The arena retains CognitiveState as the finite source state and 6 as the target.", DescribeRole.Definition),
            Node("cognitiveRealization", "Every source state is admitted through the single Boolean slot.", DescribeRole.Definition),
            Node("cognitive_bridge", "The bridge retains Fintype.card CognitiveState = 6 without substituting the frozen theorem into the statement.", DescribeRole.Theorem),
            Node("cognitive_lawSensitive", "The existing frozen cardinality theorem satisfies the all-state law; empty admission falsifies it.", DescribeRole.Theorem),
            Node("cognitive_slotSensitive", "The generic sensitivity theorem supplies the checked support of the ADMIT slot.", DescribeRole.Theorem),
            Node("sourceGroupsArena", "The arena retains PhysicalSourceGroup as the finite source state and 6 as the target.", DescribeRole.Definition),
            Node("sourceGroupsRealization", "Every source state is admitted through the single Boolean slot.", DescribeRole.Definition),
            Node("sourceGroups_bridge", "The bridge retains Fintype.card PhysicalSourceGroup = 6 without substituting the frozen theorem into the statement.", DescribeRole.Theorem),
            Node("sourceGroups_lawSensitive", "The existing frozen cardinality theorem satisfies the all-state law; empty admission falsifies it.", DescribeRole.Theorem),
            Node("sourceGroups_slotSensitive", "The generic sensitivity theorem supplies the checked support of the ADMIT slot.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
