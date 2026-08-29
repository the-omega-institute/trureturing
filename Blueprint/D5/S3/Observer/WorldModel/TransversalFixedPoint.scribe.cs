using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WorldModel;

internal sealed class TransversalFixedPointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/WorldModel/TransversalFixedPoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coherent family of states across semiconjugate world models forms a transversal fixed point whenever one anchor state is fixed.",
        H("Transversal Fixed Point"),
        Blocks(
            Theorem(
                "transport-from-fixed-is-fixed",
                "WorldModelDiagram.transport_from_fixed_is_fixed",
                "Transport From Fixed Is Fixed",
                "A fixed anchor transports to a fixed state in every target world model.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "coherent-section-fixed-from-anchor",
                "WorldModelDiagram.coherent_section_fixed_from_anchor",
                "Coherent Section Fixed From Anchor",
                "A coherent section that is fixed at one anchor is fixed in every model.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "fixed-at-anchor-iff-fixed-at-target-of-injective",
                "WorldModelDiagram.fixed_at_anchor_iff_fixed_at_target_of_injective",
                "Fixed At Anchor iff Fixed At Target Of Injective",
                "For a coherent section, fixedness at any two anchors is equivalent when the bridge in one direction is injective.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);
}
