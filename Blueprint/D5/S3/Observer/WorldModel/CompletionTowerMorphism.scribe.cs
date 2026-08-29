using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WorldModel;

internal sealed class CompletionTowerMorphismDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/WorldModel/CompletionTowerMorphism.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Natural wormholes transport fixed threads between completion towers.",
        H("Completion Tower Morphism"),
        Blocks(
            Theorem(
                "map-thread-coherent",
                "TowerMorphism.map_thread_coherent",
                "Map Thread Coherent",
                "Naturality transports coherent threads.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "map-thread-fixed",
                "TowerMorphism.map_thread_fixed",
                "Map Thread Fixed",
                "Levelwise semiconjugacy transports fixed threads.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "map-truth-thread",
                "TowerMorphism.map_truth_thread",
                "Map Truth Thread",
                "Every tower morphism transports truth threads.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "map-thread-compose",
                "TowerMorphism.mapThread_compose",
                "Map Thread Compose",
                "Coordinatewise transport respects composition.",
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
