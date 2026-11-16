using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricCycleLowPairsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric Cycle Low Pairs", H("Symmetric Cycle Low Pairs"),
        Blocks(
            Paragraph(Text("On an actual embedded high eight-cycle, girth excludes low pairs between distinct cycle points and forces two cycle partners of an outside high leaf to be antipodal. Tiny finite cycle-index checks provide actual short-path witnesses.")),
            Paragraph(Text("This module contributes to the live proof path of SymmetricSliceExclusion.result. Private helper declarations are proof organization and carry no independent novelty claim."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceLabels"))
        ]));
}
