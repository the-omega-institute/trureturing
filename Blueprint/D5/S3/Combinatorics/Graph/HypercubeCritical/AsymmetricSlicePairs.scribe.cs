using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class AsymmetricSlicePairsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual low-pair classification.", H("Actual low-pair classification"),
        Blocks(Paragraph(Text(
            "Short-path witnesses exclude pairs outside fifteen possibilities for the eleven right labels. Endpoint coverage forces four pairs. Actual degree and girth supply one partner for every high right vertex and two distinct partners for each stub; these force the final three pairs. Indexed labels retain all actual vertex, degree, incidence and neighbor facts. The generic graph checker has arbitrary finite vertex types and graph inputs, with closed kernel checks for the finite label witnesses. Its consumer is AsymmetricSliceExclusion.result on the actual induced-slice claim; every finite helper is used in that proof. These private helpers do not assume a pairing certificate or an induced embedding."))),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceLabels"))]));
}
