using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SixBoundarySideIncidenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Private helpers consumed by the actual six-boundary side-gap theorem.",
        H("Actual cube edge labels and antipodal middles"),
        Blocks(Paragraph(Text("All helpers are private and consumed. The constructive eight-vertex cube table selects twelve distinct original left labels. Their actual high-neighbor incidences equal the explicit cube edge endpoint pairs. Since there are twelve left vertices these labels exhaust the left side. A degree-two middle pairs each edge only with its antipodal parallel edge: actual girth separation is combined with the already derived cube neighbor table. Finite endpoint-index checks verify this forced pairing on that cube, rather than classifying arbitrary graphs."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideLabeling"))
        ]));
}
