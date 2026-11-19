using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class NineteenPointSliceIncidenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Private leaf-incidence arguments for the nineteen-vertex equality tree.",
        H("Forced incidences between the two leaf sets"),
        Blocks(
            Paragraph(Text(
                "All declarations are private helpers consumed by the matching obstruction "
                    + "and the nineteen-point reconstruction. The nineteen labels are the "
                    + "actual injective equality-tree labels from NineteenPointSliceTree. "
                    + "Internal neighbor sets are exhausted. Girth at least eight excludes "
                    + "additional same-side edges, common neighbors of the two distinguished "
                    + "high leaves, and a high leaf meeting two leaves of one opposite parent.")),
            Paragraph(Text(
                "The actual degree sum is forty-eight. Comparing the remaining degrees on "
                    + "both four-leaf sides forces the two leaves of the selected center to "
                    + "be low and precisely two opposite leaves to be high. The bound on "
                    + "high-neighbor counts across a high-high edge puts those high leaves "
                    + "under distinct parents, meeting distinct distinguished high leaves. "
                    + "Short-cycle exclusions and the actual neighbor counts force the "
                    + "remaining leaf incidences.")),
            Paragraph(Text(
                "The small Boolean leaf-choice helper selects an ordering of the four "
                    + "opposite leaves and the two center leaves. Its consumer supplies all "
                    + "actual graph constraints. It normalizes these labels for the cubical "
                    + "matching consumer; it enumerates neither graphs nor cube supports and "
                    + "does not provide a separate classification premise."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSliceTree"))
        ]));
}
