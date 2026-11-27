using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class PathContiguityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative contiguity of maps to an interval",
        H("Relative contiguity of maps to an interval"),
        Blocks(Describe.Lean(
            DescribeId.Create("relative-interval-contiguity"),
            DeclarationHandle.Create(
                "D5/S3/Topology/PathContiguity.relative_complex_contiguity"),
            H("Maps to a subdivided interval are contiguous relative to shared values"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "Take the pointwise minimum of two interval-valued maps. " +
                "From either map, lower a vertex whose current label is maximal among those still above the minimum. " +
                "No neighbour has a higher label, so one decrease preserves contiguity on every incident simplex. " +
                "The sum of labels decreases and vertices where the maps agree keep their value."))),
            DescribeRole.Theorem))));
}
