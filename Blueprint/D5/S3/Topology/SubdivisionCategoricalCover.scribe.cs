using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class SubdivisionCategoricalCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Categorical covers under finite-space subdivision",
        H("Categorical covers under finite-space subdivision"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("subdivision-map-fence"),
                DeclarationHandle.Create(
                    "D5/S3/Topology/SubdivisionCategoricalCover.subdivision_map_fence"),
                H("Subdivision preserves finite homotopies of order maps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text(
                    "Interpolate comparable maps by the cardinalities of principal lower sets. " +
                    "Along each interpolation step, the union of the two images of a chain remains a chain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("double-subdivision-two-cover"),
                DeclarationHandle.Create(
                    "D5/S3/Topology/SubdivisionCategoricalCover.hasCategoricalCover_double_subdivision"),
                H("Two categorical vertex subsets give two categorical opens after subdivision"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text(
                    "Intersect each chain meeting a selected set with that set, and then apply the subdivided contraction. " +
                    "The flags whose every chain meets one selected set form a lower set. " +
                    "The smallest chain of each flag supplies a vertex belonging to one of the two sets, so these lower sets cover."))),
                DescribeRole.Theorem))));
}
