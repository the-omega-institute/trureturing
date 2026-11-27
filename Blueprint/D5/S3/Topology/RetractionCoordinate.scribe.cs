using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class RetractionCoordinateDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Result(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Topology/RetractionCoordinate." + declaration),
            H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Retractions of the coloured tetrahedral regions",
        H("Retractions of the coloured tetrahedral regions"),
        Blocks(
            Result("ordinary-retraction-height", "retractionHeight_of_rank_retraction",
                "Ordinary path coordinates of the two-cut retraction",
                "At each of three ordinary subdivisions, take the sum of the least and greatest " +
                "coordinates in the underlying face. For an actual retraction in the two-cut collar, " +
                "this coordinate equals the height computed from the corresponding tetrahedral row. " +
                "The calculation respects repeated images under the rank map."),
            Result("glued-main-retraction", "main_retraction_glued",
                "The main region admits a single contiguity chain",
                "A proper rank colouring supplies a compatible oriented interval chart on each old edge. " +
                "A main vertex supported on one old vertex keeps its endpoint value in every incident chart. " +
                "These endpoint agreements glue the relative interval interpolation from the two-cut " +
                "retraction to the map obtained by halving the chamber heights."),
            Result("refined-main-retraction", "main_retraction_glued_refined",
                "The main region factors through the finer edge charts",
                "The full integer heights give a simplicial map to the fourth subdivision. " +
                "Choosing a vertex of each face gives the comparison to the third subdivision. " +
                "The relative contiguity comparison fixes the old endpoints."),
            Result("opposite-edge-for-extra-components", "extra_retraction_in_subdivided_edge",
                "Each extra component retracts into one subdivided edge",
                "A proper rank colouring is injective on each old face. The two opposite ranks " +
                "present in every extra carrier select a single edge throughout a connected component. " +
                "The opposite two-cut retraction lands in the third subdivision of that edge."))));
}
