using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class ShellingColourObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Induced cycles obstruct mixed shelling restrictions",
        H("Induced cycles obstruct mixed shelling restrictions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mixed-shelling-excludes-monochromatic-induced-four-cycle"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/ShellingColourObstruction.false_of_monochromatic_four_cycle"),
                H("Monochromatic induced four-cycles and shelling restrictions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("In a shelling starting with a simplex, a monochromatic induced four-cycle would have to survive when the last facet is removed. A newly introduced cycle vertex would put both neighbours in the attaching simplex and create a diagonal. Once the vertices are already present, the mixing requirement forces the four edges into the preceding prefix as well. The cycle would therefore lie in the initial simplex, which contains its diagonals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mixed-shelling-obstruction-in-dimension-eight"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/ShellingColourObstruction.false_of_mixed_restrictions_sd_of_nine_vertices"),
                H("Obstruction after barycentric subdivision in dimension at least eight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("A simplex with nine vertices yields three independent triples in the face-comparability graph, with all edges across triples. Two triples have the same majority colour, giving a monochromatic induced four-cycle. Consequently every positive barycentric iterate of a complex of dimension at least eight has this obstruction to the mixed restriction-face criterion."))),
                DescribeRole.Theorem))));
}
