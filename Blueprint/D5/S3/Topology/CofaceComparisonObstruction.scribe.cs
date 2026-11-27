using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class CofaceComparisonObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Obstructions to choosing comparable cofaces",
        H("Obstructions to choosing comparable cofaces"),
        Blocks(Describe.Lean(
            DescribeId.Create("bounded-coface-obstruction"),
            DeclarationHandle.Create(
                "D5/S3/Topology/CofaceComparisonObstruction.exists_small_infeasible_family"),
            H("A failed coface extension has a small witness"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "Suppose the cofaces of a face s have at most d vertices and none is comparable by inclusion with every member of a finite family. " +
                "At most d plus one minus the size of s of those requirements already rule out an extension. " +
                "A requirement incomparable with the current face forces every extension to include their union. Each feasible enlargement raises the cardinality."))),
            DescribeRole.Theorem))));
}
