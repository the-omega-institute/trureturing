using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeDimensionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The number of partition blocks determines the actual affine dimension.",
        H("Affine dimensions of crown faces"),
        Blocks(
            Paragraph(Text("This is the dimension clause of the classical face/partition correspondence cited in source Theorem 3.1.")),
            Describe.Lean(
                DescribeId.Create("crown-partition-face-finrank-direction"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeDimension.crownPartitionFace_finrank_direction"),
                H("Dimension equals the number of blocks minus two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For any connected compatible partition whose bottom and top blocks differ, the real dimension of the direction of the affine span of its face equals the cardinality of its quotient minus two. The two endpoint blocks have fixed coordinate values; the other block coordinates supply the independent directions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("crown-exposed-face-finrank-direction"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeDimension.crownExposedFace_finrank_direction"),
                H("Dimension of any nonempty exposed face"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every nonempty actual exposed face, its real affine dimension equals the number of blocks of its tight-component partition minus two. This transports the constructed-face dimension theorem through geometric face recovery."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCCP"))
        ]));
}
