using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeCCPDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connected compatible partitions recover the actual geometric faces.",
        H("Faces and connected compatible partitions"),
        Blocks(
            Paragraph(Text("These recovery statements implement the classical correspondence cited as source Theorem 3.1, attributed there to Stanley. Their formal set/partition constructions are repository-derived.")),
            Describe.Lean(
                DescribeId.Create("crown-partition-face-tight-component-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCCP.crownPartitionFace_tightComponent_iff"),
                H("The constructed face recovers its partition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every connected compatible partition of the augmented crown vertices, two vertices are reachable in the tight graph of its constructed face exactly when they belong to the same partition block. Connectedness and quotient-order antisymmetry are explicit fields of the partition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("crown-partition-face-crown-face-partition"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCCP.crownPartitionFace_crownFacePartition"),
                H("Recovery of every exposed face"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every actual exposed face, forming its tight-component partition and then imposing the partition equalities recovers the same face. Together with the reverse recovery this gives the geometric correspondence used for counting. Endpoint separation characterizes nonempty faces."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytope"))
        ]));
}
