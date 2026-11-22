using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9FanoDeletionDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FanoDeletion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extending a tight Fano deletion",
        H("Seven Fano lines force at least seven link edges"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-fano-deletion-link-bound"),
                DeclarationHandle.Create(Module + ".q9_degree_ge_seven_of_fano_deletion"),
                H("A tight seven-point deletion forces degree at least seven"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take a family of triples on eight points that places at least two triples "
                        + "in every five-set. If deleting a point leaves exactly seven triples, "
                        + "at least seven original triples contain that point.")),
                    Paragraph(Text(
                        "The surviving triples form a Fano plane by the pair-incidence law. "
                        + "The complement of each line contains no surviving triple. Restoring the "
                        + "deleted point to that four-set therefore requires at least two link edges. "
                        + "Every pair belongs to exactly two line complements, since each of its "
                        + "points lies on three lines and their common line is unique. Counting "
                        + "incidences between link edges and line complements gives the bound."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SingletonFiveMask"))
        ]));
}
