using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9SharedContactAxisOrbitsDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9SharedContactAxisOrbits.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Axis permutations reduce shared nine-cube contact triples to three cases.",
        H("Coordinate orbits of a shared contact"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-axis-permutation"),
                DeclarationHandle.Create(Owner + "exists_axis_permutation"),
                H("Three cases classified by overlap size"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three differing axes lie outside the two occupied triples. On the six agreeing "
                    + "axes, classify each axis by membership in the two occupied triples. The four fiber "
                    + "sizes depend only on the size of the common part. Equivalences between corresponding "
                    + "fibers combine to a permutation taking all five classes to their canonical "
                    + "coordinates."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "CubicContactDistance"))
        ]));
}
