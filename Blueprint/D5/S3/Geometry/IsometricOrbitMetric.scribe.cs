using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class IsometricOrbitMetricDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/IsometricOrbitMetric.";

    private static readonly LibraryNoteRef ClassicalSource =
        LibraryNoteRef.Create("D5/L/Geometry/kapovich2023properactions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible metrics and compact closed balls for quotients of isometric representations.",
        H("Isometric orbit metrics"),
        Blocks(
            Paragraph(Text(
                "For a group represented by isometries of a metric space, the distance "
                    + "between two orbits is the infimum of the distances to translates "
                    + "of one representative. Proper discontinuity makes this a metric "
                    + "with the existing quotient topology. If the original metric space "
                    + "is proper, the quotient is proper as well. Neither freeness nor "
                    + "compactness of the quotient is assumed. These statements do not "
                    + "establish a smooth hyperbolic structure, finite volume or rigidity.")),
            Describe.Lean(
                DescribeId.Create("orbit-distance"),
                DeclarationHandle.Create(Prefix + "orbitDistance"),
                H("Distance between orbits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(ClassicalSource),
                Blocks(Paragraph(Text(
                    "Changing either representative reindexes the group orbit. "
                        + "Isometry invariance of distance to a set then gives a "
                        + "well-defined real-valued function on orbit classes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("compatible-orbit-metric"),
                DeclarationHandle.Create(Prefix + "orbitMetricSpace"),
                H("Metric with the quotient topology"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(ClassicalSource),
                Blocks(Paragraph(Text(
                    "Inverting a group element gives symmetry; composing two group "
                        + "elements and taking infima gives the triangle inequality. "
                        + "Open quotient sets contain orbit-distance balls, and their "
                        + "preimages contain ordinary metric balls. The Hausdorff "
                        + "orbit quotient of a properly discontinuous action has closed "
                        + "orbit fibers, so zero distance identifies the same orbit."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("proper-orbit-quotient"),
                DeclarationHandle.Create(Prefix + "orbitProperSpace"),
                H("Compact closed balls in the quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(ClassicalSource),
                Blocks(Paragraph(Text(
                    "For a proper ambient space, distance to a nonempty closed orbit "
                        + "is attained. Consequently each quotient closed ball is "
                        + "exactly the projection of the closed ball about any chosen "
                        + "representative. The continuous projection maps that compact "
                        + "ball to a compact quotient ball. Kapovich, Lemma 21(2), "
                        + "gives this classical properness argument; the Library note "
                        + "records its hypotheses and the representation convention."))),
                DescribeRole.Definition)),
        []));
}
