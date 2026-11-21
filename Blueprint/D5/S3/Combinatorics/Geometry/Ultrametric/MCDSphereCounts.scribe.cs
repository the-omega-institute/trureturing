using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry.Ultrametric;

internal sealed class MCDSphereCountsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/Ultrametric/MCDSphereCounts.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/mazhang2026centraledges");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite ultrametric space with center {0 = c_0 < ⋯ < c_h} has 2^(i-1) points at distance "
            + "c_i from every point, for 1 ≤ i ≤ h, exactly when it has 2^h points.",
        H("Sphere counts characterize minimum-order ultrametric spaces"),
        Blocks(
            Describe.Lean(DescribeId.Create("mcd-sphere-counts-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The sphere-count characterization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let X be a finite ultrametric space whose center, the set of t ≥ 0 such "
                        + "that every point has a point at distance t, is exactly "
                        + "{c_0 < c_1 < ⋯ < c_h}, so that c_0 = 0 since 0 is always central. Then every "
                        + "point has 2^(i-1) points at "
                        + "distance c_i for all 1 ≤ i ≤ h if and only if |X| = 2^h, that is, X is "
                        + "minimum-order with this center (MCD). The forward implication does not "
                        + "assume that every distance is central. This is Corollary 11 of H. Ma "
                        + "and W. Zhang (version 3), settling Conjecture 5.5 of Dovgoshey et al.")),
                    Paragraph(Text(
                        "If the counts hold, the open balls of radius c_h, the diameter, partition "
                        + "X into parts of equal size t with (r - 1)t = 2^(h-1), and each part "
                        + "contains the disjoint spheres of radii c_0, …, c_(h-1) around its points, "
                        + "so t ≥ 2^(h-1); hence r = 2 and |X| = 2^h. Conversely, on an MCD space "
                        + "the two open balls of radius c_h around points at distance c_h are "
                        + "disjoint, keep every lower central value and so each have at least "
                        + "2^(h-1) points by the minimum-order bound; they therefore have exactly "
                        + "2^(h-1) points and center {c_0, …, c_(h-1)}, and induction gives the "
                        + "lower spheres while the sphere of radius c_h is the other ball."))),
                DescribeRole.Theorem))));
}
