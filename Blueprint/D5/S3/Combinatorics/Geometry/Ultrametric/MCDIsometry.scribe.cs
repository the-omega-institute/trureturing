using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry.Ultrametric;

internal sealed class MCDIsometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/Ultrametric/MCDIsometry.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/dovgosheyrovenska2026ultrametriccenter");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimum-order finite ultrametric spaces with equally many points are isometric exactly "
            + "when their centers of distances coincide.",
        H("Isometry rigidity of minimum-order ultrametric spaces"),
        Blocks(
            Describe.Lean(DescribeId.Create("mcd-isometry-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Equal centers characterize isometry"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let X be a finite ultrametric space with |X| = 2^(|C(X)| - 1), where C(X) "
                        + "is the center of distances, and let Y be a finite ultrametric space "
                        + "that has as many points as X or also satisfies |Y| = 2^(|C(Y)| - 1). "
                        + "Then C(X) = C(Y) if and only if X and Y are isometric. This is "
                        + "Conjecture 4.3 of O. Dovgoshey and O. Rovenska, proved as Corollary 4.3 "
                        + "(with Theorem 4.2) of Dovgoshey, Jaiswal, Kainth, Kaur and Rovenska.")),
                    Paragraph(Text(
                        "Isometric spaces have the same center. Conversely, with common center "
                        + "{c_0 < ⋯ < c_n}, let m = c_n, which is the diameter. In X take points p "
                        + "and q at distance m; the open balls of radius m around them are "
                        + "disjoint and keep every lower central value, so each has at least "
                        + "2^(n-1) points by the minimum-order bound, hence exactly 2^(n-1), and "
                        + "together they cover X. Each half is minimum-order with center "
                        + "{c_0, …, c_(n-1)}, and likewise in Y. By induction the halves are "
                        + "isometric, and the two isometries glue to an isometry X → Y, since "
                        + "points in different halves are at distance m on both sides."))),
                DescribeRole.Theorem))));
}
