using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class Q9TenShadowSelfAdjointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed fibers of a ten-pattern projection",
        H("A half-size bound from signed self-adjointness"),
        Blocks(Describe.Lean(
            DescribeId.Create("q9-ten-pattern-signed-fiber-bound"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowSelfAdjoint."
                    + "tenShadow_global_inequality"),
            H("A weighted bound on two fibers and one coordinate half"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Suppose the projection of a Huang-balanced induced cubic nine-cube support "
                    + "onto the first four coordinates is contained in "
                    + "{0,1,2,3,4,5,10,11,12,14}, using the first coordinate as the low bit. "
                    + "Let w₀ and w₂ be the fiber sizes at codes 0 and 2, and let h count the "
                    + "vertices with that bit set. Then 4(w₀ + w₂) + 3h is at most twice the "
                    + "support size.")),
                Paragraph(Text(
                    "The exterior Huang equations express each signed fiber using four "
                    + "entries in {−1,0,1}. A finite check on those parameters gives a "
                    + "weighted occupation inequality with a mixed term between the signed "
                    + "slices at codes 1 and 3. On summing over the five remaining coordinates, "
                    + "the mixed term vanishes by self-adjointness of the signed adjacency."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-ten-pattern-signed-fiber-exclusion"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowSelfAdjoint."
                        + "tenShadow_excluded"),
                H("Exclusion of the exact ten-pattern projection at half-size 30"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The slices at codes 0 and 2 satisfy the five-cube parity equation "
                        + "after reducing the signed row equations modulo two. Exact projection "
                        + "makes these slices nonempty. Each has induced degree at most three "
                        + "and hence at least eight vertices. With 72 vertices in the support "
                        + "and h at least 30, the weighted bound would give 154 at most 144.")),
                    Paragraph(Text(
                        "This removes the indicated projection in the order-72 branch "
                        + "of Hong, Wu and Xia, arXiv:2610.09483v1, Section 7, Problem 2."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9GridProjection"))
        ]));
}
