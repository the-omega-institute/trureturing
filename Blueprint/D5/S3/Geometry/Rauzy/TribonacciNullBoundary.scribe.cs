using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Rauzy;

internal sealed class TribonacciNullBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "The frontier of the actual Tribonacci Rauzy fractal has planar Haar measure zero.",
            H("Null frontier of the Tribonacci Rauzy fractal"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("tribonacci-rauzy-null-frontier"),
                    DeclarationHandle.Create("D5/S3/Geometry/Rauzy/TribonacciNullBoundary.rauzyFractal_frontier_volume_zero"),
                    H("The original Rauzy frontier has volume zero"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                        "For every complex z belonging to the roots of the Tribonacci characteristic "
                        + "polynomial X^3 - X^2 - X - 1 and distinct from the real Tribonacci constant beta, "
                        + "volume(frontier(rauzyFractal z)) = 0. Here rauzyFractal z is the existing closure "
                        + "of finite exponent-zero admissible Boolean sums, with no three consecutive ones. "
                        + "Volume is the two-dimensional Haar measure on the complex plane. "
                        + "The three prefix branches are w mapped to z w, 1 + z^2 w, and 1 + z + z^3 w. "
                        + "The exact prefix cover, compactness and nonempty interior hold for this same set "
                        + "under these two root hypotheses. The root identities give z nonzero, norm(z) < 1 "
                        + "and beta norm(z)^2 = 1. The three branch area weights norm(z)^2, norm(z)^4 "
                        + "and norm(z)^6 are positive and sum to one by the reciprocal-power identity for beta. "
                        + "Multiplication by b scales planar Haar measure by norm(b)^2, from its real-linear "
                        + "determinant; translations preserve volume. All three branches are open and have "
                        + "common Lipschitz constant norm(z). The contracting-cover theorem constructs a whole "
                        + "interior cylinder and removes its positive weight from the frontier cover. Finite "
                        + "boundary mass then forces zero. Coverage, separation, tiling and a nullity premise "
                        + "are not additional hypotheses. The argument applies to both non-Perron roots."))), DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Topology/ContractingCoverNullBoundary")),
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Geometry/Rauzy/TribonacciRegularClosure")),
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Geometry/Rauzy/TribonacciInterior")),
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Tower/Tribonacci/RauzyFractal")),
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Tower/Tribonacci/Binet")),
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Tower/Tribonacci/Values"))
            ]));
    }
}
