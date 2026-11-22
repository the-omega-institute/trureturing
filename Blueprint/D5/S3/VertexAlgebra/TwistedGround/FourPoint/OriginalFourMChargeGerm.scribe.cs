using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMChargeGermDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original four-point diagonal germ in the negative square coordinate",
        H("The original four-point diagonal germ"),
        Blocks(
            Describe.Lean(DescribeId.Create("chargesectorsewn"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.chargeSectorSewn"),
                H("Native sewn charge-sector sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a fixed lattice datum, charge class, four occupations and complex sewing "
                    + "coordinate, sum the sewn charge terms in the class with zero contribution from all "
                    + "other charges."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-fourm-coset-negative-square-germ"),
                DeclarationHandle.Create(Prefix + "cosetSeries_negative_square_germ"),
                H("Analytic descent of each sewn charge coset"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let D have positive definite real Gram matrix and unit Gram determinant. "
                        + "For a mod-two charge class a, let fₐ(w) be the original sewn charge sum for a "
                        + "after the finite lowering and Laurent projection in diagonalSewn. "
                        + "At each fixed occupation the charge terms use q on the left and −q on the right. "
                        + "The charge-normal bound gives a summable majorant on a closed disk of radius "
                        + "0 < r < 1, and the projected sum is analytic at zero.")),
                    Paragraph(Text("On the diagonal t = E + t₀, the left exponent and the right exponent "
                        + "−2t − 2 each shift by −2E from their values at E = 0. This cancels the energy "
                        + "shift in each selector, so one finite projection gives the coefficients at every E.")),
                    Paragraph(Text("For any Taylor radius R > 0 chosen strictly inside a disk of expansion "
                        + "at zero, absolute summability of the Taylor coefficients at R yields absolute "
                        + "summability of the descended coefficients at R². Their degree-E coefficient "
                        + "is (−1)^E times the ordinary Taylor coefficient of fₐ of order 2E, equivalently "
                        + "the coefficient of degree E of cosetSeries at t = E + t₀ rescaled by −1. "
                        + "The descended germ Gₐ satisfies Gₐ(−w²) = (fₐ(w) + fₐ(−w))/2 near zero. "
                        + "The two sewing evaluations use w and −w and enter the average with plus signs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-fourm-scalar-negative-square-germ"),
                DeclarationHandle.Create(Prefix + "fourM_scalar_negative_square_germ"),
                H("The actual fourM germ at all orders"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume in addition that D has rank 24. The actual minus-one parity "
                        + "states u = P ⊗ x and v = Q ⊗ y have L₀-weights H and K. For every E in ℕ, "
                        + "the degree-E Taylor coefficient of a single holomorphic germ G is the "
                        + "actual fourMScalar at modes H + K − E − 1 and E + t₀ on "
                        + "u, v, R ⊗ z, S ⊗ d.")),
                    Paragraph(Text("Near zero, G(−w²) is the sum over mod-two charge classes a of "
                        + "((fₐ(w) + fₐ(−w))/2) · groundForm(D,y,Cₐx) · groundForm(D,d,Cₐz). "
                        + "Here Cₐ is the charge operator for the actual ground representation. "
                        + "The ordered left pairing is (y,Cₐx) and the ordered right pairing is (d,Cₐz). "
                        + "The finite coset sum gives the germ, and the actual energy-coefficient identity "
                        + "identifies its coefficients for all E."))),
                DescribeRole.Theorem))));
}
