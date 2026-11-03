using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianCubicFiniteClassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Gaussian Cubic Finite Class",
        H("Original Gaussian Cubic Finite Class"),
        Blocks(
            Paragraph(Text("Explicit finite polynomials in the original neck coordinate represent every positive modulus coefficient of the literal TT and UT kernels. Degree bounds are proved for those constructed polynomials.")),
            Paragraph(Text("These sources are an implementation checkpoint. Native verification and independent admission review are separate requirements; no official acceptance or physical realization is asserted. Full four-halfmode geometry, two-source transport, identityK crossing, Monster moonshine, VOA/CFT/anomaly/fusion, complete string theory and AdS/CFT remain unfinished.")),
            Describe.Lean(
                DescribeId.Create("cubictt-finite-class"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFiniteClass.cubicTT_finite_class"),
                H("cubicTT_finite_class"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal product coefficient is a finite antidiagonal convolution embedded into the original Laurent field. The polar numerator has a double root at the external coordinate; its monic quotient cancels the original squared denominator. The zero constant term of the scalar series gives the remaining finite polynomial. These constructions yield degree strictly below the positive modulus degree, for arbitrary external amplitude."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubicut-finite-class"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFiniteClass.cubicUT_finite_class"),
                H("cubicUT_finite_class"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual inverse-series coefficient is combined with two finite antidiagonal sums. Each of the six original numerator monomials is embedded with its exact Laurent shift and negative pullback sign; the scalar contribution is the negative coordinate shift of the TT scalar polynomial. The constructed polynomial has degree at most the modulus degree. No root, sewing, resolvent or desired correspondence is assumed."))), DescribeRole.Theorem))));
}
