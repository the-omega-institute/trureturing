using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalFourMCoefficientsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The global original inverse and its genuinely finite three-M channels.",
        H("Original Four-M Coefficients"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-i-homogeneous"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.originalI_homogeneous"),
                H("The same original inverse on each homogeneous grade"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Global originalI applies the existing sourceGradePairingEquiv inverses to the actual finite graded support of normalizedCoefficient. On homogeneous inputs it is exactly the inverse used by OriginalFourMContraction, with no change of normalization or carrier. originalI_truncation preserves the existing all-state upper bound; the sharper homogeneous bound is also proved."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-jacobi-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.original_jacobi_finite"),
                H("Three statewise finite original channels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("All original M states and all integer m,n,r have statewise finite j families. For homogeneous inputs the exact ranges are j below (H+K-r).toNat, (K+L-n).toNat, and (H+L-m).toNat. The right phases remain (-1)^j and (-1)^(j+r). No infinite sum of endomorphisms is used."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-jacobi-below-two"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.original_jacobi_below_two"),
                H("The exact below-two branch"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("At common output weight N=H+K+L-m-n-r-2 below 2, the original fixed-parity mode and original right coefficients vanish by the existing exact cutoff facts. Thus the original homogeneous Jacobi equation is automatic in this branch; the physical ground shift is not substituted for the negative-parity module."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-jacobi-scalar-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.original_jacobi_scalar_finite"),
                H("Unrestricted detector scalarization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original homogeneous input and every signed integer triple, the full vector law is equivalent to the actualForm tests in the first pairing slot over every ActualTensor detector. The common ell cutoff is (N-1).toNat. Both integer right-transport phases and factorials remain exact. The N below 2 branch is derived, so there is no permanent N-at-least-2 premise."))
                ), DescribeRole.Theorem)
        ), []));
}
