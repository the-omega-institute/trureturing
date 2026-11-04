using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalRightSkewDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Finite Right Coefficients",
        H("Original Finite Right Coefficients"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-right-coefficient"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalRightSkew.originalRightCoefficient"),
                H("The original right coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let M be the actual negative parity space and A the original fixed source carrier. Write rho_t(a)u for the standard mode of fixedParitySlice; its underlying tensor is correctedField(a).coeff(-2t-2)u. Write S for the actual translation L(-1) on M. For every signed mode s the bilinear map R_s:M x A -> M is the finite sum over natural ell of (-1)^(s+ell+1)/ell! times S^ell rho_(s+ell)(a)u.")),
                    Paragraph(Text("This is the coefficient of exp(z S)rho(-z). For arbitrary original polynomial inputs, VertexOperator lower-exponent support gives an upper bound for the standard modes. Consequently the raw coefficients and translated terms vanish for all sufficiently large ell. Finite support justifies addition in both inputs; scalar multiplication also commutes with the finite sum. The definition does not use a zero default for an unsupported infinite sum."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-right-skew-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalRightSkew.original_right_skew_finite"),
                H("Integer spectral cutoff and ordered contraction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume the original lattice has rank twenty-four and integer unit determinant. Let a be any original fixed source of signed integer weight h, let u in M have actual L0 eigenweight H for any natural H, and let s be any integer. The detector d is an arbitrary original actual tensor. Put E=H+h-s-1 and raw_ell=rho_(s+ell)(a)u. Each raw coefficient has integer energy E-ell.")),
                    Paragraph(Text("If E<2, every raw coefficient is zero and R_s(u,a)=0. This is an integer-energy statement established before converting a cutoff to a natural number. If E>=2, raw_ell=0 whenever ell>=(E-1).toNat. Thus R_s is exactly the sum over ell<(E-1).toNat of the displayed translated terms, and its underlying tensor satisfies L0 R_s=E R_s. The bound is an upper support bound; allowed summands need not be nonzero.")),
                    Paragraph(Text("Let C be the actual tensor L(1), with ActualGround and actualInverse. The exact ordered scalar contraction is B(d,R_s)=sum over ell<(E-1).toNat of (-1)^(s+ell+1)/ell! times B(C^ell d,raw_ell). Actual stress transposition moves S from the second slot to C in the first slot. No symmetry of B, detector energy hypothesis, source skew, extension vertex algebra, crossing law or desired Jacobi premise is used. C and S act on actual tensors and are distinct from source lowering and fixedTranslation.")),
                    Paragraph(Text("For the three-M right channels, take the original source inverse P of normalizedCoefficient, without a new normalization. For homogeneous u,v,w of weights H,K,L and integers m,n,r, put E=H+K+L-m-n-r-2. The first right channel uses a=P_(n+j)(v,w), source weight K+L-n-j-1 and s=m+r-j. The second uses a=P_(m+j)(u,w), source weight H+L-m-j-1 and s=n+r-j. Both have the same cutoff ell<(E-1).toNat when E>=2. When E<2, both raw families vanish pointwise over the integers.")),
                    Paragraph(Text("The first outer factor (-1)^j choose(r,j) gives the contraction sign (-1)^(m+r+ell+1)/ell!. The second outer factor (-1)^(j+r) choose(r,j), before its overall subtraction, gives (-1)^(n+ell+1)/ell!, since (-1)^(2r)=1 for every integer r. Original source truncation supplies separate outer ranges (H+K-r).toNat, (K+L-n).toNat and (H+L-m).toNat; source grade zero is retained. These parameter substitutions describe the use of the finite right coefficient and do not assert that the nonzero-energy three-M defect vanishes.")),
                    Paragraph(Text("The original four-M native scalar/common rational identification remains a separate obligation. These finite coefficients do not complete Monster moonshine, a vertex operator algebra extension, conformal field theory, anomalous fusion, string theory or AdS/CFT."))), DescribeRole.Theorem))));
}
