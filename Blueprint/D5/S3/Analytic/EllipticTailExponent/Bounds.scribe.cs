using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EllipticTailExponent;

internal sealed class BoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized elliptic tails", H("Coefficient and derivative bounds"), Blocks(
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-b"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Bounds.b"),
                H("Normalized tail coefficients"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive k, b(k,a) is (1-a/k)/(k(k+1)) times the product of 1-a^2/j^2 over 1<=j<k. The index zero is not used in the tail."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-b-bounds"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Bounds.b_bounds"),
                H("Positive summable majorants"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive natural k and 0<=a<=3/4, the coefficient b(k,a) is strictly positive and at most 1/(k(k+1)). Every factor of the finite product lies in (0,1]."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-b-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Bounds.b_zero"),
                H("Coefficients at zero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a=0 the normalized coefficient equals 1/(k(k+1)). This identity supplies the exact tail value at zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-deriv-b-bounds"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Bounds.deriv_b_bounds"),
                H("Strictly negative coefficient derivatives"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive k and 0<=a<=3/4, the derivative of b(k,a) is strictly negative and has absolute value at most 4/(k(k+1)). Differentiating the product leaves nonpositive contributions. The shared NormalizedPochhammerBounds.inverse_square_sum theorem bounds the finite reciprocal-square sum by two, and the derivative of the leading linear factor is strictly negative."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-u"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Bounds.U"),
                H("Normalized infinite tails"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("U(n,a) is the sum of b(k+n+1,a) over natural k. The rational coefficient majorant is summable for each fixed n."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-hasderivat-u"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Bounds.hasDerivAt_U"),
                H("Termwise differentiation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n and 0<a<3/4, U(n,a) has derivative equal to the sum of the derivatives of its coefficient functions. The uniform summable derivative majorant and convergence at a=1/2 justify differentiation on the preconnected open interval (0,3/4)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-u-pos"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Bounds.U_pos"),
                H("Strict positivity of the tail"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n and 0<=a<=3/4, U(n,a)>0. The series converges and every summand is positive."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-deriv-u-neg"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Bounds.deriv_U_neg"),
                H("Strict decrease of the normalized tail"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n and 0<a<3/4, the derivative of U(n,a) is strictly negative. Termwise differentiation gives a convergent series of negative derivatives."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-continuouson-u"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Bounds.continuousOn_U"),
                H("Continuity through parameter zero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalized tail is continuous on [0,3/4]. Summable bounds for the continuous coefficient polynomials give uniform convergence, including at zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-u-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Bounds.U_zero"),
                H("Exact tail value at zero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, U(n,0)=1/(n+1). The rational summands at zero telescope as 1/k-1/(k+1)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-norm-deriv-u-le"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Bounds.norm_deriv_U_le"),
                H("A uniform tail derivative bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 0<a<3/4, the norm of the derivative of U(n,a) is at most four times the sum of 1/((k+n+1)(k+n+2)). This parameter-independent finite bound makes a times the derivative tend to zero as a decreases to zero."))), DescribeRole.Theorem))));
}
