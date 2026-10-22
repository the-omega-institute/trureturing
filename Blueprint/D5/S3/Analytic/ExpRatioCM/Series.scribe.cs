using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ExpRatioCM;

internal sealed class SeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exponential moments and their quotient coefficients.",
        H("Series and signed derivatives"), Blocks(
            Describe.Lean(DescribeId.Create("exp-ratio-iteratedDeriv-F"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Series.iteratedDeriv_F"),
                H("Signed derivative composition"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For natural i and k and every real t, the k-th derivative of F(i) is (-1)^k F(i+k). The differentiation operation is iterated on globally defined functions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-G-zero-eq"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Series.G_zero_eq"),
                H("The constant term in the second family"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive t, G(0,t) equals 1+F(0,t)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-G-eq-F"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Series.G_eq_F"),
                H("Equality at positive orders"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For i at least one and t positive, G(i,t)=F(i,t). The reciprocal identity holds on a neighborhood of t, so its derivatives agree there."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-contDiffOn-F"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Series.contDiffOn_F"),
                H("Smooth exponential moments"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every F(i) is smooth on the positive half-line."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-F-eq-tsum"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Series.F_eq_tsum"),
                H("The exponential moment expansion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive t, F(i,t) is the sum over natural n of (n+1)^i exp(-(n+1)t). Polynomially weighted geometric convergence supplies locally uniform derivative bounds."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-F-pos"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Series.F_pos"),
                H("Strictly positive moments"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every F(i,t) is strictly positive when t is positive. Each term in its convergent exponential expansion is positive."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-contDiffOn-ratioF"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Series.contDiffOn_ratioF"),
                H("Smooth first ratios"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The quotient F(i+1)/F(i) is smooth on the positive half-line because its denominator is strictly positive."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-ratioG-eq-ratioF"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Series.ratioG_eq_ratioF"),
                H("Equality of positive-index ratios"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For i at least one and t positive, the ratios of the two derivative families agree."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-contDiffOn-ratioG"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Series.contDiffOn_ratioG"),
                H("Smooth second ratios"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The second consecutive ratios are smooth on the positive half-line. The zeroth denominator equals 1+F(0), and the positive-order denominators equal the corresponding F moments."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-quotCoeff"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Series.quotCoeff"),
                H("The quotient coefficient recurrence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The zeroth coefficient is one. At positive n the coefficient is (n+1)^(i+1) minus the sum over j from zero to n-1 of (j+2)^i times the coefficient at n-1-j."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exp-ratio-quotCoeff-two"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Series.quotCoeff_two"),
                H("The second quotient coefficient"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural i, the coefficient at index two equals 2 times 3^i minus 4^i."))), DescribeRole.Theorem)))));
}
