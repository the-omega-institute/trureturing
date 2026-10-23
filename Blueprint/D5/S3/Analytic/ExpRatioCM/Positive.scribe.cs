using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ExpRatioCM;

internal sealed class PositiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive exponential coefficients and complete monotonicity.",
        H("The coefficient criterion"), Blocks(
            Describe.Lean(DescribeId.Create("exp-ratio-first-moment-formula"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Positive.F_one"),
                H("The first signed derivative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive t, F(1,t)=exp(t)/(exp(t)-1)^2. The existing logarithmic derivative formula yields this identity, which supplies the low-index ratio formulas."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-low-ratio-formulas"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Positive.ratio_low"),
                H("Low-index ratio formulas"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive t, ratioF(0,t)=1+F(0,t), ratioF(1,t)=1+2F(0,t), ratioF(2,t)=1+4F(0,t)-2F(0,2t), and ratioG(0,t)=F(0,t). These identities support the low-index complete monotonicity proof."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-g-zero-eq"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Positive.G_zero_eq"),
                H("The constant term in the second family"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive t, G(0,t) equals 1+F(0,t)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-contdiffon-f"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Positive.contDiffOn_F"),
                H("Smooth exponential moments"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every F(i) is smooth on the positive half-line."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-contdiffon-ratiof"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Positive.contDiffOn_ratioF"),
                H("Smooth first ratios"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The quotient F(i+1)/F(i) is smooth on the positive half-line because its denominator is strictly positive."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-contdiffon-ratiog"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Positive.contDiffOn_ratioG"),
                H("Smooth second ratios"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The second consecutive ratios are smooth on the positive half-line. The zeroth denominator equals 1+F(0), and the positive-order denominators equal the corresponding F moments."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-cm-positive-expansion"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Positive.cm_of_nonnegative_exponential_expansion"),
                H("Nonnegative exponential expansion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A smooth function whose every derivative is represented by nonnegative coefficients at nonnegative exponential frequencies has alternating derivatives of the required sign on the positive half-line."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-cm-positive-cases"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Positive.cm_of_le_two"),
                H("Low-index positive cases"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The signed exponential moments give complete monotonicity of the zeroth moment. The frozen logarithm derivative theorem LogOneSubExpDerivatives.log_one_sub_exp_derivatives supplies the first two signed moment identities through Series.iteratedDeriv_F and neighborhood equality. Only the third signed moment identity requires one further differentiation, since the frozen theorem stops at the third logarithm derivative. These identities give the low-index closed forms on the entire positive half-line. The first two ratios are a nonnegative constant plus a nonnegative multiple of the zeroth moment. The third ratio is one plus four times that moment minus twice its value at twice the argument. At every derivative order the even terms of the moment series bound this subtraction, proving the required sign. This is the same coefficient positivity as coefficient four at positive odd frequencies and coefficient two at positive even frequencies. The zeroth ratio of the second family equals the zeroth moment, and its positive-index ratios agree with the first family."))),
                DescribeRole.Theorem))));
}
