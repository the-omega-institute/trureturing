using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class WeightControlDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/WeightControl.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original forward weight ratio has quantitative value and derivative bounds.",
        H("Correlated forward weight ratios"),
        Blocks(
            Paragraph(Text(
                "Use the existing functions H(x)=x^(4/5) and "
                + "w(x)=(1+log(x))/(x^2*log(x)^2). For x>=4 and 0<=u<=1, "
                + "let A(x,u)=w(x+u*H(x))/w(x). The center in the denominator "
                + "moves together with the center in the numerator.")),
            Describe.Lean(
                DescribeId.Create("forward-weight-ratio-value"),
                DeclarationHandle.Create(Prefix + "weightRatio_sub_one"),
                H("Value of the original ratio"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact monotonicity and lower power bound for w give "
                    + "|A(x,u)-1|<=4*x^(-1/5). The lower bound uses "
                    + "(x/(x+u*H(x)))^4 rather than replacing the weight "
                    + "by a different window."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-weight-ratio-derivative"),
                DeclarationHandle.Create(Prefix + "weightRatio_control"),
                H("Cancellation in the correlated derivative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The ratio satisfies 0<=A(x,u)<=1. Put "
                        + "L(x)=(-2+1/(1+log(x))-2/log(x))/x, the logarithmic "
                        + "derivative of w. The derivative of A in x equals "
                        + "A(x,u)*(L(x+u*H(x))*(1+(4/5)*u*x^(-1/5))-L(x)). "
                        + "Its absolute value is at most 12*x^(-6/5).")),
                    Paragraph(Text(
                        "For x>=4, |L(x)|<=5/x and |L'(x)|<=8/x^2. "
                        + "The mean value theorem bounds L at the two correlated "
                        + "arguments. Their separation is u*H(x), so the "
                        + "difference has size at most 8*u*x^(-6/5). The "
                        + "moving-endpoint factor contributes at most "
                        + "4*u*x^(-6/5). This establishes the extra relative "
                        + "window factor in the derivative."))),
                DescribeRole.Theorem))));
}
