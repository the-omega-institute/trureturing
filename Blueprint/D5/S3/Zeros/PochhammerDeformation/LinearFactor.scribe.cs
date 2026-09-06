using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.PochhammerDeformation;

internal sealed class LinearFactorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/PochhammerDeformation/LinearFactor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive parameter, a normalized linear factor preserves the closed "
            + "real-root interval of the Pochhammer image.",
        H("Linear Factors for the Pochhammer Operator"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("linear-factor-falling-basis"),
                DeclarationHandle.Create(Prefix + "lOp_linear_factor_on_falling"),
                H("The operator identity on each falling basis element"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Write D_k=X(X-1)...(X-k+1) and A_k=(a)_k. The frozen operator "
                        + "definition gives L_a(D_k)=A_k X^k. The recurrences "
                        + "X D_k=D_(k+1)+k D_k and A_(k+1)=A_k(a+k) show that both "
                        + "sides of V7.0 equal A_k[(1+k/a)X^(k+1)+(t+k/a)X^k]. "
                        + "The constant basis element is included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("linear-factor-operator-identity"),
                DeclarationHandle.Create(Prefix + "lOp_linear_factor"),
                H("V7.0 for every real polynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For Q=L_a(P), the image L_a((X/a+t)P) is "
                        + "(X+t)Q+X(1+X)Q'/a. Mathlib's polynomial-sequence span theorem "
                        + "and linearity extend the basis identity to all polynomials. "
                        + "This identity requires a>0 but imposes no restriction on t."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("differential-root-interval"),
                DeclarationHandle.Create(Prefix + "differential_preserves_unit_interval"),
                H("The differential expression preserves the closed interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a>0 and 0<=t<=1, the expression (X+t)Q+X(1+X)Q'/a has "
                        + "all complex roots in the real interval [-1,0] whenever Q does. "
                        + "At a root away from Q and the endpoints, Mathlib's logarithmic "
                        + "derivative identity gives a*t/z+a*(1-t)/(z+1)+sum_r 1/(z-r)=0. "
                        + "Real linear functionals separate every point outside [-1,0] "
                        + "from this nonnegative weighted sum. Multiplicities are retained; "
                        + "zero polynomials and endpoint roots are handled separately."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pochhammer-linear-factor-preservation"),
                DeclarationHandle.Create(Prefix + "linear_factor_preserves_unit_interval"),
                H("Open Problem 1.9 with a normalized linear factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every a>0, 0<=t<=1 and real polynomial P whose Pochhammer image "
                        + "has all roots in [-1,0], the same holds after multiplying P by "
                        + "X/a+t. This resolves the registered linear-factor case of "
                        + "Vishnyakova's Open Problem 1.9 in arXiv:2608.03723. "
                        + "The unrestricted two-factor question is outside this theorem."))),
                DescribeRole.Theorem))));
}
