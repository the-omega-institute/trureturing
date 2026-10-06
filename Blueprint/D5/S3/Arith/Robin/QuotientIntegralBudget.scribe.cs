using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class QuotientIntegralBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/QuotientIntegralBudget.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual quotient residual blocks have separate head and logarithmic tail payments before infinite integral exchange.",
        H("Quotient Integral Budget"),
        Blocks(
            Paragraph(Text(
                "Let K(y) be the finite prefix of k(n) over positive integers n<=floor(y), "
                + "G(y)=A*y*log(y)-D*y and R=K-G. The real coefficients A,D are arbitrary. "
                + "Assume independent C,mu>=0, 0<=k(n)<=C*log(n) for every n>=1, and "
                + "|R(y)|<=mu*(1+log(y)) for every y>=1. The coefficient assumptions imply k(1)=0. "
                + "On 0<y<1 the actual residual is D*y-A*y*log(y).")),
            Paragraph(Text(
                "For x>1 use the existing Robin weight w(t)=(1+log(t))/(t^2*log(t)^2) and "
                + "W(x)=(1+log(x))/log(x)^2. Define Q(x,m) as the integral on t>x of "
                + "|R(t/m)-R(t/(m+1))|*w(t). This absolute value is taken inside the integral. "
                + "Put a2=C+|A|, a1=C+2*|A|*(1+log(2))+2*|D|+2*mu and a0=4*mu.")),
            Describe.Lean(
                DescribeId.Create("original-absolute-block-budget"),
                DeclarationHandle.Create(Prefix + "quotientIntegralProducer"),
                H("The actual residual blocks are integrable with separate first and quadratic logarithmic budgets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every x>1 the actual weighted absolute block is integrable for every m>=1. "
                        + "The first block obeys Q(x,1)<=W(x)*(mu*(3+2*log(2))+|D|+|A|*log(2)). "
                        + "Every m>=2 obeys Q(x,m)<=W(x)/m^2*(a2*log(m)^2+a1*log(m)+a0).")),
                    Paragraph(Text(
                        "With c=m/(m+1), each finite prefix jump has support [n,n/c). "
                        + "The low domain is enlarged to 1/m<=y<=m and its finite jump sum is integrated "
                        + "before any infinite exchange. Exact jump masses and a smooth log-product majorant "
                        + "pay this domain. The centered residual envelope pays y>m, retaining the "
                        + "actual residual instead of separately integrating unsigned K and G on the tail."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-logarithmic-tail"),
                DeclarationHandle.Create(Prefix + "quotient_logarithmic_tail"),
                H("Every strict tail has its explicit logarithmic payment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let B>=0 and assume the explicit inequality |H(m)|<=B*m/log(m)^4 for every m>=2. "
                        + "For every M>=2 the strict tail sum over m>M of |H(m)|*Q(x,m) is at most "
                        + "B*W(x)*(a2/log(M)+a1/(2*log(M)^2)+a0/(3*log(M)^3)). "
                        + "The strict enumeration is m=n+M+1, and reciprocal-log integral tests pay "
                        + "the three terms with their exact factors 1, 1/2 and 1/3."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-signed-integral-budget"),
                DeclarationHandle.Create(Prefix + "quotient_signed_integral_budget"),
                H("The signed series has integrable blocks and a complete norm budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the same hypotheses define F(m,t)=H(m)*(R(t/m)-R(t/(m+1)))*w(t). "
                        + "Every positive-index F(m) is integrable on t>x, and the integral of its pointwise norm equals "
                        + "|H(m)|*Q(x,m). The sequence of these norm integrals is summable. "
                        + "H(1) is unrestricted and its norm integral is at most |H(1)| times the separate "
                        + "first-block budget. Every strict norm tail has the preceding explicit bound.")),
                    Paragraph(Text(
                        "These integrable blocks and summable integrals of their pointwise norms supply the premises of "
                        + "Mathlib's integral_tsum_of_summable_integral_norm. That existing Fubini result "
                        + "is the downstream supplier. "
                        + "The coefficient and residual envelopes do not prove the independent H growth "
                        + "hypothesis, the complete Robin inequality or the Riemann hypothesis."))),
                DescribeRole.Theorem))));
}
