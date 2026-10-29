using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class AnalyticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/Analytic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual inverse-coordinate forward remainder and its differentiated Chebyshev tail depend holomorphically on the Mellin parameter.",
        H("Analytic dependence of the inverse-coordinate remainder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("entire-integral-compact-bound"),
                DeclarationHandle.Create(Prefix + "entire_integral_of_compact_bound"),
                H("Integrating an entire family with compact uniform bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a finite measure space, let f(s,a) be almost everywhere strongly "
                    + "measurable in a for every s, and entire in s for almost every a. "
                    + "Assume that every compact parameter set K has a finite constant C "
                    + "such that |f(s,a)|<=C for all s in K outside one null set. "
                    + "Then integral f(s,a) da is entire. Countable difference quotients "
                    + "give measurability of the parameter derivative. Cauchy's estimate "
                    + "on unit circles inside a ball of radius two bounds that derivative "
                    + "by an integrable constant, allowing differentiation under the integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adjoint-remainder-entire"),
                DeclarationHandle.Create(Prefix + "adjointRemainder_entire"),
                H("Entire dependence of the actual remainder"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each fixed t>8, the actual remainder "
                    + "r(t,s)=t^(-s-1/2)*(N(t,s)-1/2) is entire in s. "
                    + "Here N is the fixed triangular integral of the normalized "
                    + "inverse-coordinate kernel. Its parameter dependence is an exponential "
                    + "of (-s-1/2)*log(x(t,z)/t), multiplied by the original weight ratio "
                    + "and inverse Jacobian. The proved kernel bounds are uniform on each "
                    + "compact parameter set, so the finite-measure integral theorem applies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adjoint-remainder-time-derivative-entire"),
                DeclarationHandle.Create(Prefix + "adjointRemainder_timeDerivative_entire"),
                H("The time derivative is also entire in the parameter"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each fixed t>8, the time derivative of r(t,s) is entire in s. "
                    + "The exact derivative-under-integral formula for N differentiates "
                    + "the same triangular kernel. Its integrand is a finite sum of "
                    + "polynomials in s times the original exponential, with real "
                    + "coefficients depending on the inverse coordinate. The uniform "
                    + "time-derivative estimate gives compact parameter bounds. "
                    + "This proves entire dependence before forming the Chebyshev tail."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adjoint-remainder-tail-holomorphic"),
                DeclarationHandle.Create(Prefix + "adjointRemainder_tail_holomorphic"),
                H("Holomorphy of the actual differentiated remainder tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume alpha>=0 and there are real C and t0 such that "
                    + "|psi(t)-t|<=C*t^alpha for every t>=t0. "
                    + "For every fixed x0>8, integral_(x0,infinity) "
                    + "(psi(t)-t)*partial_t r(t,s) dt is holomorphic for Re(s)>alpha-7/10. "
                    + "The actual compact C1 remainder bound gives "
                    + "|partial_t r(t,s)|<=A_K*t^(-Re(s)-17/10) on each compact K. "
                    + "Derivatives as functions of t are measurable; countable parameter "
                    + "difference quotients provide the remaining measurability. "
                    + "The Chebyshev remainder integral theorem then applies with these "
                    + "proved properties of the actual kernel."))),
                DescribeRole.Theorem))));
}
