using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class ThetaLaplaceContinuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/ThetaLaplaceContinuation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual cutoff theta transform continues meromorphically and detects every zeta zero with real part greater than one half with its full multiplicity.",
        H("Chebyshev theta Laplace continuation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("theta-laplace-continuation"),
                DeclarationHandle.Create(Prefix + "theta_laplace_continuation"),
                H("Actual integrals, arbitrary cutoffs and multiplicity-dependent poles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q(u)=exp(-u)*(theta(exp(u))-exp(u)), where theta is Chebyshev's actual "
                        + "prime logarithm sum. For a real cutoff u0>=0, Q(u0,s) is the Lebesgue "
                        + "integral of exp(-s*u)*q(u) over u>u0. Put b(n)=0 at primes and "
                        + "b(n)=Lambda(n) otherwise, and let C be its complex Dirichlet series. "
                        + "The actual coefficient prefixes are psi(x)-theta(x). Chebyshev's "
                        + "O(sqrt(x)) bound proves absolute convergence and holomorphy of C "
                        + "throughout Re(z)>1/2. Reindexing its absolutely summable terms gives "
                        + "C(z)=sum_p sum_j log(p)*p^(-(j+2)*z), with j>=0.")),
                    Paragraph(Text(
                        "Chebyshev's linear theta bound makes q measurable and globally bounded "
                        + "in absolute value by log(4)+1. Thus Q converges absolutely for Re(s)>0. "
                        + "The prime coefficient Lambda-b has prefix theta; Mathlib's SumCoeff "
                        + "integral representation and Dirichlet's actual zeta logarithmic "
                        + "derivative give its complex Mellin identity. Substitution x=exp(u), "
                        + "including the Jacobian exp(u), yields Q(0,s)="
                        + "(-logDeriv(zeta,1+s)-C(1+s))/(1+s)-1/s.")),
                    Paragraph(Text(
                        "The oriented finite interval correction is A(u0,s)="
                        + "integral(exp(-(s+1)*u)*(theta(exp(u))-exp(u)),u=0..u0). "
                        + "Splitting the actual integrable tail gives Q(u0,s)=Q(0,s)-A(u0,s). "
                        + "Bounded measurable coefficients on a finite interval allow "
                        + "differentiation under this integral, so A is entire. On the infinite "
                        + "tail a positive exponential margin controls the first moment and proves "
                        + "Q'(u0,s)=-integral(u*exp(-s*u)*q(u),u>u0). This assertion includes "
                        + "integrability of that actual moment.")),
                    Paragraph(Text(
                        "Write zeta1 for Mathlib's entire normalized factor, with "
                        + "zeta(z)=(z-1)^(-1)*zeta1(z) away from 1, zeta1(1)=1 and "
                        + "zeta1'(1)=EulerGamma. Then M(u0,s)="
                        + "-(1+logDeriv(zeta1,1+s)+C(1+s))/(1+s)-A(u0,s) is meromorphic "
                        + "on Re(s)>-1/2 and equals the actual Q for Re(s)>0. It is analytic "
                        + "at zero, with value -1-EulerGamma-C(1)-A(u0,0). This continued "
                        + "value does not assert convergence of the original integral at s=0.")),
                    Paragraph(Text(
                        "At every actual zeta zero rho with Re(rho)>1/2, the analytic order is "
                        + "finite and its natural multiplicity m is positive. Set a=rho-1 and "
                        + "alpha=-m/rho, which is nonzero; a lies in Re(s)>-1/2 and a is not zero. Finite-order factorization of the "
                        + "actual zeta function gives a nonvanishing analytic factor and an "
                        + "analytic logarithmic-derivative remainder R for zeta1. The identity "
                        + "-m/((1+s)*(s-a))=alpha/(s-a)+m/(rho*(1+s)) produces an analytic "
                        + "H such that M=alpha/(s-a)+H on a punctured neighborhood. "
                        + "Differentiating this exact identity yields -M'+M="
                        + "alpha/(s-a)^2+alpha/(s-a)+H-H'. The respective unit factors after "
                        + "multiplication by s-a and (s-a)^2 have center value alpha. "
                        + "Consequently the exact meromorphic orders are -1 and -2, "
                        + "without a simple-zero hypothesis.")),
                    Paragraph(Text(
                        "This supplies the actual theta transform for a signed-tail Laplace "
                        + "argument. It does not construct the separate signed-tail clock, "
                        + "prove its moment convergence or continuation, establish an oscillation "
                        + "or abscissa theorem, or imply the Riemann hypothesis or Robin's criterion. "
                        + "For the separate actual clock f, the intended integration-by-parts equation is "
                        + "s*L''(s)+2*L'(s)=-Q'(s)+Q(s)+u0^2*f(u0)*exp(-s*u0). Its positive "
                        + "cutoff term is entire and must be retained unless its coefficient is separately proved zero."))),
                DescribeRole.Theorem))));
}
