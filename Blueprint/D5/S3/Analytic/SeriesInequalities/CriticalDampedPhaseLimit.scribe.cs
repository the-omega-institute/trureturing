using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class CriticalDampedPhaseLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive damping that shrinks to zero leaves an exact full-array distance "
        + "determined by the limiting ratio of phase to damping.",
        H("Critical Damped Phase Limit"),
        Blocks(Describe.Lean(
            DescribeId.Create("critical-damped-phase-limit"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/SeriesInequalities/CriticalDampedPhaseLimit.critical_damped_phase_limit"),
            H("The full weighted distance for every finite phase ratio"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let A and rho be real, with A>0, 0<rho<1 and A rho=(1-rho)^2. "
                    + "Put c=A/(1+rho) and b=c rho. For every complex zeta of norm one, "
                    + "the boundary is a(i)=-A zeta^(i+1), indexed by natural numbers from zero. "
                    + "Its actual extension obeys E(a)(n,0)=a(n) and "
                    + "E(a)(n,k+1)=E(a)(n+1,k)-sum over j=0,...,k of E(a)(n,j)a(k-j).")),
                Paragraph(Text(
                    "Let tau and theta be arbitrary real sequences, with tau(j)>0 for every j, "
                    + "tau(j) tending to zero, and theta(j)/tau(j) tending to any real kappa. "
                    + "Define w(j)=exp(-tau(j)+i theta(j)). The theorem constructs bounded "
                    + "weighted arrays U and V(j) whose coordinates are exactly "
                    + "rho^(n+k) E(a)(n,k) and rho^(n+k) E(D_w(j)a)(n,k), respectively, "
                    + "where D_w a(i)=w^(i+1)a(i). These coordinate equations determine "
                    + "the arrays uniquely; the norm is the supremum over all natural n and k.")),
                Paragraph(Text(
                    "For every j, the norm of U-V(j) equals the supremum over natural k of "
                    + "(c+b rho^(2k)) times the modulus of "
                    + "1-exp(-(k+1)tau(j)+i(k+1)theta(j)). Thus the full norm is independent "
                    + "of the common unit phase zeta. The sequence theta tends to zero and "
                    + "the norm tends to c G(kappa), where G(kappa) is the supremum over "
                    + "s>=0 of the modulus of 1-exp(-s+i kappa s). The definition of the "
                    + "same integrand in Lean factors the exponential into its real damping "
                    + "and unit complex phase factors.")),
                Paragraph(Text(
                    "The recursion transports multiplication in degree i+1 to degree n+k+1. "
                    + "The constant negative boundary has amplitude u(k), with "
                    + "rho^k u(k)=c(1+rho^(2k+1)). At a fixed total degree the amplitude "
                    + "increases with k, so the largest coordinate occurs at n=0. This gives "
                    + "the exact norm formula without replacing the actual recursive arrays.")),
                Paragraph(Text(
                    "For a continuous nonnegative bounded profile f with f(0)=0 and weights "
                    + "converging from above to c>0, the supremum of w(n) f((n+1)t) tends "
                    + "to c sup(f) as the positive mesh t tends to zero. A finite prefix "
                    + "vanishes uniformly, while the tail weights approach c. The moving "
                    + "index floor(s/t)+1 approximates every nonnegative real s and gives "
                    + "the lower bound. A uniform parameter estimate for the damped spiral "
                    + "then permits the varying phase ratio. This argument includes kappa=0 "
                    + "and assumes no attained maximum on the noncompact half-line."))),
            DescribeRole.Theorem))));
}
