using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class FullZeroGaussianResponseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/FullZeroGaussianResponse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An off-line zero forces a positive response of the complete zero family at an explicit Gaussian scale.",
        H("Full Gaussian zero response"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("full-zero-gaussian-response"),
                DeclarationHandle.Create(Prefix + "full_zero_gaussian_response"),
                H("Positive response, exact signed integration, and envelope bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho be a countable family in the open critical strip, with multiplicities, "
                        + "a conjugation-preserving permutation, |Im(rho_i)|>10, and "
                        + "HasSum of a_i=1/(rho_i*(1-rho_i)) equal to 2+EulerGamma-log(4*pi). "
                        + "Fix rho_0=beta+i*gamma with beta>1/2 and gamma>0. Put delta=beta-1/2, "
                        + "D=gamma+10, m0=100*D^2/delta^2, m1=500*D^4/delta^2, and a=beta^2+16*beta. "
                        + "There is m in [m0,m1], with m>=1, for which the complete Gaussian sum "
                        + "E_gamma(m)=sum exp(m*(rho_i-i*gamma)^2+16*m*(rho_i-i*gamma)) "
                        + "converges absolutely and Re(E_gamma(m))>=exp(a*m)/2.")),
                    Paragraph(Text(
                        "Use the normalized Gaussian g(y)=exp(-(y-16*m)^2/(4*m))/sqrt(4*pi*m), "
                        + "u(y)=(y-16*m)/(2*m), P(y)=(u(y)+i*gamma)*(u(y)+i*gamma-1)-1/(2*m), "
                        + "K(y)=-Re(exp(-i*gamma*y)*P(y))*g(y), and "
                        + "v(y)=2*(u(y)^2+gamma^2+1)*g(y). The envelope satisfies v>=|K|. "
                        + "Both H*K and H*v are integrable, as is exp(max(y,0))*v(y), and "
                        + "the signed identity is integral H*K=Re(E_gamma(m)).")),
                    Paragraph(Text(
                        "The full envelope integral is retained: integral H*v is the real part of "
                        + "sum 2*a_i*(rho_i^2+gamma^2+1+1/(2*m))*exp(m*rho_i^2+16*m*rho_i). "
                        + "Its absolute value is at most 1000*D^2*exp(-83*m). "
                        + "Taking the real part makes this identity an equality of real numbers.")),
                    Paragraph(Text(
                        "The finite set |Im(rho_i)-gamma|<=6 contains the designated zero. "
                        + "The finite power-sum theorem chooses an integer nu with 1<=nu<=2*n+1; "
                        + "m=nu*m0 gives the positive finite response and the stated scale bounds. "
                        + "The inverse-height budget controls the omitted terms: for m>=1 and x>=c>=1, "
                        + "exp(-m*x)<=c*exp(-m*c)/x. Applied to the shifted heights, this bounds the "
                        + "far response by 2*D^2*exp(-19*m). Applied to |Im(rho_i)|>10, it bounds "
                        + "the unshifted Gaussian sum by 200*exp(-100*m), hence by 500*exp(-100*m).")),
                    Paragraph(Text(
                        "Mathlib's complex Gaussian moment-generating function and its first two derivatives "
                        + "give the individual polynomial responses. The common majorant "
                        + "|a_i|*exp(max(y,0))*v(y) pays the integral of the norm before interchanging "
                        + "the sum and integral. The proof uses the summable coefficients and keeps the "
                        + "Gaussian height decay after integration; it requires no unweighted second moment of the zeros."))),
                DescribeRole.Theorem))));
}
