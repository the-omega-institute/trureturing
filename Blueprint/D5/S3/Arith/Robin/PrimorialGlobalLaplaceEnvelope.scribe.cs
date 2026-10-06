using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class PrimorialGlobalLaplaceEnvelopeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PrimorialGlobalLaplaceEnvelope.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal finite prime Euler ratio has one explicit error envelope on the complete nonnegative Laplace axis.",
        H("Primorial Global Laplace Envelope"),
        Blocks(
            Paragraph(Text(
                "For every real z>=2 let L=log(z), and take precisely the primes p<=floor(z). "
                + "Let E_z(s) be the finite product of 1-p^(-s), and F_z(v)=E_z(1+v/L)/E_z(1). "
                + "The product uses real powers. The denominator is positive, including when the finite product is empty.")),
            Paragraph(Text(
                "The comparison profile is Phi(v)=exp(integral from 0 to 1 of (1-exp(-v*b))/b db). "
                + "The proof bridges this original integral to the nonsingular primitive of "
                + "U(v)=integral from 0 to 1 of exp(-v*b) db. The single zero endpoint is retained "
                + "through equality of the integrands on the open interval. Put D=log(4)+4+Mertens.E1, "
                + "where the existing frozen Mertens.E1 is the sum over primes of log(p)/(p*(p-1)).")),
            Describe.Lean(
                DescribeId.Create("complete-actual-euler-envelope"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Every actual cutoff and every nonnegative Laplace parameter share the same explicit budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every z>=2 and every v>=0, exp(-D*v/L)*Phi(v)<=F_z(v)<=exp(D*v/L)*Phi(v). "
                        + "The same complete parameter axis obeys F_z(v)<=exp(D*v/L+1)*(1+v). "
                        + "There is no upper cutoff on v, and v=0 is included.")),
                    Paragraph(Text(
                        "The literal cumulative first-Mertens estimate is consumed by Abel summation. "
                        + "For the decreasing logarithmic exponential weight f, the integral error costs "
                        + "at most K*(1-f(z)); its endpoint costs at most K*f(z), so the combined cost is exactly K. "
                        + "The finite Euler logarithmic derivative is calculated from every factor. "
                        + "Replacing p^s-1 by p^s costs the existing summable prime correction uniformly "
                        + "for every v>=0. The resulting derivative error integrates to D*v/L. "
                        + "Exponentiation and the original profile's linear envelope give the stated bounds.")),
                    Paragraph(Text(
                        "This theorem supplies the finite Euler factor and its full parameter tail for the Robin kernel route. "
                        + "It does not prove the complete actual kernel asymptotic, the sign of the compensated Robin residual, "
                        + "or the Riemann hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-finite-support-curvature"),
                DeclarationHandle.Create(Prefix + "actualCurvature_bounds"),
                H("Actual prime support bounds the curvature by twice the same slope"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the same literal primes p<=z, put S_z(v)=(1/L)*sum log(p)/(p^(1+v/L)-1) "
                        + "and T_z(v)=(1/L^2)*sum p^(1+v/L)*log(p)^2/(p^(1+v/L)-1)^2. "
                        + "For every z>=2 and v>=0, 0<=T_z(v)<=2*S_z(v). "
                        + "The actual slope derivative is minus this actual curvature.")),
                    Paragraph(Text(
                        "The proof uses the actual finite support: log(p)<=L and q=p^(1+v/L)>=p>=2. "
                        + "Each curvature summand is its nonnegative slope summand multiplied by "
                        + "(log(p)/L)*q/(q-1)<=2. Finite summation gives the stated bound; "
                        + "no second prime moment asymptotic is assumed.")),
                    Paragraph(Text(
                        "PrimorialCompensatedNumerator directly consumes this bound together with the original "
                        + "ratio and slope derivatives. Its exact initial-slope compensation gives a uniform "
                        + "quadratic zero-end budget. The complete signed-kernel integral limit remains a separate consumer."))),
                DescribeRole.Theorem))));
}
