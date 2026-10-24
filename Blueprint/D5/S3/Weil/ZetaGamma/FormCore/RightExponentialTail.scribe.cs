using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class RightExponentialTailDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTail.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact half-line energy balance for the actual right exponential tail "
            + "retains its boundary value at zero and both real and imaginary channels.",
        H("Right exponential tail and its half-line energy balance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-right-exponential-tail"),
                DeclarationHandle.Create(Owner + "rightExponentialTail"),
                H("The literal right exponential-tail integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real rate k and complex profile u, R_k u(t) is the actual "
                        + "integral from zero to infinity of exp(-k*s)*u(t+s). "
                        + "The rate is allowed to be negative. On a continuous compactly "
                        + "supported input, the relevant integral is over a bounded "
                        + "interval at each t, so no decay assumption is added."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("right-exponential-tail-exact-energy-balance"),
                DeclarationHandle.Create(Owner + "right_exponential_tail_energy_balance"),
                H("Exact norm balance including the actual endpoint value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let u be any continuous compactly supported complex profile "
                            + "on the real line and let k and c be arbitrary real numbers. "
                            + "With all norms integrated over t>0, the identity is "
                            + "||u-c*R_k u||_2^2+c*(2*k-c)*||R_k u||_2^2 "
                            + "+c*|R_k u(0)|^2=||u||_2^2. No zero boundary value, "
                            + "parity, reality, differentiability of u, Fourier-domain "
                            + "hypothesis, or positivity of k or c is assumed.")),
                    Paragraph(Text(
                        "The proof translates the literal right-tail integral to "
                            + "exp(k*t) times the weighted tail integral. Compact "
                            + "support supplies one upper cutoff. The fundamental "
                            + "theorem of calculus gives (R_k u)'=k*R_k u-u. "
                            + "Differentiating its complex norm square through the "
                            + "real and imaginary channels and integrating to the "
                            + "cutoff pays the actual value at zero. The transformed "
                            + "norm is then expanded with integral additivity justified "
                            + "on that compact interval.")),
                    Paragraph(Text(
                        "For 0<=c<=2*k the two displayed correction terms are "
                            + "nonnegative, yielding the half-line contraction. In the "
                            + "W338 logarithmic coordinate u=x^(9/4)*U, k=5/4 and "
                            + "c=3/2 make both coefficients equal to 3/2. In the W314 "
                            + "coordinate g_U=x^(5/2)*U, the same c=3/2 instead gives "
                            + "k=3/2, a tail coefficient 9/4, and an endpoint coefficient "
                            + "3/2. These applications still need their actual "
                            + "source-coordinate identifications. This norm balance does not construct the "
                            + "complete arithmetic debit, identify its Weil value, bound "
                            + "the full logarithmic Gamma form by physical moments, "
                            + "or determine the sign required for RH."))),
                DescribeRole.Theorem))));
}
