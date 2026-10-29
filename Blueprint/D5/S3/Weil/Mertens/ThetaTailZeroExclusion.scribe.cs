using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class ThetaTailZeroExclusionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/ThetaTailZeroExclusion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An eventual exponential upper bound on the actual logarithmic theta tail rules out every Riemann zeta zero in the corresponding right half-plane.",
        H("Actual theta-tail exponential zero exclusion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("theta-tail-zero-exclusion"),
                DeclarationHandle.Create(Prefix + "actual_theta_tail_exponential_zero_exclusion"),
                H("Positive-density continuation and zero exclusion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix 0<b<1/2 and C>=0. Assume the actual logarithmic theta tail f is eventually "
                        + "bounded above by C*exp(-b*u). Choose one cutoff U beyond both the eventual-bound "
                        + "threshold and the source threshold log 2. The actual integrability of f on the tail "
                        + "and the exponential integrability of the majorant make C*exp(-b*u)-f(u) integrable "
                        + "on Ioi U. Its nonnegative ofReal density defines a finite positive measure mu on "
                        + "that half-line.")),
                    Paragraph(Text(
                        "For X=id, the genuine complex moment generating function of mu splits on Re(s)>0 as "
                        + "G(s)=K(s)-L(U,s), where K(s)=C*exp(-(s+b)U)/(s+b) is the elementary exponential "
                        + "integral and L(U,s) is the actual cutoff Laplace transform of f. The actual theta-tail "
                        + "ODE and the continuation identity Q(U,s)=M(U,s) give the Euler forcing equation for G, "
                        + "including the positive cutoff term U^2*f(U)*exp(-sU).")),
                    Paragraph(Text(
                        "The positive Euler continuation theorem extends G holomorphically to Re(s)>-b without "
                        + "assuming a target-cut integrability hypothesis. Since K is holomorphic there, H=K-G is "
                        + "holomorphic and agrees with the actual L(U,.) on Re(s)>0. The Euler expression of H "
                        + "minus the cutoff term is therefore analytic on the whole half-plane. On the right half-plane "
                        + "it equals the meromorphic forcing -M'(U,s)+M(U,s). Equality is transported as meromorphic "
                        + "germs on the connected half-plane, rather than asserted pointwise at totalized poles.")),
                    Paragraph(Text(
                        "If rho were a zeta zero with 1-b<Re(rho), then a=rho-1 lies in this half-plane. "
                        + "The continuation source gives the exact multiplicity-dependent order -2 of "
                        + "-M'(U,.)+M(U,.) at a, while the transported analytic Euler expression has nonnegative "
                        + "order. This contradiction proves the exclusion.")),
                    Paragraph(Text(
                        "The result is conditional on the actual eventual bound and does not assume RH, zero-freeness, "
                        + "convergence of the signed transform on the target line, or a real-cut continuation. It is "
                        + "the analytic zero-exclusion step intended for the later Robin/5040 application; that arithmetic "
                        + "witness and its unbounded-prefix consequence are separate applications."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The actual source law, positive continuation theorem, and multiplicity-dependent forcing pole are "
                + "the reusable ingredients for this conditional conclusion.")))));
}
