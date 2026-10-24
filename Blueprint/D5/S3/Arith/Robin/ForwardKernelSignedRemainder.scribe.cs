using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ForwardKernelSignedRemainderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernelSignedRemainder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial summation identifies a convergent signed prime-power remainder with its error integral.",
        H("Signed forward-kernel remainders"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-remainder-limit"),
                DeclarationHandle.Create(Prefix + "signed_remainder_tendsto"),
                H("The infinite endpoint of exact partial summation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E(t)=psi(t)-t and assume |E(t)|<=C*sqrt(t)*log(t)^2 "
                        + "for t>=2. Suppose a>=3, sigma>-1/5, A>=0, r'=dr on "
                        + "[a,infinity), and dr is almost everywhere strongly measurable "
                        + "with respect to Lebesgue measure restricted to that interval. If "
                        + "|r(t)|<=A*t^(-sigma-7/10) and "
                        + "|dr(t)|<=A*t^(-sigma-17/10), then as b tends to infinity, "
                        + "sum(Lambda(n)*r(n),floor(a)<n<=floor(b))-integral_a^b r(t) dt "
                        + "tends to -E(a)*r(a)-integral_a^infinity E(t)*dr(t) dt.")),
                    Paragraph(Text(
                        "Finite Abel summation and ordinary integration by parts give "
                        + "the exact identity with the additional endpoint E(b)*r(b). "
                        + "The complete Chebyshev psi keeps every prime power with its "
                        + "full logarithmic weight. The initial atom is excluded and the "
                        + "terminal atom is included. The stated estimates make the "
                        + "error integral absolutely integrable and send the terminal "
                        + "endpoint to zero."))),
                DescribeRole.Theorem))));
}
