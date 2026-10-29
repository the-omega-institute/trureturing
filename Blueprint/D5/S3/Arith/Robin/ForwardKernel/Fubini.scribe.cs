using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class FubiniDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/Fubini.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute Fubini retains every complete-prime-power contribution in the forward Mellin adjoint.",
        H("The complete forward Mellin adjoint"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unbounded-forward-adjoint"),
                DeclarationHandle.Create(Prefix + "unbounded_forward_adjoint"),
                H("Absolute transport of the complete signed response"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let x0>=4 and let f be a measurable complex center weight. Assume "
                        + "that norm(f(x))*abs(T(x)) and norm(f(x))*V(x) are integrable over "
                        + "x>=x0, where V(x)=integral k(x,t) dt is the original continuous "
                        + "kernel mass. Then the literal adjoint integral of f(x)*k(x,t) "
                        + "is integrable in t, and its Lambda-weighted positive-integer "
                        + "values form an absolutely summable series.")),
                    Paragraph(Text(
                        "The integral of f(x)*T(x) equals that series minus the integral "
                        + "of the adjoint in t. Nonnegativity of the original kernel bounds "
                        + "its complete arithmetic row mass by abs(T(x))+V(x). This proves "
                        + "both product-integrability statements before either use of Fubini. "
                        + "Every prime power keeps its full log-prime weight."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-mellin-adjoint-tendsto"),
                DeclarationHandle.Create(Prefix + "forwardMellin_adjoint_tendsto"),
                H("Signed adjoint truncations recover the Mellin integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume alpha>=0 and an eventual power bound abs(psi(t)-t)<=C*t^alpha "
                        + "for all t>=t0. For x0>=4 and Re(s)>max(1/2,alpha-3/10), the actual adjoint "
                        + "q_s(t) is integrable over t>1. The difference between the "
                        + "sum of Lambda(n)*q_s(n) for 0<=n<=floor(b) and the integral "
                        + "of q_s(t) from 1 to b tends to the original forward Mellin "
                        + "integral as b tends to infinity.")),
                    Paragraph(Text(
                        "The established response convergence and continuous-kernel moment "
                        + "bound supply the two absolute majorants. The adjoint vanishes "
                        + "for t<=1. Absolute summability gives the arithmetic truncation "
                        + "limit, and integrability gives the continuous truncation limit. "
                        + "The power error estimate is an explicit hypothesis."))),
                DescribeRole.Theorem))));
}
