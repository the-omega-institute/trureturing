using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class RemainderContinuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/RemainderContinuation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A holomorphic error integral.",
        H("A holomorphic error integral"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("remainder-tail-converges"),
                DeclarationHandle.Create(Prefix + "remainder_tail_converges"),
                H("The infinite endpoint of partial summation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume alpha>=0 and an eventual bound |E(t)|<=C*t^alpha. Let x0>=3, sigma>alpha-7/10 and A>=0. Suppose |r(t)|<=A*t^(-sigma-7/10) and |dr(t)|<=A*t^(-sigma-17/10) for t>=x0, with dr almost everywhere strongly measurable. Then E(t)*dr(t) is integrable on (x0,infinity), and E(t)*r(t) tends to zero. The boundary exponent p=alpha-sigma-7/10 is negative, and the integral exponent is p-1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("remainder-integral-holomorphic"),
                DeclarationHandle.Create(Prefix + "remainder_integral_holomorphic"),
                H("A holomorphic error integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same eventual power bound and x0>=3, let d(s,t) be holomorphic in s for Re(s)>alpha-7/10 and t>x0. Assume d and its parameter derivative are almost everywhere strongly measurable in t. If every compact parameter set K has A>=0 with |d(s,t)|<=A*t^(-Re(s)-17/10) for all s in K and t>=x0, the integral of E(t)*d(s,t) over t>x0 is holomorphic on that half-plane. Cauchy estimates on nested parameter balls provide an integrable majorant for differentiation under the integral."))),
                DescribeRole.Theorem))));
}
