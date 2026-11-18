using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class MovingPrimeSoftplusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/MovingPrimeSoftplus.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Moving softplus weights on primes.",
        H("Softplus comparison with Chebyshev theta"),
        Blocks(
            Describe.Lean(DescribeId.Create("movingprimesoftplus-weight"),
                DeclarationHandle.Create(Prefix + "weight"), H("Moving softplus weight"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At t the weight is log(1 + exp(-s |log(t/P)|)), where P is the real center and s is the scale."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("movingprimesoftplus-softplus-theta-window"),
                DeclarationHandle.Create(Prefix + "softplus_theta_window"), H("Uniform finite comparison"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For P > 0 and s >= 0, suppose E >= 0 bounds |theta(t) - t| on [P/2, 2P]. The log-prime weighted sum on (P/2, 2P] differs from the Lebesgue integral of the weight by at most 6 log(2) E. Finite Abel summation on each side of P pays for two boundary terms and a derivative integral. Each half has variation at most log(2), independently of s."))), DescribeRole.Theorem)
        )));
}
