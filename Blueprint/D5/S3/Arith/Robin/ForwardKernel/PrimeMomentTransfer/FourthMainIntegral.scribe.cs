using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class FourthMainIntegralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FourthMainIntegral.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted approximation of the fourth logarithmic pairing integral.",
        H("Fourth pairing integral"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fourth-main-integral-error"),
                DeclarationHandle.Create(Prefix + "fourth_main_integral_error"),
                H("Uniform approximation of the fourth main term"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let N be at least two, let one be at most H at most N, and let four ordered intervals lie in [0,M] with M nonnegative. For a supported bounded variation weight of norm at most B, the integral over [N,2N] of w(x/N) times the squared ratio (log x minus log H)/log N times the fourth overlap pairing differs from N times the mean of w on [1,2] times kappa(N,H) squared times that pairing by at most N B times 9 M squared log 2 divided by log N. The estimate follows by integrating the logarithmic square error and bounding the fourth overlap pairing by 3 M squared."))),
                DescribeRole.Theorem))));
}
