using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class ContinuousIntegerMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousIntegerMoments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous sampling and bounded variation quadrature transfer the discrete cubic and fourth moments.",
        H("Integer-length continuous mixed moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integer-third"),
                DeclarationHandle.Create(Prefix + "integer_third"),
                H("Integer-length cubic moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<alpha<beta<1/4, a normalized singular series satisfying HL4(beta) and the interval correlation estimates has vanishing continuous cubic mixed moments, uniformly for integer H in [N^alpha,N^beta], interval endpoints in [0,M], and supported bounded variation weights. The absolute error is at most B*delta eventually whenever the supremum-plus-variation bound is B."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-fourth"),
                DeclarationHandle.Create(Prefix + "integer_fourth"),
                H("Integer-length fourth moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same singular series, Hardy–Littlewood and interval correlation hypotheses, the continuous fourth mixed moment at integer H approaches the integral of the weight times kappa(N,H)^2 times the sum of the three overlap pairings. The error is uniformly at most B*delta on each polynomial length band and bounded endpoint window."))),
                DescribeRole.Theorem))));
}
