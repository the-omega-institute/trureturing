using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class ContinuousIntegerMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousIntegerMoments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous sampling from second moments transfers the cubic asymptotic on beta<1/3; fourth moments transfer on beta<1/4. Bounded variation quadrature controls both weight replacements.",
        H("Integer-length continuous mixed moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integer-third"),
                DeclarationHandle.Create(Prefix + "integer_third"),
                H("Integer-length cubic moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<alpha<beta<1/3 and M>=1, a singular series equal to one on the empty set and singletons and satisfying MeanSquareHL(3,SS,beta) and the interval correlation estimates has vanishing continuous cubic mixed moments, uniformly for integer H in [N^alpha,N^beta], interval endpoints in [0,M], and supported bounded variation weights. For every delta>0, the absolute error is at most B*delta eventually whenever the supremum-plus-variation bound is B."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-fourth"),
                DeclarationHandle.Create(Prefix + "integer_fourth"),
                H("Integer-length fourth moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<alpha<beta<1/4, under the singular series normalization, MeanSquareHL4(SS,beta) and interval correlation hypotheses, the continuous fourth mixed moment at integer H approaches the integral of the weight times kappa(N,H)^2 times the sum of the three overlap pairings. The error is uniformly at most B*delta on each polynomial length band and bounded endpoint window."))),
                DescribeRole.Theorem))));
}
