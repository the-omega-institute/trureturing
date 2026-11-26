using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class RobinActualWeightedBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit bounds for the weighted Chebyshev tail.",
        H("Explicit bounds for the weighted Chebyshev tail"),
        Blocks(
            Paragraph(Text("The unconditional integrated explicit formula splits the weighted Chebyshev error into the actual zero response and a residual from the trivial zeros and the constant term.")),
            Describe.Lean(DescribeId.Create("log-bounds"), DeclarationHandle.Create(Prefix + "J_log_bounds"),
                H("Two-sided logarithmic bounds"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For j in [1,10] and u at least log 2, assuming every actual occurrence lies on the critical line, the upper bound is the first Li mass times exp((1/2 − j)u) H(j,u). The lower bound is its negative minus log(2π) exp(−ju)/u."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("li-mass"), DeclarationHandle.Create(Prefix + "firstLiMass_lt_twentieth"),
                H("First Li mass constant"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact bounds on Euler’s constant and the logarithms give a first Li mass strictly below 1/20."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tail-lower"), DeclarationHandle.Create(Prefix + "actual_weighted_tail_lower"),
                H("Scaled weighted tail lower bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real x at least 2 on the same occurrence-line premise, the weighted Chebyshev tail scaled by √x log x is at least −((1/20)(1 + 1/log x) + 2/√x)."))), DescribeRole.Theorem)
        )));
}
