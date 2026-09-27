using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hankel;

internal sealed class RankOneInfiniteHorizonRiskDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp uniform prediction error for strictly stable scalar responses.",
        H("RankOneInfiniteHorizonRisk"),
        Blocks(
            Describe.Lean(DescribeId.Create("compatible"), DeclarationHandle.Create("D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.Compatible"), H("Compatible observations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For a parameter a strictly between zero and one, the impulse response at time k is a to the power k. Data consist of T+1 real observations indexed from zero through T. Each observation differs from its response by at most eta; the errors are deterministic and pointwise bounded."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("risk"), DeclarationHandle.Create("D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.risk"), H("All-future risk"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("An estimator is any map from the observation vector to a real prediction at every integer time n at least T. Its loss is the supremum of absolute prediction error over all such times, all parameters in the open unit interval, and every compatible observation vector. Extended nonnegative real values allow unbounded losses."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("minimax-risk"), DeclarationHandle.Create("D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.minimaxRisk"), H("Optimal worst-case risk"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The minimax risk is the infimum of the all-future risks over all deterministic sequence estimators, without restrictions on computation or measurability."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hankel"), DeclarationHandle.Create("D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.hankel"), H("Finite Hankel sections"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The Hankel section indexed from zero through N has entry a to the power i+j. It is the outer product of the vector of powers with itself, whose zeroth coordinate is one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rank-one-infinite-horizon-risk"), DeclarationHandle.Create("D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.rank_one_infinite_horizon_risk"), H("Exact risk one half"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("For every finite integer T at least one and every positive eta, the all-future minimax risk equals one half. Every response tends to zero, and every nonempty finite Hankel section is positive semidefinite with rank exactly one. No common spectral gap is imposed.")),
                Paragraph(Text("The constant prediction one half bounds the error by one half. For the reverse inequality, the all-one observation vector is compatible with stable parameters sufficiently close to one. Fix one such parameter b and choose an allowed late time at which its response is arbitrarily small. A second parameter a can be chosen closer to one so that it remains compatible with the same data and its response at that time is arbitrarily close to one. The same prediction then incurs error approaching one half for at least one of these systems."))), DescribeRole.Theorem)),
        []));
}
