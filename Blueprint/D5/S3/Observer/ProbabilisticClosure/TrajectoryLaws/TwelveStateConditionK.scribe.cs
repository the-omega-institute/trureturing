using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class TwelveStateConditionKDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Condition K on the original emitted-bit clock", H("Condition K on the original emitted-bit clock"),
        Blocks(
            Paragraph(Text("The deterministic-state observation convention is represented by arrival matrices K times the diagonal selector. Its equality with the usual stationary state-observation cylinder formula is proved on the same integer clock.")),
            Describe.Lean(DescribeId.Create("observation"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateConditionK.observation"),
                H("The deterministic observation selector"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a state observation f and Boolean x, observation(f,x) is the diagonal indicator of f(i)=x, retaining every structural zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-condition-k-boundary"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateConditionK.actual_condition_k_boundary"),
                H("The actual Condition K exclusion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite stationary marked presentation θ, transition matrix K and deterministic observation f with θ.matrix(x)=K observation(f,x), assume its whole visible law equals the actual twelve-state P and every pair of hidden states has a positive K-power entry. For every integer origin and every finite word, the actual cylinder mass equals the usual departure-observation formula using observation(f,x)K. Every word product of the arrival matrices has no nonempty exact positive rectangular support. Summing selectors gives K, hence stationarity and stochasticity transfer from θ. The intertwining identity cancels K at the two ends under the stationary initial row and stochastic final column. Irreducible positive stationary masses then make a nonzero rectangle a supported word, contradicting the same-law obstruction. Thus the additional aperiodicity required by finite Condition K cannot restore such a presentation. No rank-one or scaled-closure assertion is made."))), DescribeRole.Theorem))));
}
