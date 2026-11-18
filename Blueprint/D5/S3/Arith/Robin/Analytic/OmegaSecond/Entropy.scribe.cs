using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaSecond;

internal sealed class EntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite binomial entropy lower bound with an explicit logarithmic loss.",
        H("Finite binomial entropy lower bound"), Blocks(
            Describe.Lean(DescribeId.Create("log-choose-ge-binentropy"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.log_choose_ge_binEntropy"),
                H("Maximum-term entropy bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For natural a at most m, log choose(m,a) is at least m*binEntropy(a/m)-log(m+1), including the endpoint cases. At p=a/m the binomial probabilities increase up to a and decrease after a, as their adjacent-term recurrence shows. Their sum is one, so the a-th term is at least 1/(m+1). Taking logarithms yields the bound. This is the finite maximum-term argument, with no Stirling estimate or asymptotic hypothesis. In the second-threshold construction it estimates the number of choices in each prime box; feasibility is proved separately by the exchange budget. The equal-number exchange method around a primorial and its partition-constant mechanism have precedent in Erdős–Nicolas 1981, section 1."))), DescribeRole.Theorem))));
}
