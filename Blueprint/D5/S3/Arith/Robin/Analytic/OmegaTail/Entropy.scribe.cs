using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class EntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binomial entropy at a moving interior proportion.", H("Binomial entropy at a moving interior proportion"), Blocks(
            Describe.Lean(DescribeId.Create("log-choose-scaled"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Entropy.log_choose_scaled"),
                H("Moving binomial exponent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any filter, any real scale y tending to positive infinity, and natural functions n and k with n/y tending to d>0 and k/y tending to r with 0<r<d, log(choose(n,k))/y tends to d*binEntropy(r/d). The proof uses the pinned Stirling sequence limit at n, k and n-k, the exact factorial quotient, and logarithmic errors divided by the growing scale. It does not require a Gaussian window or a rate of convergence of k/n."))), DescribeRole.Theorem))));
}
