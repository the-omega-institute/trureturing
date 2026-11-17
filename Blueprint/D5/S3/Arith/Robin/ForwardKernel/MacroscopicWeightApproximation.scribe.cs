using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MacroscopicWeightApproximationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightApproximation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform interval cancellation extends to continuous weights when absolute mass stays bounded.",
        H("Continuous macroscopic weights"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("continuous-weight-lifting"),
                DeclarationHandle.Create(Prefix + "continuous_weight_lifting"),
                H("Lifting interval cancellation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let f(X,i,u) be eventually integrable on [1,2], with the integrals "
                        + "of its absolute value bounded by one constant uniformly in i. "
                        + "Suppose the integral over every subinterval tends to zero uniformly "
                        + "in i and in both endpoints. For every real continuous weight phi "
                        + "on [1,2], the integrals of phi(u)*f(X,i,u) tend to zero uniformly in i.")),
                    Paragraph(Text(
                        "Uniform continuity provides a fixed partition into equal blocks on "
                        + "which phi differs little from its left endpoint value. The sum of "
                        + "the errors is at most that oscillation times the total absolute "
                        + "mass. The finite sum with the frozen weights tends to zero by "
                        + "interval cancellation. The partition is chosen before X. For "
                        + "linear averages, a uniform second-moment bound controls absolute "
                        + "mass by Cauchy–Schwarz; for bilinear averages, apply Cauchy–Schwarz "
                        + "to the two factors. A nonzero limiting density can be subtracted "
                        + "before applying this result."))),
                DescribeRole.Theorem))));
}
