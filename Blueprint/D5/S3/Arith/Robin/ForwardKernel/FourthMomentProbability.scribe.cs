using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class FourthMomentProbabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FourthMomentProbability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second and fourth moments with a small mean force positive probability in both tails.",
        H("Two-sided probability from moments"),
        Blocks(
            Paragraph(Text(
                "For v>0 and a fourth-moment upper bound K, put "
                + "K1=8*(K+v^2/4), Lambda=(v/2)^(3/2)/sqrt(K1), "
                + "c=Lambda/8, and delta=Lambda^2/(16*sqrt(K1)).")),
            Describe.Lean(
                DescribeId.Create("fourth-moment-k-one"),
                DeclarationHandle.Create(Prefix + "fourthMomentK1"),
                H("Centered fourth-moment bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real v and K, define K1=8*(K+v^2/4). This is the fourth-moment bound after subtracting a mean whose absolute value is at most sqrt(v/2)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fourth-moment-lambda"),
                DeclarationHandle.Create(Prefix + "fourthMomentLambda"),
                H("Absolute first-moment lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real v and K, define Lambda=(v/2)^(3/2)/sqrt(K1), where K1=8*(K+v^2/4). Interpolation gives this lower bound for the first absolute moment of the centered variable."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fourth-moment-threshold"),
                DeclarationHandle.Create(Prefix + "fourthMomentThreshold"),
                H("Strict-tail threshold"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The threshold c is Lambda/8, where Lambda=(v/2)^(3/2)/sqrt(8*(K+v^2/4))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fourth-moment-density"),
                DeclarationHandle.Create(Prefix + "fourthMomentDensity"),
                H("Probability lower bound for each tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The probability lower bound delta is Lambda^2/(16*sqrt(K1)), with K1=8*(K+v^2/4) and Lambda=(v/2)^(3/2)/sqrt(K1)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("two-sided-positive-proportion-of-moments"),
                DeclarationHandle.Create(Prefix + "two_sided_positive_proportion_of_moments"),
                H("A uniform probability in each strict tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Z be an almost everywhere strongly measurable real random variable on a probability space. "
                        + "Assume Z, Z^2, and Z^4 are integrable, E[Z^2]>=v>0, "
                        + "E[abs(Z)^4]<=K, and abs(E[Z])<=min(sqrt(v/2),Lambda/8). "
                        + "Then both P(Z>c) and P(Z<-c) are at least delta.")),
                    Paragraph(Text(
                        "Center Z by W=Z-E[Z]. The variance identity gives E[W^2]>=v/2, "
                        + "and the even-power sum inequality gives E[W^4]<=K1. "
                        + "Holder's inequality with exponents 3/2 and 3 gives "
                        + "E[abs(W)^2]^3<=E[abs(W)]^2*E[abs(W)^4], so E[abs(W)]>=Lambda. "
                        + "The positive and negative parts of W each have expectation at least Lambda/2. "
                        + "Truncate either part at Lambda/4 and apply Cauchy-Schwarz on the upper event. "
                        + "Since its second moment is at most sqrt(K1), this event has probability "
                        + "at least delta. Finally abs(E[Z])<=Lambda/8 transfers the strict centered "
                        + "tails to the thresholds c and -c for Z."))),
                DescribeRole.Theorem))));
}
