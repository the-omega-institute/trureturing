using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualRobinClockCovarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal finite Robin log kernels have ordered relative activation and decreasing actual centered covariance.",
        H("Actual Relative Clock Covariance for the Finite Robin Log Kernel"),
        Blocks(
            Paragraph(Text(
                "For the literal finite clipped kernel W(A,x), the common ambient "
                + "floor equals the literal floor definition, including noninteger "
                + "clocks. Increasing A increases W(A,x), while W(A,x)-W(A',x) "
                + "decreases in x.")),
            Describe.Lean(
                DescribeId.Create("actual-robin-clock-covariance"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualRobinClockCovariance.actual_clock_covariance"),
                H("Actual covariance signs and support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite actual clock sample with clocks greater "
                        + "than one, the unnormalized centered covariance is "
                        + "nonnegative on positive shifts and decreases when both "
                        + "arguments advance. If every clock is at most b and "
                        + "b<=2*y, the later covariance is exactly zero.")),
                    Paragraph(Text(
                        "The proof uses the literal clipped sum and a common finite "
                        + "ambient floor. It does not assume a covariance envelope, "
                        + "relative-clock K or C bound, Corr, a CA optimizer "
                        + "realization, or a Robin/RH conclusion. The exact finite "
                        + "Abel coefficient budget remains a separate obligation."))),
                DescribeRole.Theorem))));
}
}
