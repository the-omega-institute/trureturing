using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SingularSeriesTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantitative singular series tails",
        H("Quantitative singular series tails"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("primorial-ratio-eq-denominator-product"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SingularSeriesTail.primorial_ratio_eq_denominator_product"),
                H("primorial ratio eq denominator product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural cutoff y, the primorial divided by its totient equals the product over primes at most y of the reciprocal of one minus the reciprocal prime."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("density-log-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SingularSeriesTail.density_log_bound"),
                H("density log bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every M at least one, a nonnegative constant bounds the primorial sieve density by that constant times log H for every real H at least two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("correlation-tail-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SingularSeriesTail.correlation_tail_bound"),
                H("correlation tail bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every M at least one there is a nonnegative constant C such that, for each order k between one and four, every real H at least two and all ordered interval endpoints in [0,M], the full and finite distinct correlations differ by at most C H^k (log H)^4 / ((M+5)H)^10. The estimate follows by summing the uniform centered Euler tail over the distinct shift tuples."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("concrete-interval-covariance"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SingularSeriesTail.concrete_interval_covariance"),
                H("concrete interval covariance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume MSSecond. For every M at least one there is a nonnegative C such that, for every H at least one and two ordered intervals in [0,M], the absolute value of the second distinct full correlation plus H log H times their overlap length is at most C H. Translation invariance identifies the centered singular-series kernel with the interval covariance sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-correlation-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SingularSeriesTail.second_correlation_bound"),
                H("second correlation bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume MSSecond. For every M at least one there is a nonnegative C such that the absolute second distinct full correlation of any two ordered intervals in [0,M] is at most C H log H for every real H at least two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pairing-tail-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SingularSeriesTail.pairing_tail_bound"),
                H("pairing tail bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume MSSecond. For every M at least one there is a nonnegative C such that, for every real H at least two and four ordered intervals in [0,M], the full and finite sums of pairing products differ by at most C times the sum of H^3 (log H)^5 / ((M+5)H)^10 and H^4 (log H)^8 / ((M+5)H)^20."))),
                DescribeRole.Theorem))));
}
