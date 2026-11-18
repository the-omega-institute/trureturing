using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class RobinThresholdDivergenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An eventual threshold must diverge when every right-hand neighborhood of the endpoint contains a counterexample above each prescribed finite cutoff.",
        H("Divergence forced by a local obstruction family"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("threshold-divergence-local-obstruction"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/RobinThresholdDivergence.threshold_tendsto_atTop_of_local_obstruction"),
                H("Threshold divergence from local obstruction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let P κ n be a parameterized property and T κ a natural threshold. "
                        + "If P κ n holds for every n > T κ to the right of an endpoint a, "
                        + "while every sufficiently close right-hand neighborhood contains "
                        + "a counterexample above each finite cutoff M, then T κ tends to "
                        + "infinity as κ approaches a from the right.")),
                    Paragraph(Text(
                        "This is the order-theoretic implication used by Theorem 5.2 of "
                        + "the LCM/Robin volume. The local-obstruction premise is explicit; "
                        + "the endpoint counterexample from that volume's Theorem 2.3 is "
                        + "a separate unresolved input."))),
                DescribeRole.Theorem))));
}
