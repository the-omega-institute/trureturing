using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution;

internal sealed class ActualRenewalHistoryLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary histories of the actual raw renewal execution.",
        H("Actual history and cylinder laws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-renewal-history-locality"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalHistoryLaw.actual_history_locality"),
                H("The ordinary past is an exact raw past"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix a finite source slice containing the first wait and exactly the gaps before epoch n. Its cut is the original clock c(n). Extend the unused gaps by zero and the unused coin suffix by the first coin of the nonempty prefix. Those extensions are used only to define a deterministic reconstruction map on the initial state and the coins strictly before c(n); they are not a replacement probability model.")),
                    Paragraph(Text("The saved actual-word identities prove by induction that the reconstruction equals every actual epoch from zero through n. All accessed coins lie strictly before the slice cut. The map is measurable because each deterministic raw step is the common effective sampler applied to a state and one coordinate. Consequently every measurable event of the finite source tuple and the ordinary epoch history is an exact raw-past event. The next gap K(n), the coin at c(n), and the whole future tape are excluded.")),
                    Paragraph(Text("No law of the epoch process, positivity of any history, eventual stopping or termination of an auxiliary chain is assumed. Initially terminal states, stops during zero segments, zero initial wait, zero gaps and arbitrary measurable coin spaces remain in scope. Primitive product realization, effective-row specialization, real matrix transport, predictable payment, occupation and the full original E4 are separate obligations."))), DescribeRole.Theorem))));
}
