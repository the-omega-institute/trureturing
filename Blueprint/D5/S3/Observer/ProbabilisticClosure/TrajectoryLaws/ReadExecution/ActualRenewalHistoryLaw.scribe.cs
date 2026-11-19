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
                    Paragraph(Text("No law of the epoch process, positivity of any history, eventual stopping or termination of an auxiliary chain is assumed. Initially terminal states, stops during zero segments, zero initial wait, zero gaps and arbitrary measurable coin spaces remain in scope. Primitive product realization, effective-row specialization, real matrix transport, predictable payment, occupation and the full original E4 are separate obligations."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-renewal-history-step"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalHistoryLaw.actual_history_step"),
                H("Summing every actual next gap"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a measurable event of the finite source coordinates and actual epoch history that fixes the current state s, locality converts that event to an exact raw-past event. Apply actual_past_step separately at each natural gap k and use countable additivity on the disjoint exhaustive gap events. The next-state event has mass P(E) times the B-mass of f.bind(k => zeroRow(A,k,s).bind(C)). This is the actual execution's row identity, including gap zero and zero-mass histories; no normalized conditional probability or assumed law of Y is used."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-renewal-ordinary-past"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalHistoryLaw.actual_ordinary_past"),
                H("The ordinary-past integral identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every measurable event H of epochs zero through n and every measurable target set B, partition H by its current actual state s. Countable additivity and the actual all-gap row identity give P(H and Y(n+1) in B) as the sum over s of P(H and Y(n)=s) times the B-mass of the common gap-mixture row at s. This nonnegative state-sum form is the ordinary-past Markov integral identity. It applies to null histories without selecting values by division."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-renewal-state-prefix"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalHistoryLaw.actual_state_prefix"),
                H("Every length of actual state prefix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every length l and every state word x of that length, the probability that the literal actual epochs equal x is prefixMass(nu,U,l,x). Here nu is the w-mixture of eta.bind(s => zeroRow(A,u,s).bind(C)), and U(s) is the f-mixture of zeroRow(A,k,s).bind(C). The unique empty word has mass one. At length one the result is actual_initial_law; each successor appends the last-state factor using the actual ordinary-history step. Thus m=0, unreachable words and every zero entry are retained. The formula is derived from Primitive and the effective sampler rows, rather than imposed as a cylinder law."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-renewal-source-cylinder"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalHistoryLaw.actual_source_cylinders"),
                H("Joint source and state cylinders"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix the first wait u, exactly n following gaps v, and n+1 actual epoch states x. The joint cylinder mass is w(u) times the x(0)-mass of eta.bind(s => zeroRow(A,u,s).bind(C)), multiplied over j<n by f(v(j)) times the x(j+1)-mass of zeroRow(A,v(j),x(j)).bind(C). The base integrates the literal first wait word on its fixed source slice. The successor fixes the last actual state and applies raw-past freshness to the next original gap and coins. Empty gap tuples at n=0, initial stops and later stops inside zero words are included. Neither primitive realization for the two original targets nor the remaining E4 payment and occupation claims follow from this abstract cylinder theorem."))), DescribeRole.Theorem))));
}
