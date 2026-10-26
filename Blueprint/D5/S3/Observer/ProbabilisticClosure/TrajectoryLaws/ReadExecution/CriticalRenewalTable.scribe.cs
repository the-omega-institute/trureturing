using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution;

internal sealed class CriticalRenewalTableDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual capped zero row.",
        H("Critical renewal Table"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("criticalrenewaltable-phase-coin-row"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.phase_coin_row"),
                H("The actual capped zero row"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural cap J and phase z in Fin(J+1), mapping a Bernoulli coin with success probability 2^(-(z+1)) through Phase.step z gives exactly GeometricPhaseOccupation.finiteCappedRow J z. Live index z denotes source phase z+1. The last index J is dead; both fresh outcomes there have the same destination.")),
                    Paragraph(Text("The deterministic phase step stays on false and advances to min(z+1,J) on true. This includes J=0 and all finite phases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("criticalrenewaltable-fresh-row"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.fresh_row"),
                H("Every bit row is a fresh coin transition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive natural H, natural J, immutable Tick J, counted state s and Boolean input bit x, the distribution of next(s,x,b), when b has coin(s,x), is exactly row(s,x).")),
                    Paragraph(Text("The complete state carrier is one wait, two Boolean labels, and every integer evidence value strictly between -H and H paired with Fin(J+1). Wait holds on zero and enters evidence zero and phase zero on one. Both label rows fix their label. Active zero rows use the capped phase row at fixed evidence. Active tick rows round by lower(z)+b and go directly through target. target emits label one at or above H, label zero at or below -H, and otherwise retains the new evidence at phase zero. The order of these cases is explicit. No pending phase is needed.")),
                    Paragraph(Text("The coin outcome is consumed by one transition. Its retained consequence is only the successor in the counted carrier. The table depends on no source label, time, history, gap length or external register. A tick following zero zeros is a fully specified row."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("criticalrenewaltable-complete-gap-row"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.complete_gap_row"),
                H("The complete actual-gap row"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive H, natural J, immutable Tick J, interior evidence e and natural duration k, wordLaw from (e,first) along exactly k zeros and one closing tick is the capped phase law at k, followed by that same phase's tick coin and target(e+lower(z)+b). The duration k=0 is included.")),
                    Paragraph(Text("wordLaw samples a new row coin for every consecutive input bit and applies the deterministic counted-state successor. No zero after phase death is omitted. Capped phase death preserves the evidence while zeros continue to be read."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("criticalrenewaltable-random-gap-row"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.random_gap_row"),
                H("Duration and mark remain joint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any probability mass function f on natural durations, the f-mixture of the literal complete-gap rows at an interior evidence e is the pushforward of pairLaw f t through (k,u) mapped to target(e+u).")),
                    Paragraph(Text("pairLaw first draws k with law f, then the capped phase after its k zeros, and finally the tick coin at that phase. Its second coordinate is the integer increment lower(z)+b. The increment is not assumed independent of its own duration."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("criticalrenewaltable-full-state-count"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.full_state_count"),
                H("The entire listed carrier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural J and positive natural H, the cardinality of State H J is exactly 3+(2H-1)(J+1). All interior integer evidence values and all phases count; no reachability or positive-probability restriction is imposed.")),
                    Paragraph(Text("The three distinguished states are the wait and two internally emitted labels. The evidence interval has 2H-1 integers and the capped phase carrier has J+1 elements. The real choice H=ceil(A/delta) is a separate numerical specialization of this exact natural-H identity."))),
                DescribeRole.Theorem))));
}
