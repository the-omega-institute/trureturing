using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution;

internal sealed class CriticalRenewalFreshBlocksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A mark from its own actual gap.",
        H("Critical renewal FreshBlocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("criticalrenewalfreshblocks-block-pair-law"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalFreshBlocks.block_pair_law"),
                H("A mark from its own actual gap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural J, any duration mass function f and immutable Tick J, the pushforward of blockLaw f t under b mapped to (length(b.zeros),increment(t,b)) is exactly pairLaw f t.")),
                    Paragraph(Text("zeroTraceLaw starts with the empty zero history and phase zero. At each successive zero it samples the capped phase coin at the current phase and appends the outcome, retaining the terminal phase as a proof coordinate. markedTraceLaw then samples the one tick coin at that phase. The resulting Block contains only the finite zero outcomes and its tick outcome; its duration is the length of that very history.")),
                    Paragraph(Text("The support induction identifies both the trace length and terminal phase, and the marginal phase induction gives GeometricPhaseOccupation.finiteCappedLaw. Thus the potential pair is the duration and mark of these same coins, with no independence claim inside a pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("criticalrenewalfreshblocks-fresh-same-source"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalFreshBlocks.fresh_same_source"),
                H("Independent blocks on the same renewal source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any initial-wait mass function w, duration mass function f and immutable Tick J, sourceLaw is w times the infinite product of the freshly constructed block laws. The duration-mark pairs extracted from successive coordinates are mutually independent, and every one has exactly pairLaw f t. The complete pair sequence is independent of the initial wait. The pushforward retaining only the initial wait and all actual durations is exactly w times the infinite product of f. For every positive H and interior evidence e, the distribution of target(e+increment) from a sampled block equals the f-mixture of the literal k-zero/one-tick word laws.")),
                    Paragraph(Text("The numerical equilibrium wait law and the two polynomial-exponential duration laws may be inserted into w and f separately. The table remains unchanged between source labels. The construction does not assume or assert independence of a gap duration and its own terminal score.")),
                    Paragraph(Text("The pathwise execution uses the initial wait and this one block sequence in chronological order. The proof arrays, block indices, phase histories and clocks do not enlarge State H J."))),
                DescribeRole.Theorem))));
}
