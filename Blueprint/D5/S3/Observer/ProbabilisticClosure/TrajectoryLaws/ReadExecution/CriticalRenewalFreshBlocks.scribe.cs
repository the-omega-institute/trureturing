using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution;

internal sealed class CriticalRenewalFreshBlocksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One wait and one sequence of complete duration-mark blocks.",
        H("Critical renewal independent source blocks"),
        Blocks(
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
