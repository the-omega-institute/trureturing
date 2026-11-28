using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class ThreeQueryPhaseProtocolDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/ThreeQueryPhaseProtocol.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/sieniawski2026adaptivechannel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict adaptive advantage in three independent queries to a qubit dephasing channel.",
        H("Three-query longitudinal dephasing discrimination"),
        Blocks(Describe.Lean(
            DescribeId.Create("adaptive-dephasing-advantage"),
            DeclarationHandle.Create(Module + "three_query_adaptive_advantage"),
            H("A common isometric control separates the two strategy classes"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(
                "The two hypotheses preserve the computational-basis populations and multiply "
                + "the upper coherence by 3/4 plus or minus 5i/16. A diagonal path Gram matrix "
                + "covers normalized pure parallel probes with arbitrary finite auxiliary memory. "
                + "A feasible dual matrix bounds their trace distance. A normalized input, "
                + "isometric control and Hermitian contraction realize a larger readout in "
                + "the adaptive protocol. The exact certificate gives a trace-distance gap "
                + "of at least 2281037/4096000000."))),
            DescribeRole.Theorem))));
}
