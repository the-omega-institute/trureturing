using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class WindowSuccessorGraphDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Successor Graphs of Finite Legal Digit Windows.",
        H("Successor Graphs of Finite Legal Digit Windows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("windowsuccessorgraph-window-successor-graph"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/WindowSuccessorGraph.window_successor_graph"),
                H("The exact window successor graph"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive window length L, Fibonacci values identify the observed "
                    + "successor graph with the increment cycle from zero through G_L minus one, "
                    + "together with the extra reset from G_(L-1) minus one to zero. That extra "
                    + "source is the unique vertex with two outgoing edges, and zero is the unique "
                    + "vertex with two incoming edges. Every edge occurs on natural digit rows. "
                    + "One extra input digit determines the successor window uniquely, while the "
                    + "original window cannot determine it even on natural rows. After h steps, "
                    + "h extra input digits suffice."))),
                DescribeRole.Theorem))));
}
