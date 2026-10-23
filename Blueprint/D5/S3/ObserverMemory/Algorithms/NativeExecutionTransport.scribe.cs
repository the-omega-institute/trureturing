using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class NativeExecutionTransportDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native transport and halt endpoint uniqueness preserve literal execution.",
        H("Native Execution Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("instruction-transport"), Handle("transport"),
                H("Control equivalence and literal address mapping"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A control equivalence maps every successor. An arbitrary address map "
                    + "maps the literal installed at each read; distinct occurrences may share "
                    + "one physical literal. Replies retain their type and meaning."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("transported-program"), Handle("transportProgram"),
                H("The reindexed instruction table"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The table at a new control evaluates the original table at its inverse "
                    + "control, then maps that instruction. It adds no source or epoch port."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("run-transport"), Handle("run_transport_iff"),
                H("Exact native execution transport in both directions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under exact instruction compatibility and equality of observations "
                        + "at every epoch and mapped address, a native Run exists exactly when "
                        + "the reindexed Run exists. Both initial and terminal epochs are unchanged. "
                        + "The same original source observation is used at every read.")),
                    Paragraph(Text(
                        "The reverse direction inspects the original instruction at the inverse "
                        + "control and identifies its mapped successor. It needs no inverse, "
                        + "injectivity or surjectivity of the address map. No finite carrier or "
                        + "termination assumption is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("halt-endpoint-uniqueness"), Handle("run_halt_unique"),
                H("Halt-ended executions agree in control and epoch"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two native Runs from the same control and epoch on the same observation "
                        + "field have equal endpoint controls and epochs when both endpoint "
                        + "instructions are halt. Deterministic reads and updates force their "
                        + "successors to agree, and a halt has no outgoing edge.")),
                    Paragraph(Text(
                        "Arbitrary finite endpoints are not unique: the empty path and a longer "
                        + "prefix can coexist. This result provides the native operational "
                        + "prerequisite for whole-table synthesis; it constructs no synthesis "
                        + "algorithm and does not settle the uniform descriptor boundary theorem."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(Owner + name);
}
