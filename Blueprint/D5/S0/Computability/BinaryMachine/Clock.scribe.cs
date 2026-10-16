using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class ClockDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform numerical clocks and output bounds.",
        H("Uniform numerical clocks and output bounds"),
        Blocks(
            Paragraph(Text("Polynomial clocks use natural coefficients and exponents independent of the input. A transducer output has a polynomial length bound because an executed instruction changes finite tape size by a bounded amount. Pair lengths and verifier clocks are numerical consequences of actual executions.")),
            Describe.Lean(
                DescribeId.Create("supplied-clock"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/Clock.polyTime_output_length"),
                H("polyTime_output_length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text(
                    "This declaration and its proof are attributed immutable source supply. "
                    + "The mathematical namespace and proof body are preserved. Full license, "
                    + "source correspondence and the finite retirement contract are recorded "
                    + "in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies "
                    + "no new classification or independent mathematical escape content."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/Classes"))]));
}
