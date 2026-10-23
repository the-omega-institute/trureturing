using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class StackSimulationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counted stack-to-tape simulation.",
        H("Counted stack-to-tape simulation"),
        Blocks(
            Paragraph(Text("The finite controller implements each stack instruction through physical tape macros. A room invariant bounds every live register by a shared capacity. Summing the per-instruction budgets gives a polynomial tape execution bound and preserves either halting decision.")),
            Describe.Lean(
                DescribeId.Create("supplied-stacksimulation"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackSimulation.controller_simulates"),
                H("controller_simulates"),
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
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackProgram")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackCompiler")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackPop")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackEncoding")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/TapeEquiv"))]));
}
