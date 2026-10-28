using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class TapeToStacksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tape execution inside finite stacks.",
        H("Tape execution inside finite stacks"),
        Blocks(
            Paragraph(Text("The tape model is encoded into three Boolean registers using a fixed two-bit symbol representation. The core simulation preserves both accepting and rejecting decisions. A separate normalized transducer extracts exactly the physical output on true halts and restores its two work registers.")),
            Describe.Lean(
                DescribeId.Create("supplied-tapetostacks"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/TapeToStacks.simulate_core"),
                H("simulate_core"),
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
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackSimulation")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackWords"))]));
}
