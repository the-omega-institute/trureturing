using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class StackWordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Executed word operations.",
        H("Executed word operations"),
        Blocks(
            Paragraph(Text("Clear, transfer, scatter, copy and unary length are finite primitive programs. Copy restores the original source word and scratch while replacing the destination. Exact costs include all loop control and terminal instructions, and frame statements retain untouched registers.")),
            Describe.Lean(
                DescribeId.Create("supplied-stackwords"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackWords.exec_copy"),
                H("exec_copy"),
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
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackProgram"))]));
}
