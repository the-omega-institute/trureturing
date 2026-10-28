using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class StackCompilerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical tape insertion and deletion.",
        H("Physical tape insertion and deletion"),
        Blocks(
            Paragraph(Text("Literal tape machines insert, shift and delete cells and rewind to a marked boundary. Their counted runs provide the physical operations used by the stack compiler; tape capacity is charged through actual scans rather than output length alone.")),
            Describe.Lean(
                DescribeId.Create("supplied-stackcompiler"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackCompiler.insert_run"),
                H("insert_run"),
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
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackMachine"))]));
}
