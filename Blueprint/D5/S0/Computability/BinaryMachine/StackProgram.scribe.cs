using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class StackProgramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite program algebra and compilation.",
        H("Finite program algebra and compilation"),
        Blocks(
            Paragraph(Text("Typed finite control labels are represented by explicit finite encodings. Counted inductive execution compiles to the same number of primitive stack instructions. Sequential composition retains rejection, loops count their control operations, and label embeddings preserve the actual instruction trace.")),
            Describe.Lean(
                DescribeId.Create("supplied-stackprogram"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackProgram.compile_exec"),
                H("compile_exec"),
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
