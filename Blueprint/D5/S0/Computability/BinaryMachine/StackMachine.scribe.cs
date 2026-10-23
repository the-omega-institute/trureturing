using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class StackMachineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Boolean stack machines.",
        H("Finite Boolean stack machines"),
        Blocks(
            Paragraph(Text("Every instruction is a literal push, pop, peek, jump or halt on one of finitely many Boolean stacks. A register initially bounded by input length grows by at most one bit per instruction. This supplies an executed size bound for malformed decoder residuals.")),
            Describe.Lean(
                DescribeId.Create("supplied-stackmachine"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackMachine.runInput_length_le"),
                H("runInput_length_le"),
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
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/Machine"))]));
}
