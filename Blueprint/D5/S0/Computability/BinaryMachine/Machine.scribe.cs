using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class MachineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite binary tape machines.",
        H("Finite binary tape machines"),
        Blocks(
            Paragraph(Text("Each machine has finitely many states and reads a finite symbol alphabet. A run counts every local instruction. Two halting runs from the same configuration agree, including their Boolean decision and complete final tape. The output-size theorem bounds physical output by initial word length plus twice the executed instruction count.")),
            Describe.Lean(
                DescribeId.Create("supplied-machine"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/Machine.run_deterministic"),
                H("run_deterministic"),
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
        []));
}
