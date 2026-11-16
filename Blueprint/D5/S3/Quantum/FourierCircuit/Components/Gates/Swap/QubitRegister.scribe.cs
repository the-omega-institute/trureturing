using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Components.Gates.Swap;

internal sealed class QubitRegisterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Components Gates Swap QubitRegister", H("Components Gates Swap QubitRegister"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.qubitLayout"),
                H("qubitLayout"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The original ordered register of physical qubits."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.swap_qubitOperator_matrix"),
                H("swap qubitOperator matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The placed SWAP has the unchanged addressed target, including exact phase."))), DescribeRole.Lemma))));
}
