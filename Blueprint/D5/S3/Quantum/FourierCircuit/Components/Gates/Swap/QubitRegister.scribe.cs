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
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("The original ordered register of physical qubits."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.selected_pair"),
                H("selected pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma selected_pair (basis : Fin width → Fin 2) : UnitaryCircuit.selectedInput layout (qubitLayout width) (positions left right distinct) (dimensions (qubitLayout width) left right distinct rfl rfl) basis = ![basis left, basis right]."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.matching_coordinates"),
                H("matching coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma matching_coordinates (row column : Fin width → Fin 2) : (fun index => row (Equiv.swap left right index)) = column ↔ ![row right, row left] = ![column left, column right] ∧ (qubitLayout width).restrictComplementBasis (Finset.univ.map (positions left right distinct)) row = (qubitLayout width).restrictComplementBasis (Finset.univ.map (positions left right distinct)) column."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration3"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.qubitCircuit"),
                H("qubitCircuit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("Execute all three CNOTs on the selected positions of the original register."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration4"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.swap_qubitCircuit_matrix"),
                H("swap qubitCircuit matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("The full native word realizes the unchanged addressed SWAP, including exact phase."))), DescribeRole.Lemma))));
}
