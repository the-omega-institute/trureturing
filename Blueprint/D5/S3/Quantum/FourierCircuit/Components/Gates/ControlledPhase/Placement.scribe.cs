using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase;

internal sealed class PlacementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Components Gates ControlledPhase Placement", H("Components Gates ControlledPhase Placement"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Placement.phase_token_diagonal"),
                H("phase token diagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma phase_token_diagonal (angle : Real) : ((AlgorithmGate.model.operator (.singleQubit (phaseGateOp angle))).val : HilbertOperator (QuantumSignature.qubits 1).register) = Matrix.diagonal (fun basis => if QuantumSignature.qubitsIndexEquiv 1 basis = 0 then 1 else Complex.exp ((angle : Complex) * Complex.I))."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Placement.controlledPhase_single_phase_diagonal"),
                H("controlledPhase single phase diagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("Each actual phase occurrence acts on exactly the selected bit of the full two-qubit basis."))), DescribeRole.Lemma))));
}
