using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source;

internal sealed class PhaseMatrixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Primitives QFT Source PhaseMatrix", H("Primitives QFT Source PhaseMatrix"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/PhaseMatrix.phaseStep_binaryMatrix"),
                H("phaseStep binaryMatrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma phaseStep_binaryMatrix (oracles : OracleModel) (n : Nat) (offset : Fin n) (environment : oracles.Interpretation) : onBinaryLabels (phaseStep oracles n offset) environment = qftControlledPhaseOperator 0 offset.succ (phaseAngle offset.val)."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/PhaseMatrix.phasePrefix_binaryMatrix"),
                H("phasePrefix binaryMatrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma phasePrefix_binaryMatrix (oracles : OracleModel) (n count : Nat) (bounded : count ≤ n) (environment : oracles.Interpretation) : (onBinaryLabels (phasePrefix oracles n count bounded) environment : HilbertOperator (Qubits (n + 1))) = Matrix.diagonal (qftPhaseLayerFactorPrefix n count bounded)."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/PhaseMatrix.qftSource_phase_binaryMatrix_entry"),
                H("qftSource phase binaryMatrix entry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The full native source phase layer has the original exact Fourier phase on every input label."))), DescribeRole.Lemma))));
}
