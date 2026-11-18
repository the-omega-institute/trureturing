using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source;

internal sealed class RecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Primitives QFT Source Recurrence", H("Primitives QFT Source Recurrence"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Recurrence.phase_binaryMatrix_pair"),
                H("phase binaryMatrix pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma phase_binaryMatrix_pair (oracles : OracleModel) (n : Nat) (outputHead inputHead : Fin 2) (outputTail inputTail : Fin (2 ^ n)) (environment : oracles.Interpretation) : onBinaryLabels (phaseLayer oracles n) environment (qftPairEquiv n (outputHead, outputTail)) (qftPairEquiv n (inputHead, inputTail)) = if outputHead = inputHead ∧ outputTail = inputTail then (if inputHead = 1 then ω (n + 1) ^ inputTail.val else 1) else 0."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Recurrence.phaseAfterLeading_binaryMatrix_pair"),
                H("phaseAfterLeading binaryMatrix pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma phaseAfterLeading_binaryMatrix_pair (oracles : OracleModel) (n : Nat) (outputHead inputHead : Fin 2) (outputTail inputTail : Fin (2 ^ n)) (environment : oracles.Interpretation) : ((onBinaryLabels (phaseLayer oracles n) environment : HilbertOperator (Qubits (n + 1))) * (onBinaryLabels (leadingHadamard oracles n) environment : HilbertOperator (Qubits (n + 1)))) (qftPairEquiv n (outputHead, outputTail)) (qftPairEquiv n (inputHead, inputTail)) = (if outputHead = 1 then ω (n + 1) ^ outputTail.val else 1) * Gate.HOp outputHead inputHead * (if outputTail = inputTail then 1 else 0)."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Recurrence.qftSource_noSwap_succ_binaryMatrix_pair"),
                H("qftSource noSwap succ binaryMatrix pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma qftSource_noSwap_succ_binaryMatrix_pair (oracles : OracleModel) (n : Nat) (outputHead inputHead : Fin 2) (outputTail inputTail : Fin (2 ^ n)) (environment : oracles.Interpretation) : onBinaryLabels (noSwap oracles (n + 1)) environment (qftPairEquiv n (outputHead, outputTail)) (qftPairEquiv n (inputHead, inputTail)) = onBinaryLabels (noSwap oracles n) environment outputTail inputTail * (if outputHead = 1 then ω (n + 1) ^ inputTail.val else 1) * Gate.HOp outputHead inputHead."))), DescribeRole.Lemma))));
}
