using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Reverse;

internal sealed class MatrixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Primitives QFT Source Reverse Matrix", H("Primitives QFT Source Reverse Matrix"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix.swapStep_binaryMatrix"),
                H("swapStep binaryMatrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma swapStep_binaryMatrix (oracles : OracleModel) (n : Nat) (index : Fin (n / 2)) (environment : oracles.Interpretation) : onBinaryLabels (swapStep oracles n index) environment = qftSwapOperator (qftSwapLeft n index) (qftSwapRight n index) (qftSwapLeft_ne_right n index)."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix.reversePrefix_binary_apply_ket"),
                H("reversePrefix binary apply ket"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma reversePrefix_binary_apply_ket (oracles : OracleModel) (n count : Nat) (bounded : count ≤ n / 2) (label : Fin (2 ^ n)) (environment : oracles.Interpretation) : (onBinaryLabels (reversePrefix oracles n count bounded) environment).applyVec (NormalizedVector.ket (R."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix.qftSource_reverse_binary_apply_ket"),
                H("qftSource reverse binary apply ket"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma qftSource_reverse_binary_apply_ket (oracles : OracleModel) (n : Nat) (label : Fin (2 ^ n)) (environment : oracles.Interpretation) : (onBinaryLabels (bitReverse oracles n) environment).applyVec (NormalizedVector.ket (R."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration3"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix.qftSource_reverse_binaryMatrix"),
                H("qftSource reverse binaryMatrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma qftSource_reverse_binaryMatrix (oracles : OracleModel) (n : Nat) (environment : oracles.Interpretation) : onBinaryLabels (bitReverse oracles n) environment = UnitaryOperator.ofPerm (qftReverseBitsPerm n)."))), DescribeRole.Lemma))));
}
