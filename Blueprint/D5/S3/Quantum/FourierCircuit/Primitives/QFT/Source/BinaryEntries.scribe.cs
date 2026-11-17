using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source;

internal sealed class BinaryEntriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Primitives QFT Source BinaryEntries", H("Primitives QFT Source BinaryEntries"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries.binary_pair_decode"),
                H("binary pair decode"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma binary_pair_decode (n : Nat) (head : Fin 2) (tail : Fin (2 ^ n)) : (QuantumSignature.qubitsIndexEquiv (n + 1)).symm (qftPairEquiv n (head, tail)) = Fin.cons head ((QuantumSignature.qubitsIndexEquiv n).symm tail)."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries.qftSource_binaryMatrix_pair"),
                H("qftSource binaryMatrix pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma qftSource_binaryMatrix_pair {oracles : OracleModel} {n : Nat} (body : UnitaryCircuit FourierGate.model oracles (QFTPrimitive.layout (n + 1))) (rowHead columnHead : Fin 2) (rowTail columnTail : Fin (2 ^ n)) (environment : oracles.Interpretation) : onBinaryLabels body environment (qftPairEquiv n (rowHead, rowTail)) (qftPairEquiv n (columnHead, columnTail)) = (body.matrix environment) (Fin.cons rowHead ((QuantumSignature.qubitsIndexEquiv n).symm rowTail)) (Fin.cons columnHead ((QuantumSignature.qubitsIndexEquiv n).symm columnTail))."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries.qftSource_leading_binaryMatrix_pair"),
                H("qftSource leading binaryMatrix pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma qftSource_leading_binaryMatrix_pair (oracles : OracleModel) (n : Nat) (rowHead columnHead : Fin 2) (rowTail columnTail : Fin (2 ^ n)) (environment : oracles.Interpretation) : onBinaryLabels (leadingHadamard oracles n) environment (qftPairEquiv n (rowHead, rowTail)) (qftPairEquiv n (columnHead, columnTail)) = if rowTail = columnTail then Gate.HOp rowHead columnHead else 0."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration3"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries.qftSource_tail_binaryMatrix_pair"),
                H("qftSource tail binaryMatrix pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma qftSource_tail_binaryMatrix_pair (oracles : OracleModel) (n : Nat) (body : UnitaryCircuit FourierGate.model oracles (QFTPrimitive.layout n)) (rowHead columnHead : Fin 2) (rowTail columnTail : Fin (2 ^ n)) (environment : oracles.Interpretation) : onBinaryLabels (tailLayer oracles n body) environment (qftPairEquiv n (rowHead, rowTail)) (qftPairEquiv n (columnHead, columnTail)) = if rowHead = columnHead then onBinaryLabels body environment rowTail columnTail else 0."))), DescribeRole.Lemma))));
}
