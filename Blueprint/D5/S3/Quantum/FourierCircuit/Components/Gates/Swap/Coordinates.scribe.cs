using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Components.Gates.Swap;

internal sealed class CoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Components Gates Swap Coordinates", H("Components Gates Swap Coordinates"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates.encoded_bit"),
                H("encoded bit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma encoded_bit {width : Nat} (basis : Fin width → Fin 2) (index : Fin width) : (QuantumSignature.qubitsIndexEquiv width basis).val.testBit (WireAddress.bitIndex index).val = finTwoEquiv (basis index)."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates.decoded_bit"),
                H("decoded bit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma decoded_bit {width : Nat} (label : Fin (2 ^ width)) (index : Fin width) : finTwoEquiv ((QuantumSignature.qubitsIndexEquiv width).symm label index) = label.val.testBit (WireAddress.bitIndex index).val."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates.qftSwapLabel_coordinates"),
                H("qftSwapLabel coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The unchanged integer-label action exchanges exactly the two physical coordinates."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration3"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates.qftSwapOperator_coordinates_entry"),
                H("qftSwapOperator coordinates entry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Every matrix entry of the original target is the same exact coordinate exchange."))), DescribeRole.Lemma))));
}
