using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Components.Gates.Swap;

internal sealed class LabelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Components Gates Swap Label", H("Components Gates Swap Label"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapLabel"),
                H("qftSwapLabel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Basis-label action of the usual three-CNOT addressed SWAP."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapLabel_left"),
                H("qftSwapLabel left"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma qftSwapLabel_left {n : Nat} (left right : Fin n) (hne : left ≠ right) (label : Fin (2 ^ n)) : (qftSwapLabel left right label).val.testBit (WireAddress.bitIndex left).val = label.val.testBit (WireAddress.bitIndex right).val."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapLabel_right"),
                H("qftSwapLabel right"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma qftSwapLabel_right {n : Nat} (left right : Fin n) (hne : left ≠ right) (label : Fin (2 ^ n)) : (qftSwapLabel left right label).val.testBit (WireAddress.bitIndex right).val = label.val.testBit (WireAddress.bitIndex left).val."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration3"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapLabel_of_ne"),
                H("qftSwapLabel of ne"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma qftSwapLabel_of_ne {n : Nat} (left right bit : Fin n) (hne : left ≠ right) (hleft : bit ≠ left) (hright : bit ≠ right) (label : Fin (2 ^ n)) : (qftSwapLabel left right label).val.testBit (WireAddress.bitIndex bit).val = label.val.testBit (WireAddress.bitIndex bit).val."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration4"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapOperator_applyVec_ket"),
                H("qftSwapOperator applyVec ket"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("public lemma qftSwapOperator_applyVec_ket {n : Nat} (left right : Fin n) (hne : left ≠ right) (label : Fin (2 ^ n)) : (qftSwapOperator left right hne).applyVec (NormalizedVector.ket (R."))), DescribeRole.Lemma))));
}
