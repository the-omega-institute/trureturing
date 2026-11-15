using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Primitives.QFT.Mathematics;

internal sealed class BitReverseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Primitives QFT Mathematics BitReverse", H("Primitives QFT Mathematics BitReverse"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftSwapLeft"),
                H("qftSwapLeft"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Left wire of the indexth symmetric bit-reversal swap."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftSwapRight"),
                H("qftSwapRight"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Right wire of the indexth symmetric bit-reversal swap."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftSwapLeft_ne_right"),
                H("qftSwapLeft ne right"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma qftSwapLeft_ne_right (n : Nat) (index : Fin (n / 2)) : qftSwapLeft n index ≠ qftSwapRight n index."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration3"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftBitReverseLabelPrefix"),
                H("qftBitReverseLabelPrefix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Basis-label action of the first count symmetric swaps."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration4"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftBitReverseLabelPrefix_invariant"),
                H("qftBitReverseLabelPrefix invariant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("After the first count symmetric swaps, the outer count wires on each side contain their reversed source bits and every middle wire is unchanged."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration5"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftBitReverseLabel_eq"),
                H("qftBitReverseLabel eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The complete symmetric SWAP network realizes the canonical bit-reversal permutation on computational-basis labels."))), DescribeRole.Lemma))));
}
