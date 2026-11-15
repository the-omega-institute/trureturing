using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source;

internal sealed class TailEntriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Primitives QFT Source TailEntries", H("Primitives QFT Source TailEntries"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/TailEntries.tail_complement"),
                H("tail complement"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma tail_complement (n : Nat) (row column : (layout (n + 1)).Basis) : (layout (n + 1)).restrictComplementBasis (Finset.univ.map ⟨Fin.succ, Fin.succ_injective n⟩) row = (layout (n + 1)).restrictComplementBasis (Finset.univ.map ⟨Fin.succ, Fin.succ_injective n⟩) column ↔ row 0 = column 0."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/TailEntries.qftSource_tail_matrix_entry"),
                H("qftSource tail matrix entry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Placing the recursive word leaves precisely the leading coordinate untouched."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/TailEntries.qftSource_tail_matrix_cons"),
                H("qftSource tail matrix cons"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("In leading-bit and tail coordinates, the placed word is identity tensor its original matrix."))), DescribeRole.Lemma))));
}
