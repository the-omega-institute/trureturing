using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source;

internal sealed class NoSwapMatrixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Primitives QFT Source NoSwapMatrix", H("Primitives QFT Source NoSwapMatrix"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/NoSwapMatrix.hadamard_entry"),
                H("hadamard entry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma hadamard_entry (output input : Fin 2) : Gate.HOp output input = invSqrt2 * (if output = 1 ∧ input = 1 then -1 else 1)."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/NoSwapMatrix.qftSource_noSwap_binaryMatrix_entry"),
                H("qftSource noSwap binaryMatrix entry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Closed matrix formula for the actual recursive no-swap circuit. Its row label is bit-reversed because the final symmetric SWAP network has not yet been applied."))), DescribeRole.Lemma))));
}
