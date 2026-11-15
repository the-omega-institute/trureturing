using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Util.FinPow.BinaryBasis;

internal sealed class PairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Util FinPow BinaryBasis Pair", H("Util FinPow BinaryBasis Pair"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis/Pair.bigEndianEquiv_cons_value"),
                H("bigEndianEquiv cons value"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma bigEndianEquiv_cons_value (n : Nat) (head : Fin 2) (tail : Fin n → Fin 2) : (bigEndianEquiv (n + 1) (Fin.cons head tail)).val = (bigEndianEquiv n tail).val + 2 ^ n * head.val."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis/Pair.bigEndianEquiv_cons_pair"),
                H("bigEndianEquiv cons pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma bigEndianEquiv_cons_pair (n : Nat) (head : Fin 2) (tail : Fin n → Fin 2) : bigEndianEquiv (n + 1) (Fin.cons head tail) = qftPairEquiv n (head, bigEndianEquiv n tail)."))), DescribeRole.Lemma))));
}
