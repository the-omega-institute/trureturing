using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source;

internal sealed class LeadingEntriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Primitives QFT Source LeadingEntries", H("Primitives QFT Source LeadingEntries"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/LeadingEntries.leading_complement"),
                H("leading complement"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma leading_complement (n : Nat) (row column : (layout (n + 1)).Basis) : let application."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/LeadingEntries.qftSource_leading_matrix_entry"),
                H("qftSource leading matrix entry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The actual leading Hadamard has identity action on the full tail register."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/LeadingEntries.qftSource_leading_matrix_cons"),
                H("qftSource leading matrix cons"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Leading-bit coordinates expose Hadamard tensor identity, with no extra phase."))), DescribeRole.Lemma))));
}
