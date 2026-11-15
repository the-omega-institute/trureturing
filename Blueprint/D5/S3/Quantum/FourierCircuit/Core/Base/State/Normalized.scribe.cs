using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base.State;

internal sealed class NormalizedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base State Normalized", H("Core Base State Normalized"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.NormalizedVector"),
                H("NormalizedVector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("A unit vector over a finite register, with no preparation metadata."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration5"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ofVector"),
                H("ofVector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("Certify a raw vector once its norm-one proof is available."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration6"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ext"),
                H("ext"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma ext {ψ φ : NormalizedVector R} (hvec : ∀ i, ψ i = φ i) : ψ = φ."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration7"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ket"),
                H("ket"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("Computational-basis ket as a metadata-free normalized vector."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration8"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ket_apply"),
                H("ket apply"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("public lemma ket_apply (x i : R.Index) : ket x i = if i = x then 1 else 0."))), DescribeRole.Lemma))));
}
