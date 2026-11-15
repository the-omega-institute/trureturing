using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base.State;

internal sealed class NormalizedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base State Normalized", H("Core Base State Normalized"), Blocks(
            Describe.Lean(DescribeId.Create("instance-instcoehilbertvector"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.instCoeHilbertVector"),
                H("instCoeHilbertVector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("For every register R, a NormalizedVector R coerces to its underlying HilbertVector R through the vec field."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("instance-instcoetailhilbertvector"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.instCoeTailHilbertVector"),
                H("instCoeTailHilbertVector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("For every register R, the tail coercion from NormalizedVector R to HilbertVector R is the vec field."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("instance-instcoeouthilbertvector"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.instCoeOutHilbertVector"),
                H("instCoeOutHilbertVector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("For every register R, the output coercion from NormalizedVector R to HilbertVector R is the vec field."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("instance-instcoefunforallindexcomplex"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.instCoeFunForallIndexComplex"),
                H("instCoeFunForallIndexComplex"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("For every register R and normalized vector psi, function coercion evaluates psi.vec at an index of R. This supplies the notation used by ext and ket_apply."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.NormalizedVector"),
                H("NormalizedVector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("A unit vector over a finite register, with no preparation metadata."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration5"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ofVector"),
                H("ofVector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Certify a raw vector once its norm-one proof is available."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration6"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ext"),
                H("ext"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma ext {ψ φ : NormalizedVector R} (hvec : ∀ i, ψ i = φ i) : ψ = φ."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration7"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ket"),
                H("ket"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Computational-basis ket as a metadata-free normalized vector."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration8"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ket_apply"),
                H("ket apply"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("public lemma ket_apply (x i : R.Index) : ket x i = if i = x then 1 else 0."))), DescribeRole.Lemma))));
}
