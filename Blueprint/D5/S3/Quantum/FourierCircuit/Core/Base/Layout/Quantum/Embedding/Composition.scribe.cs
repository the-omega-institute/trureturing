using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding;

internal sealed class CompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base Layout Quantum Embedding Composition", H("Core Base Layout Quantum Embedding Composition"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.compose"),
                H("compose"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Compose two inclusions of the same physical wires."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.embedding_ext"),
                H("embedding ext"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Embeddings are determined by their actual position maps."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.complement_eq_iff"),
                H("complement eq iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma complement_eq_iff (placement : QuantumLayout.Embedding source target) (row column : target.Basis) : (placement.splitBasis row).2 = (placement.splitBasis column).2 ↔ ∀ position, position ∉ placement.selection → row position = column position."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration3"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.selected_compose"),
                H("selected compose"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma selected_compose (inner : QuantumLayout.Embedding source intermediate) (outer : QuantumLayout.Embedding intermediate target) (basis : target.Basis) : ((compose inner outer).splitBasis basis).1 = (inner.splitBasis (outer.splitBasis basis).1).1."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration4"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.complement_compose"),
                H("complement compose"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma complement_compose (inner : QuantumLayout.Embedding source intermediate) (outer : QuantumLayout.Embedding intermediate target) (row column : target.Basis) : ((compose inner outer).splitBasis row).2 = ((compose inner outer).splitBasis column).2 ↔ (inner.splitBasis (outer.splitBasis row).1).2 = (inner.splitBasis (outer.splitBasis column).1).2 ∧ (outer.splitBasis row).2 = (outer.splitBasis column).2."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration5"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.embedding_lift_compose"),
                H("embedding lift compose"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Nested physical inclusions have exactly the same full operator as their composition."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration6"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.embedding_lift_mul"),
                H("embedding lift mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Physical extension preserves multiplication, including every spectator block."))), DescribeRole.Lemma))));
}
