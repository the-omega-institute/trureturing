using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum;

internal sealed class EmbeddingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base Layout Quantum Embedding", H("Core Base Layout Quantum Embedding"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.Embedding"),
                H("Embedding"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("An ordered subsystem consists of the same physical wires in a larger layout."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.selection"),
                H("selection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The ambient positions occupied by the ordered subsystem."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.positionEquiv"),
                H("positionEquiv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Source order identifies the selected ambient positions without changing their values."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration3"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.valueEquiv"),
                H("valueEquiv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Dimension equality casts a local value without permuting the computational basis."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration4"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.selectedBasisEquiv"),
                H("selectedBasisEquiv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The selected subsystem basis in source order; every coordinate map is a dimension cast."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration5"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.splitBasis"),
                H("splitBasis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Split an ambient basis into the ordered subsystem and every untouched wire."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration6"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.embedding_splitBasis_selected_value"),
                H("embedding splitBasis selected value"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Splitting reads precisely the original basis value at each selected physical wire."))), DescribeRole.Lemma))));
}
