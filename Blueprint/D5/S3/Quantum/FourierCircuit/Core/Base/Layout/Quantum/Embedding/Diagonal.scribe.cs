using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding;

internal sealed class DiagonalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base Layout Quantum Embedding Diagonal", H("Core Base Layout Quantum Embedding Diagonal"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Diagonal.embedding_liftOperator_diagonal"),
                H("embedding liftOperator diagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("A diagonal operator stays diagonal under physical embedding, with its exact selected phase."))), DescribeRole.Lemma))));
}
