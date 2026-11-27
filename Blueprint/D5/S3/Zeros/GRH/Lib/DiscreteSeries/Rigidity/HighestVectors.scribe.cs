using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Rigidity;

internal sealed class HighestVectorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Highest Vectors", H("Highest Vectors"),
        Blocks(
            Paragraph(Text("Highest weight vectors exist; filtration steps are spanned by lowering words, finite-dimensional.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Rigidity/HighestVectors.filtration_le_of_word_mem"),
                H("filtration_le_of_word_mem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let l have distinct entries and x be K-highest. A subspace that is stable under the compact lowering operators and contains all words of length ≤ s in the E_ab applied to x contains M_s, where M_0 = U(𝔨)x, M_{s+1} = M_s + 𝔤M_s.")))))));
}
