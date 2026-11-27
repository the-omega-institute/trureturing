using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Theta;

internal sealed class FischerDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fischer Decomposition", H("Fischer Decomposition"),
        Blocks(
            Paragraph(Text("Swap symmetry, vacuum weight, Laplacians and Fischer inner product for Howe's argument.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Theta/FischerDecomposition.fockLaplacian_eq_zero_of_isKHighest"),
                H("fockLaplacian_eq_zero_of_isKHighest"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let P be K-highest of weight ν for the oscillator action on rows, Q_ab = Σ ∂_{ac}∂_{bc}P over c with σε_aε'_c = +. If no nonzero Q_ab, ε_a ≠ ε_b, is K-highest of weight ν − e_a + e_b, all these Q_ab vanish.")))))));
}
