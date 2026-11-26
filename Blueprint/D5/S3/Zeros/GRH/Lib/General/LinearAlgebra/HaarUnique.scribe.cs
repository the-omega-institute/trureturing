using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.LinearAlgebra;

internal sealed class HaarUniqueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Haar Unique", H("Haar Unique"),
        Blocks(
            Paragraph(Text("Complex Gaussian integral for matrices of positive real part; linear change of variables. Determinant is monotone in the semidefinite order; matrix Bessel inequality for contractions. Reindexing, currying and flipping product measures preserve measure. Haar measures giving one function integral one are equal.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/HaarUnique.addHaar_eq_of_integral_eq_one"),
                H("addHaar_eq_of_integral_eq_one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Two Haar measures μ, ν on a second countable locally compact additive group are equal if some real function f has integral 1 for both.")))))));
}
