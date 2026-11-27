using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.LinearAlgebra;

internal sealed class ValuedMatrixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Valued Matrix", H("Valued Matrix"),
        Blocks(
            Paragraph(Text("Polynomials in matrices: adjoints, base change, invertibility, characteristic polynomial divisibility. Diagonalisation with simple roots; Sylvester's law of inertia. Valuation bounds for matrix products; GL_n(O) as integral entries with unit determinant.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ValuedMatrix.mem_intGL_iff_det"),
                H("mem_intGL_iff_det"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Over a field F with a valuation v into the value group ℤᵐ⁰, an invertible matrix g lies in GL_n(𝒪_F) if and only if all its entries have valuation at most 1 and v(det g) = 1.")))))));
}
