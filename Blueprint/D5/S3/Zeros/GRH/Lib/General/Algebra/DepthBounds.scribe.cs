using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class DepthBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Depth Bounds", H("Depth Bounds"),
        Blocks(
            Paragraph(Text("Coefficients of substituted p-adic series; bounds by products over columns; lowest terms.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/DepthBounds.coeff_subst_linearSeries"),
                H("coeff_subst_linearSeries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For g ∈ ℂ_p[[t]] and a linear form ∑ c_x z_x in finitely many variables, the coefficient of z^D in g(∑ c_x z_x) is (∏ c_x^{D_x}) · |D|! · g_{|D|} / ∏ D_x!, with |D| the total degree and g_n the n-th coefficient of g.")))))));
}
