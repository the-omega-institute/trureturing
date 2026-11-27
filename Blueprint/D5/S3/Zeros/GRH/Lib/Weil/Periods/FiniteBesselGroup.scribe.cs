using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Periods;

internal sealed class FiniteBesselGroupDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Bessel Group", H("Finite Bessel Group"),
        Blocks(
            Paragraph(Text("Base point of the surviving orbit, shift character, generic Bessel/Fourier-Jacobi functions. Graded hermitian matrices, adjoints; Bessel subgroup is unipotent radical times definite unitary group. Rational coordinates of finite adelic points; finite parts of the Bessel subgroup.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Periods/FiniteBesselGroup.gram_xFin"),
                H("gram_xFin"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a hermitian space (J, x), the finite part x_f of x satisfies x_fᴴ J x_f = 1 over the finite adeles.")))))));
}
