using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Adeles;

internal sealed class MatrixApproxDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Matrix Approx", H("Matrix Approx"),
        Blocks(
            Paragraph(Text("Additive strong approximation omitting finite places; density at infinite places.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Adeles/MatrixApprox.denseRange_rat_matrix_add"),
                H("denseRange_rat_matrix_add"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Strong approximation for matrices: for a nonempty set S of finite places and x in GL_n(𝔸), the matrices x⁻¹A + B, with A rational and B adelic, supported on S, are dense in the n × m adelic matrices.")))))));
}
