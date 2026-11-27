using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Adeles;

internal sealed class LocalComponentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Components", H("Local Components"),
        Blocks(
            Paragraph(Text("Principal congruence subgroups form a neighbourhood basis of 1 in finite adelic GL_n. Local components of finite adelic unitary group; GL_n at split places; restricted product API.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Adeles/LocalComponents.range_atSplit"),
                H("range_atSplit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a split finite place w (w̄ ≠ w), the image of atSplit : GL_n(E_w) → G_f is the subgroup of elements with component 1 at every place other than w and w̄.")))))));
}
