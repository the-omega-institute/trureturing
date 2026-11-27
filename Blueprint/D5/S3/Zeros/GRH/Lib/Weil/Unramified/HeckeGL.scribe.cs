using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Unramified;

internal sealed class HeckeGLDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hecke GL", H("Hecke GL"),
        Blocks(
            Paragraph(Text("Cosets of minuscule Hecke operators of GL_n indexed by residue subspaces; local congruence groups.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Unramified/HeckeGL.heckeGL_dual"),
                H("heckeGL_dual"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let ϖ be a uniformiser of E_w, n = i + j, and v fixed by GL_n(O_w). Acting on v by the indicator of the inverse of the double coset of T_i and then by the scalar matrix ϖ gives T_j v.")))))));
}
