using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.LocalGlobal;

internal sealed class LocalTranslatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Translates", H("Local Translates"),
        Blocks(
            Paragraph(Text("Forms spherical off S; simultaneous diagonalisation of Hecke operators; levels off finite sets. Local component of a form: smooth, admissible, translates keep the Hecke eigensystem.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/LocalTranslates.hasHeckePolyAt_iff_localFormRep"),
                H("hasHeckePolyAt_iff_localFormRep"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("At a split place w, a form x has Hecke polynomial P if and only if, in the local representation of GL_n(E_w) on forms, GL_n(O_w) fixes x, the j-th Hecke operator scales x by t_j, and P = Σ (−1)^j q_w^{j(j−1)/2} t_j X^{n−j}.")))))));
}
