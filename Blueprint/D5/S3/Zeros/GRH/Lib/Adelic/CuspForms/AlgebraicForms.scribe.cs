using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.CuspForms;

internal sealed class AlgebraicFormsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Algebraic Forms", H("Algebraic Forms"),
        Blocks(
            Paragraph(Text("Forms on a definite unitary group are algebraic modular forms; integrals become class sums.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/AlgebraicForms.isSphericalWith_toAlgForm_iff"),
                H("isSphericalWith_toAlgForm_iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For V standard and l twice the Harish-Chandra parameter of (κ, e), a form y of type e_l is spherical at w with Hecke polynomial p if and only if its algebraic form, as a function on G_f, is.")))))));
}
