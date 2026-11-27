using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GLn.SchurModule;

internal sealed class SchurMatrixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schur Matrix", H("Schur Matrix"),
        Blocks(
            Paragraph(Text("Universal basis, Schur matrices with functoriality and base change, Weyl character formula.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GLn/SchurModule/SchurMatrix.schur_apply_eq_prod"),
                H("schur_apply_eq_prod"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If the sizes fit κ (FitsRanks), the (i,j) entry of S_κ(z) is the product over places τ of the (i_τ, j_τ) entries of the one-place Schur matrices S_{κ_τ}(z_τ).")))))));
}
