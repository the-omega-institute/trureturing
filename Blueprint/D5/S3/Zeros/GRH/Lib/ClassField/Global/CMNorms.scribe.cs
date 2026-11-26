using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Global;

internal sealed class CMNormsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "CM Norms", H("CM Norms"),
        Blocks(
            Paragraph(Text("Class field theory of a CM extension: real ideles modulo norms, signs, splitting character.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Global/CMNorms.exists_eq_principalIdele_mul_norm"),
                H("exists_eq_principalIdele_mul_norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("L CM. A conjugation-invariant finite idele t is x z z̄, x ∈ L^×, with any signs of product 1 if t = 1. For real a ∈ L^×, a z z̄ = 1 forces ∏Φ_w(a) > 0. A splitting character is −1 on the uniformiser at every w = w̄.")))))));
}
