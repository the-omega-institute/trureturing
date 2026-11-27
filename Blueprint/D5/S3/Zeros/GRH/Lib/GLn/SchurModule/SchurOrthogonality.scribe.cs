using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GLn.SchurModule;

internal sealed class SchurOrthogonalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schur Orthogonality", H("Schur Orthogonality"),
        Blocks(
            Paragraph(Text("Maps between algebraic forms and scalar functions on the adelic group. Schur orthogonality on products of U(n); highest coefficient as product of principal minors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GLn/SchurModule/SchurOrthogonality.gramForm_highestVector_self"),
                H("gramForm_highestVector_self"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If each l_w is injective, the vector v⁺ = highestVector κ l is a unit vector for the Gram form of weight κ: ⟨v⁺, v⁺⟩ = 1.")))))));
}
