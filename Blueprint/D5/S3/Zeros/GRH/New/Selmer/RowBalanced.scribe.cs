using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class RowBalancedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Row Balanced", H("Row Balanced"),
        Blocks(
            Paragraph(Text("Roots of unity give a tame class; lattices in columns read above ℓ. Local duality bounds Ribet cocycles' distance from crystalline by the dual lattice's defect. Rows are balanced: local conditions and mirror scalar within explicit bound.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/RowBalanced.eventually_isBalanced"),
                H("eventually_isBalanced"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a row R of rank n, a chosen place w off ℓ and all large O, some lattice u is balanced (IsBalanced) for Z_f above ℓ, and β plus v(det(u(σ) − 1)) for σ = σ_w, σ_w^{−c} (σ_w a tame generator at w) has normalised length ≤ 10fn·cr_ℓ.")))))));
}
