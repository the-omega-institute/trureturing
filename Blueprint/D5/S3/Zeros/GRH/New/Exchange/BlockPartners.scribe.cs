using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class BlockPartnersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Block Partners", H("Block Partners"),
        Blocks(
            Paragraph(Text("Sections over cosets; matched pairs are GL-stable and determined by one side. Block determinant functions on the open cell are partners, by Jacobi's complementary minors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/BlockPartners.partner_block"),
                H("partner_block"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For any function f, the functions Φ(x₁ x₂) = χ⁻¹(det x₂)f(x₂⁻¹x₁) and Ψ(y₁; y₂) = χ⁻¹(det y₁)f(−y₂y₁⁻¹), with blocks cut by e and x₂, y₁ square, are partners for χ over R (IsPartner).")))))));
}
