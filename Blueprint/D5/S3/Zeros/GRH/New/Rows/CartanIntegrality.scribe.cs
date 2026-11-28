using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class CartanIntegralityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cartan Integrality", H("Cartan Integrality"),
        Blocks(
            Paragraph(Text("Denominator lost by the Cartan product at the glued lattice.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/CartanIntegrality.weylGauge_cartanProduct_le"),
                H("weylGauge_cartanProduct_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let L be glued for s and M ≠ 0 an integer in the ideal of the chosen places. The p-adic gauge of y·η at (h₁, h₂)γ is at most |M|_p^(−loss) times the gauges of y at h₁ and of η̄ at h₂, the latter for the conjugate embedding.")))))));
}
