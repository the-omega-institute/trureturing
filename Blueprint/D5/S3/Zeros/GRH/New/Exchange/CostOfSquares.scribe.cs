using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class CostOfSquaresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cost Of Squares", H("Cost Of Squares"),
        Blocks(
            Paragraph(Text("Cost in squares bookkeeping; exchange constants on the data cost one square.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/CostOfSquares.exists_isTameFor_costsSquares_one"),
                H("exists_isTameFor_costsSquares_one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let (ν, z) be a pair ramified exactly at the chosen places, e ≥ 1, 1 ≤ n ≤ m. Each (νϑⁿ)⁻¹ is tame for the modulus 𝔪 = M^e Q(ϑ) (Data.𝔪), and every c with |c(ϑ)|² = C·Π(z) (lValueProd) costs one square (Data.CostsSquares).")))))));
}
