using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.GoodReduction;

internal sealed class ArcReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arc Reduction", H("Arc Reduction"),
        Blocks(
            Paragraph(Text("Theta tori over good places have multiplicative sup norm; degree and level are units.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/GoodReduction/ArcReduction.hasGoodReduction_and_val_card_eq_one"),
                H("hasGoodReduction_and_val_card_eq_one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Good reduction of a theta torus x: if Φ_{v₀} maps O_E into the valuation ring of v, over a prime good for D, then the v-adic sup norm on torsion points is multiplicative (HasGoodReduction), and r and |T| are v-units.")))))));
}
