using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class LinePointPowersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Line Point Powers", H("Line Point Powers"),
        Blocks(
            Paragraph(Text("Mirror lemma: relations isotropic on a coset are few, killed by a scalar difference. One polynomial bounds twisted Selmer lengths everywhere, sharply at a chosen point. Points on the line through a root of unity are almost roots of unity.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/LinePointPowers.exists_sharp_fitting_poly"),
                H("exists_sharp_fitting_poly"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let ρ modulo ℓ^M and h: Gal(Ω/E) → (ℤ/q)^σ be continuous. For each tuple y₀ over O some polynomial F bounds the Selmer length of y^h·ρ modulo ℓ^M by v(F(y)) at every tuple y over every discrete valuation ring over O, with equality at y₀.")))))));
}
