using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class PoincareSeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Poincare Series", H("Poincare Series"),
        Blocks(
            Paragraph(Text("Poincaré series from cut-off Bessel function: convergence, being a form, unfolding, inner products.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/PoincareSeries.petersson_poincare"),
                H("petersson_poincare"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Unfolding. Under Filling.IsAdmissible, for coordinate columns a = (c, i), a' = (c', i') and k in K₀ with reduction s, the Petersson product ⟨k𝒫a', 𝒫a⟩ is the volume of Filling.stdPrincipalLevel times entry (i, i') of the amplitude sum over all rational terms over (c, s, c').")))))));
}
