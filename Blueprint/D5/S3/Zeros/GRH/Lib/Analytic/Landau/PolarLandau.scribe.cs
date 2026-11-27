using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Analytic.Landau;

internal sealed class PolarLandauDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polar Landau", H("Polar Landau"),
        Blocks(
            Paragraph(Text("Landau's lemma for one-sided bounds; Laplace transforms of powers; logarithmic derivatives of L-functions.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Analytic/Landau/PolarLandau.landau"),
                H("landau"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Landau's lemma. Let E satisfy IsPolar with residues r, and let β > 0. If re r(x) ≥ 0 for all real x > β and E(v) ≤ e^{(β−1)v} for large v, then r(ρ) = 0 whenever re ρ > β.")))))));
}
