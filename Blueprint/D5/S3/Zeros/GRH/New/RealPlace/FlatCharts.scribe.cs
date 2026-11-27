using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class FlatChartsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Flat Charts", H("Flat Charts"),
        Blocks(
            Paragraph(Text("Gauge estimates: flat charts, fibre masses, nearness, supports and weights on floors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/FlatCharts.hasMatSize_sub_one_of_floorValues"),
                H("hasMatSize_sub_one_of_floorValues"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let p, q be heads of length j for a gauge S, with c/g of Γ-size 1 for c of S-size 10(ϱ+1) if j ≠ 0. If ux, vy lie in the box (u, v ∈ 𝖴), (vy−ux)/g has Γ-size 2, w_p⁻¹x, w_q⁻¹y are near at j, and each 𝔤_a(x,y), a > j, holds a unit with inverse of Γ-size 1, then (x⁻¹y−1)/g has Γ-size 99(ϱ+1).")))))));
}
