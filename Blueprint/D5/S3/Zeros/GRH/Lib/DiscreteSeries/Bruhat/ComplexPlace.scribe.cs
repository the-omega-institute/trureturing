using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Bruhat;

internal sealed class ComplexPlaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex Place", H("Complex Place"),
        Blocks(
            Paragraph(Text("The place C, boosts, cell densities, top floor carries Leray measure on hyperboloid.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Bruhat/ComplexPlace.map_orbitPoint_cellLaw_top"),
                H("map_orbitPoint_cellLaw_top"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Polar coordinates on the hyperboloid h(v, v) = −1 of V_ϱ, for k = |κ| > 1: σ ↦ σ⁻¹z carries the law of w_ϱ(c)⁻¹h, under cellDensity(c) dc and Haar probability on U(X₀), to the quadric measure δ^(ϱ).")))))));
}
