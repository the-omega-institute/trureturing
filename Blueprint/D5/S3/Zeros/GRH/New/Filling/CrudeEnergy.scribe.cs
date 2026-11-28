using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class CrudeEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Crude Energy", H("Crude Energy"),
        Blocks(
            Paragraph(Text("Agreeing characters with vanishing discriminant force a level; disagreeing terms contribute zero. Energy of a stable set: incoherent and degenerate pairs of terms are negligible.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/CrudeEnergy.energy_le_of_linkEnergy_le"),
                H("energy_le_of_linkEnergy_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Crude estimate (letters as in Filling.energy_le_of_level_pairs): T stable, all s ∈ Ω fixing X ≥ 1; C ≥ 𝖽₁, ≥ τ²⁰𝖽₁ if a term has IsNormalForm 0, ≥ τ¹²𝖽/X^|κ| if R omits a link. If cut Filling.linkEnergy (𝗀 ≠ 0) ≤ wν², the full energy is ≤ (1+b⁻⁴)²w + b⁻¹²C.")))))));
}
