using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class SchurTestDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schur Test", H("Schur Test"),
        Blocks(
            Paragraph(Text("Energy of terms of the second moment; splitting; passage to cut Bessel functions. Size function of a class of terms; open-cell mass fits under it.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/SchurTest.lintegral_boxCutoff_le_of_average"),
                H("lintegral_boxCutoff_le_of_average"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Averaging: let s map (X, m) measurably to 𝖴⁰_∞, B ⊆ X with m(B) ≥ 1, F ≥ 0 be measurable and left 𝖴⁰_c(g)-invariant, ∫_B F(u·s(x)·y)dm ≤ C for u ∈ 𝖴⁰_∞, y ∈ Filling.boxedPoints. Then ∫β⁰_c∏_v‖W_v‖²F ≤ C·ν·#Filling.BesselCoord, for W_v cut, β⁰ = Filling.boxCutoff.")))))));
}
