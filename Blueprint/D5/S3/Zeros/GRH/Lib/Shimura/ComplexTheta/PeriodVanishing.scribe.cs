using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.ComplexTheta;

internal sealed class PeriodVanishingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Period Vanishing", H("Period Vanishing"),
        Blocks(
            Paragraph(Text("Vanishing theta descent to the split group forces zero period over the stabiliser.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/ComplexTheta/PeriodVanishing.period_eq_zero"),
                H("period_eq_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let Y on U(I_n), n = n₁ + n₂, be continuous, left invariant under rational points, fixed by the part of K₀ = Kf above T ∪ T̄, and satisfy DescentsVanish for ℍ^{n₁}, υ^{n₁}, T. Then the period ∫Y(h₁u)du over [U(I_{n₂})] vanishes for every h₁ in the first block.")))))));
}
