using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class IntegralAsCosetSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral As Coset Sum", H("Integral As Coset Sum"),
        Blocks(
            Paragraph(Text("Finite coset cut with multiplicities dividing powers of q; period as weighted finite sum.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/IntegralAsCosetSum.exists_integral_eq_sum_over_cut"),
                H("exists_integral_eq_sum_over_cut"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a level A and a on G_∞, one κ gives ∫_{B(E⁺)∖G} f = κ∑_{t∈T} b(t)/mult(t), B = Grading.besselGroup, for all integrable f = Py (Grading.IsGeneric P, y automorphic), levels J and finite (A ∩ B_f)-stable T ⊆ G_f/J, if mult ≠ 0 where f ≠ 0 and ∫_{[B]} f(ρt)dρ = [K₀:J]a(t_∞)b(t_f) for t_f ∈ T.")))))));
}
