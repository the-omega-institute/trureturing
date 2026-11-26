using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Adeles;

internal sealed class FinitePlaceDensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Place Density", H("Finite Place Density"),
        Blocks(
            Paragraph(Text("Product of completions at finite set S: projection, section, measure, modulus, product formula. Finite place as one ring: volumes, content moments, cone mass bound, slab densities.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Adeles/FinitePlaceDensity.mass_near_quadric_off_places_le"),
                H("mass_near_quadric_off_places_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let sm = 1, β = β̄, ζ_Ô(μ) ≤ 2, 2μ+2 ≤ |κ|. Integrals of f(x_T) over x integral off T with m(x*x−β−a) ∈ Ô are v times the same integrals at T, for a finite v with vol(codifferent E s)·ν{Γ : mΓ/δ ∈ R}·v ≤ ζ_Ô(μ)vol(Ô)^|κ|.")))))));
}
