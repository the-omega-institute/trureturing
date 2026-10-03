using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois.Chebotarev;

internal sealed class FixedFieldDensityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Density-lift through the fixed-field subextension.",
        H("Density-lift through the fixed-field subextension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("density-lift-through-fixed-field"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Galois/Chebotarev/FixedFieldDensity.density_lift_through_fixedField"),
                H("Density-lift through the fixed-field subextension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Density-lift through the fixed-field subextension (Sharifi 7.2.2 Step 1, p. 143). Let " +
                    "σ ∈ Gal(L/K), E = L^⟨σ⟩ the fixed field of the cyclic subgroup ⟨σ⟩, and σ_E ∈ " +
                    "Gal(L/E) the corresponding element. Given the abelian-case density over E for the " +
                    "Frobenius-fibre of σ_E (value 1/|Gal(L/E)|), the density over K of the Frobenius " +
                    "class of σ is |C|/|G|."))),
                DescribeRole.Theorem)
        )));
}
