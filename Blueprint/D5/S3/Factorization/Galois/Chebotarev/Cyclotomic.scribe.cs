using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois.Chebotarev;

internal sealed class CyclotomicDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclotomic.",
        H("Cyclotomic"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cyclotomic-density-from-two-sided-asymp"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Galois/Chebotarev/Cyclotomic.cyclotomic_density_from_two_sided_asymp"),
                H("Cyclotomic"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Sharifi 7.2.1 step (iv) — two-sided log-asymptotic comparison (p. 142). Source: \"on " +
                    "the one hand we have Σ_χ χ(σ)^{-1} log L(χ,s) ~ |G| Σ_{φ_𝔭=σ} N𝔭^{-s}, whereas on the " +
                    "other we have Σ_χ χ(σ)^{-1} log L(χ,s) ~ log ζ_K(s) ~ log(s-1)^{-1}\". Comparing " +
                    "yields density 1/|G|."))),
                DescribeRole.Theorem)
        )));
}
