using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois.Chebotarev;

internal sealed class FixedFieldFrobeniusCountingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "𝔓 is the unique prime of 𝓞 L above 𝔓 ∩ 𝓞 E.",
        H("𝔓 is the unique prime of 𝓞 L above 𝔓 ∩ 𝓞 E"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eq-of-lies-over-under-e-of-frobenius"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Galois/Chebotarev/FixedFieldFrobeniusCounting.eq_of_liesOver_under_E_of_frobenius"),
                H("𝔓 is the unique prime of 𝓞 L above 𝔓 ∩ 𝓞 E"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Let E = L^⟨σ⟩. If 𝔓 is a prime of L above an unramified prime of K, its arithmetic " +
                    "K-Frobenius is σ, and ord(σ) = |Gal(L/E)|, then 𝔓 is the unique prime of L above " +
                    "𝔓 ∩ 𝓞 E. The hypotheses make the stabilizer of 𝔓 in Gal(L/E) the whole group; " +
                    "transitivity on primes above 𝔓 ∩ 𝓞 E gives uniqueness."))),
                DescribeRole.Theorem)
        )));
}
