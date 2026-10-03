using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois.Chebotarev;

internal sealed class AbelianDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chebotarev's theorem, abelian case.",
        H("Chebotarev's theorem, abelian case"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("chebotarev-abelian"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Galois/Chebotarev/Abelian.chebotarev_abelian"),
                H("Chebotarev's theorem, abelian case"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Chebotarev's theorem, abelian case (Sharifi 7.2.2 Step 2). For an abelian Galois " +
                    "extension L/K of number fields and any σ ∈ Gal(L/K), the Dirichlet density of primes " +
                    "𝔭 of 𝓞 K unramified in L whose Frobenius equals σ is 1 / |Gal(L/K)|. Composition: the " +
                    "|G| fibres S_σ each have liminf ≥ 1/|G| (liminf_ratio_ge_inv_card_G) and their " +
                    "density ratios sum to 1 (ratioSum_frobeniusFibres_tendsto_one); the pigeonhole glue " +
                    "tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one forces each to the limit 1/|G|."))),
                DescribeRole.Theorem)
        )));
}
