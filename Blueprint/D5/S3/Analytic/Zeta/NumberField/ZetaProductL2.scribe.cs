using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.NumberFieldZeta;

internal sealed class ZetaProductL2Document : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "unramified-supported Frobenius-fibre equidistribution.",
        H("unramified-supported Frobenius-fibre equidistribution"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-card-frobenius-ideal-fibre-sub-kappa-mul-le"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/ZetaProductL2.exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le"),
                H("unramified-supported Frobenius-fibre equidistribution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "unramified-supported Frobenius-fibre equidistribution. For L = K(μ_m) cyclotomic, the " +
                    "number of nonzero ideals 𝔞 with N𝔞 ≤ N, every prime factor of 𝔞 unramified in L (U 𝔞) " +
                    "and Frob_𝔞 = g is κ·N + O(N^{1−1/d}) with the leading constant κ independent of g (d " +
                    "= finrank ℚ K). U 𝔞 is the exact support condition (galoisCharacterOnIdeal χ 𝔞 ≠ 0)."))),
                DescribeRole.Theorem)
        )));
}
