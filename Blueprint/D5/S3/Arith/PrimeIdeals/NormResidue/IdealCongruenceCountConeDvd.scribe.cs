using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimeIdeals.NormResidue;

internal sealed class IdealCongruenceCountConeDvdDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The J- and 𝔟J-cone residue counts share a leading constant up to N(𝔟).",
        H("The J- and 𝔟J-cone residue counts share a leading constant up to N(𝔟)"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-card-ideal-set-residue-real-le-dvd"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountConeDvd.exists_card_idealSet_residue_real_le_dvd"),
                H("The J- and 𝔟J-cone residue counts share a leading constant up to N(𝔟)"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The J- and 𝔟J-cone residue counts share a leading constant up to N(𝔟). For gcd(N(𝔟), " +
                    "m) = 1, there is a common κ = ∑_cells L_J with both the J-cone count ≈ κ·S and the " +
                    "𝔟J-cone count ≈ (κ/N(𝔟))·S (same O(S^{1-1/d}) rate). The two per-cell estimates " +
                    "(exists_card_residue_fibre_sub_mul_rpow_le_explicit, " +
                    "exists_card_fibre_dvd_residue_sub_mul_rpow_le) carry the explicit per-cell constants " +
                    "L_J(p) and L_J(p)/N(𝔟); summing over the (orthant, coset) partition at tN = S^{1/d} " +
                    "gives the result."))),
                DescribeRole.Theorem)
        )));
}
