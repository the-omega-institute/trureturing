using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimeIdeals.NormResidue;

internal sealed class IdealCongruenceCountTransferDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sublattice cell count.",
        H("Sublattice cell count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("card-norm-le-residue"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer.cardNormLeResidue"),
                H("Norm-residue count, abbreviation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Norm-residue count, abbreviation. cardNormLeResidue K c a N is the number of nonzero " +
                    "integral ideals of 𝓞 K of norm ≤ N whose norm is ≡ a (mod c). The leading constant of " +
                    "its effective estimate (exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le) is, by " +
                    "the normalized-error limit of cardNormLeResidue K c a N / N."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("card-norm-le-residue-class"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer.cardNormLeResidueClass"),
                H("Per-class norm-residue count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Per-class norm-residue count. The number of nonzero integral ideals of 𝓞 K of norm ≤ " +
                    "N, norm residue y (mod c), and ideal class C."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("card-norm-le-residue-class-dvd"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer.cardNormLeResidueClassDvd"),
                H("𝔟-divisible per-class norm-residue count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "𝔟-divisible per-class norm-residue count. The number of nonzero integral ideals of 𝓞 " +
                    "K divisible by 𝔟, of norm ≤ N, norm residue y (mod c), and ideal class D."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exists-mk0-eq-abs-norm-coprime"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer.exists_mk0_eq_absNorm_coprime"),
                H("Coprime ideal-class representative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Every ideal class of a number field has a nonzero integral representative whose " +
                    "absolute norm is coprime to a prescribed positive integer."))),
                DescribeRole.Theorem)
        )));
}
