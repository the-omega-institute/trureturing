using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimeIdeals.NormResidue;

internal sealed class IdealCongruenceCountDvdFibreDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Effective product-ideal residue fibre count.",
        H("Effective product-ideal residue fibre count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-card-fibre-dvd-residue-sub-mul-rpow-le"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountDvdFibre.exists_card_fibre_dvd_residue_sub_mul_rpow_le"),
                H("Effective product-ideal residue fibre count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each sign orthant and lattice coset, the product-ideal residue fibre count " +
                    "has a leading cell volume term divided by the norm of the additional ideal, " +
                    "with an error bounded by a constant times the dilation to degree d - 1. " +
                    "The leading term vanishes when the original cell does not carry the residue."))),
                DescribeRole.Theorem)
        )));
}
