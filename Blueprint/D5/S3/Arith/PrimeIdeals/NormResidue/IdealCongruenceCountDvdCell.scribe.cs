using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimeIdeals.NormResidue;

internal sealed class IdealCongruenceCountDvdCellDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sublattice cell correspondence.",
        H("Sublattice cell correspondence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-card-fibre-dvd-eq-card-cell"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountDvdCell.exists_card_fibre_dvd_eq_card_cell"),
                H("Sublattice cell correspondence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a modulus coprime to the norm of the additional ideal, the points in a fixed " +
                    "norm and sign-orthant fibre of the product-ideal lattice have the same cardinality " +
                    "as a translated sublattice cell in the real embedding chart."))),
                DescribeRole.Theorem)
        )));
}
